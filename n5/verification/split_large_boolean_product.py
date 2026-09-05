#!/usr/bin/env python3
"""Split one large generated Boolean-product proof into bounded Lean leaves.

The raw return-history certificates are identities in the Boolean polynomial
ring over ``F₂``.  A single multiplier can occasionally be large enough that
normalizing its product in one Lean process exhausts a CI worker.  This tool
partitions that multiplier, computes the squarefree product of every part,
and replaces the original proof by a sum of independently checkable leaves.

It is intentionally a post-processing step for files emitted by
``split_raw_history_certificate.py``.  The resulting theorem has exactly the
same statement; only its proof and the definition of the selected multiplier
are factored.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


Monomial = tuple[int, ...]
Polynomial = set[Monomial]


def module_name(path: Path) -> str:
    parts = path.with_suffix("").parts
    start = parts.index("UnrestrictedBooleanMul")
    return ".".join(parts[start:])


def definition_body(text: str, name: str) -> tuple[tuple[int, int], str]:
    pattern = re.compile(
        rf"(?ms)^def {re.escape(name)} \(v : Fin \d+ → F₂\) : F₂ :=\n"
        rf"  (.*?)(?=\n\n/--|\n\ndef |\n\nset_option |\n\nend$)"
    )
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"definition {name} was not found")
    return match.span(1), match.group(1).replace("\n  ", " ")


def parse_polynomial(expression: str) -> Polynomial:
    result: Polynomial = set()
    for raw_term in expression.strip().split(" + "):
        term = raw_term.strip()
        if term == "0" or not term:
            continue
        if term == "1":
            monomial: Monomial = ()
        else:
            residue = re.sub(r"v \d+(?: \^ \d+)?", "", term)
            residue = residue.replace("*", "").replace("(", "").replace(")", "")
            if residue.strip():
                raise ValueError(
                    f"unsupported syntax in Boolean monomial {term!r}: "
                    f"residue={residue.strip()!r}"
                )
            factors = tuple(int(value) for value in re.findall(r"v (\d+)", term))
            if not factors:
                raise ValueError(f"unrecognized monomial: {term!r}")
            monomial = tuple(sorted(set(factors)))
        if monomial in result:
            result.remove(monomial)
        else:
            result.add(monomial)
    return result


def multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    result: Polynomial = set()
    for first in left:
        for second in right:
            monomial = tuple(sorted(set(first) | set(second)))
            if monomial in result:
                result.remove(monomial)
            else:
                result.add(monomial)
    return result


def format_polynomial(polynomial: Polynomial) -> str:
    if not polynomial:
        return "0"
    terms: list[str] = []
    for monomial in sorted(polynomial, key=lambda value: (len(value), value)):
        if not monomial:
            terms.append("1")
        else:
            terms.append(" * ".join(f"v {index}" for index in monomial))
    return " + ".join(terms)


def constraint_expressions(text: str, stem: str) -> list[str]:
    start = text.index(f"def {stem}Constraint")
    end = text.index(f"\ntheorem {stem}_f2_mul_self", start)
    block = text[start:end]
    return re.findall(r"(?m)^    -- [^\n]+\n    (.*?)(?:,)?$", block)


def part_module(
    base_module: str,
    stem: str,
    coordinates: int,
    product_index: int,
    part_index: int,
    multiplier: Polynomial,
    product: Polynomial,
) -> str:
    multiplier_name = f"{stem}Multiplier_{product_index}_part_{part_index}"
    product_name = f"{stem}Product_{product_index}_part_{part_index}"
    theorem_name = f"{stem}_product_{product_index}_part_{part_index}"
    return f"""import {base_module}

namespace UnrestrictedBooleanMul.N5
noncomputable section
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192

def {multiplier_name} (v : Fin {coordinates} → F₂) : F₂ :=
  {format_polynomial(multiplier)}

def {product_name} (v : Fin {coordinates} → F₂) : F₂ :=
  {format_polynomial(product)}

set_option maxHeartbeats 3000000 in
theorem {theorem_name} (v : Fin {coordinates} → F₂) :
    {multiplier_name} v * {stem}Constraint v {product_index} =
      {product_name} v := by
  simp [{multiplier_name}, {stem}Constraint, {product_name}, add_mul, mul_add]
  all_goals ring_nf
  all_goals simp only [pow_two, {stem}_f2_mul_self]
  all_goals (try rw [{stem}_f2_two_eq_zero])
  all_goals (try simp only [mul_zero, add_zero, zero_add])
  all_goals ring_nf
  all_goals simp [{stem}_f2_two_eq_zero, CharTwo.ofNat_eq_mod]

end
end UnrestrictedBooleanMul.N5
"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("base", type=Path)
    parser.add_argument("--stem", required=True)
    parser.add_argument("--product-index", required=True, type=int)
    parser.add_argument("--part-size", type=int, default=64)
    parser.add_argument(
        "--alias-product", action="store_true",
        help=(
            "define the selected auxiliary product as the sum of its checked "
            "part products instead of flattening that sum again"
        ),
    )
    args = parser.parse_args()
    if args.part_size <= 0:
        parser.error("--part-size must be positive")

    source = args.source.resolve()
    base = args.base.resolve()
    text = source.read_text(encoding="utf-8")
    base_text = base.read_text(encoding="utf-8")
    coordinate_match = re.search(r"Fin (\d+) → F₂", text)
    if coordinate_match is None:
        raise ValueError("could not recover the coordinate count")
    coordinates = int(coordinate_match.group(1))

    multiplier_name = f"{args.stem}Multiplier_{args.product_index}"
    product_name = f"{args.stem}Product_{args.product_index}"
    multiplier_span, multiplier_expression = definition_body(text, multiplier_name)
    product_span, product_expression = definition_body(text, product_name)
    existing_part_pattern = (
        f"{source.stem}Product{args.product_index}Part*.lean"
    )
    existing_part_paths = sorted(source.parent.glob(existing_part_pattern))
    if f"{multiplier_name}_part_" in multiplier_expression:
        multiplier = set()
        for part_path in existing_part_paths:
            part_text = part_path.read_text(encoding="utf-8")
            part_match = re.search(
                rf"(?ms)^def {re.escape(multiplier_name)}_part_\d+ "
                rf"\(v : Fin \d+ → F₂\) : F₂ :=\n  "
                rf"(.*?)(?=\n\ndef )",
                part_text,
            )
            if part_match is None:
                raise ValueError(f"could not recover multiplier part from {part_path}")
            multiplier.symmetric_difference_update(
                parse_polynomial(part_match.group(1).replace("\n  ", " "))
            )
    else:
        multiplier = parse_polynomial(multiplier_expression)
    if f"{product_name}_part_" in product_expression:
        expected_product = set()
        for part_path in existing_part_paths:
            part_text = part_path.read_text(encoding="utf-8")
            part_match = re.search(
                rf"(?ms)^def {re.escape(product_name)}_part_\d+ "
                rf"\(v : Fin \d+ → F₂\) : F₂ :=\n  "
                rf"(.*?)(?=\n\nset_option )",
                part_text,
            )
            if part_match is None:
                raise ValueError(f"could not recover product part from {part_path}")
            expected_product.symmetric_difference_update(
                parse_polynomial(part_match.group(1).replace("\n  ", " "))
            )
    else:
        expected_product = parse_polynomial(product_expression)
    constraints = constraint_expressions(base_text, args.stem)
    if args.product_index >= len(constraints):
        raise ValueError("product index is outside the constraint vector")
    constraint = parse_polynomial(constraints[args.product_index])
    actual_product = multiply(multiplier, constraint)
    if actual_product != expected_product:
        raise ValueError("stored product is not the Boolean multiplier product")

    ordered_multiplier = sorted(multiplier, key=lambda value: (len(value), value))
    parts = [
        set(ordered_multiplier[first:first + args.part_size])
        for first in range(0, len(ordered_multiplier), args.part_size)
    ]
    part_products = [multiply(part, constraint) for part in parts]
    combined: Polynomial = set()
    for product in part_products:
        combined.symmetric_difference_update(product)
    if combined != expected_product:
        raise AssertionError("partitioned products do not reconstruct the stored product")

    part_paths: list[Path] = []
    for part_index, (part, product) in enumerate(zip(parts, part_products, strict=True)):
        part_path = source.with_name(
            f"{source.stem}Product{args.product_index}Part{part_index}.lean"
        )
        part_path.write_text(
            part_module(
                module_name(base), args.stem, coordinates, args.product_index,
                part_index, part, product,
            ),
            encoding="utf-8",
            newline="\n",
        )
        part_paths.append(part_path)

    replacement = " +\n  ".join(
        f"{args.stem}Multiplier_{args.product_index}_part_{index} v"
        for index in range(len(parts))
    )
    product_replacement = " +\n  ".join(
        f"{args.stem}Product_{args.product_index}_part_{index} v"
        for index in range(len(parts))
    )
    if args.alias_product:
        text = (
            text[:product_span[0]] + product_replacement + text[product_span[1]:]
        )
    text = text[:multiplier_span[0]] + replacement + text[multiplier_span[1]:]

    theorem_pattern = re.compile(
        rf"(?ms)^set_option maxHeartbeats \d+ in\n"
        rf"theorem {re.escape(args.stem)}_product_{args.product_index} .*?"
        rf"(?=\nset_option maxHeartbeats|\nend\nend UnrestrictedBooleanMul\.N5)"
    )
    theorem_match = theorem_pattern.search(text)
    if theorem_match is None:
        raise ValueError("selected product theorem was not found")
    part_theorems = ", ".join(
        f"{args.stem}_product_{args.product_index}_part_{index}"
        for index in range(len(parts))
    )
    part_product_names = ", ".join(
        f"{args.stem}Product_{args.product_index}_part_{index}"
        for index in range(len(parts))
    )
    if args.alias_product:
        multiplier_parts = [
            f"{args.stem}Multiplier_{args.product_index}_part_{index} v"
            for index in range(len(parts))
        ]
        product_parts = [
            f"{args.stem}Product_{args.product_index}_part_{index} v"
            for index in range(len(parts))
        ]
        proof_lines = [
            f"  have hpart_{index} := "
            f"{args.stem}_product_{args.product_index}_part_{index} v"
            for index in range(len(parts))
        ]
        proof_lines.extend([
            "  have hsum_0 :",
            f"      {multiplier_parts[0]} * "
            f"{args.stem}Constraint v {args.product_index} =",
            f"        {product_parts[0]} := hpart_0",
        ])
        for index in range(1, len(parts)):
            left = " + ".join(multiplier_parts[:index + 1])
            right = " + ".join(product_parts[:index + 1])
            proof_lines.extend([
                f"  have hsum_{index} :",
                f"      ({left}) * "
                f"{args.stem}Constraint v {args.product_index} =",
                f"        {right} := by",
                f"    rw [add_mul, hsum_{index - 1}, hpart_{index}]",
            ])
        proof_lines.extend([
            f"  unfold {multiplier_name} {product_name}",
            f"  exact hsum_{len(parts) - 1}",
        ])
        proof = "\n".join(proof_lines) + "\n"
    else:
        proof = f"""  simp only [{multiplier_name}, add_mul]
  rw [{part_theorems}]
  simp [{product_name}, {part_product_names}] <;>
    ring_nf <;>
    simp [{args.stem}_f2_two_eq_zero]
"""
    theorem = f"""set_option maxHeartbeats 3000000 in
theorem {args.stem}_product_{args.product_index} (v : Fin {coordinates} → F₂) :
    {multiplier_name} v * {args.stem}Constraint v {args.product_index} =
      {product_name} v := by
{proof}
"""
    text = text[:theorem_match.start()] + theorem + text[theorem_match.end():]

    old_import = re.compile(
        rf"(?m)^import UnrestrictedBooleanMul\.N5\."
        rf"{re.escape(source.stem)}Product{args.product_index}Part\d+\n"
    )
    text = old_import.sub("", text)
    imports = "".join(f"import {module_name(path)}\n" for path in part_paths)
    first_import_end = text.index("\n", text.index("import ")) + 1
    text = text[:first_import_end] + imports + text[first_import_end:]
    source.write_text(text, encoding="utf-8", newline="\n")

    print(f"multiplier_terms={len(multiplier)}")
    print(f"constraint_terms={len(constraint)}")
    print(f"product_terms={len(expected_product)}")
    for path, part, product in zip(part_paths, parts, part_products, strict=True):
        print(f"part={path} multiplier_terms={len(part)} product_terms={len(product)}")
    print(f"source={source}")


if __name__ == "__main__":
    main()
