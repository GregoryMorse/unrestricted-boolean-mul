#!/usr/bin/env python3
"""Replace a monolithic Boolean-ring cancellation by additive normalization.

The generated return-history certificate first proves every multiplier times
constraint identity separately.  Its last step is then only an equality of
explicit sums of already squarefree monomials.  Asking ``ring_nf`` to revisit
that equality is needlessly expensive: multiplication is no longer involved.

This post-processor validates the final XOR identity in Python, expands the
named product definitions in Lean, and lets ``abel_nf`` collect identical
monomials as additive atoms.  The remaining even integer coefficients vanish
by characteristic two.  Large products that were split into checked part
definitions are expanded at this additive stage as well.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from split_large_boolean_product import (
    Polynomial,
    definition_body,
    parse_polynomial,
)


def xor_into(target: Polynomial, source: Polynomial) -> None:
    target.symmetric_difference_update(source)


def numbered_part(path: Path) -> int:
    match = re.search(r"Part(\d+)$", path.stem)
    if match is None:
        raise ValueError(f"could not recover a part number from {path}")
    return int(match.group(1))


def product_polynomial(
    product_module: Path,
    stem: str,
    index: int,
) -> tuple[Polynomial, list[str]]:
    text = product_module.read_text(encoding="utf-8")
    product_name = f"{stem}Product_{index}"
    _, expression = definition_body(text, product_name)
    part_references = [
        int(value)
        for value in re.findall(
            rf"{re.escape(product_name)}_part_(\d+) v", expression
        )
    ]
    if not part_references:
        return parse_polynomial(expression), []

    imported_parts = re.findall(
        rf"(?m)^import UnrestrictedBooleanMul\.N5\."
        rf"([A-Za-z0-9_]*Product{index}Part\d+)$",
        text,
    )
    part_paths = sorted(
        (product_module.parent / f"{name}.lean" for name in imported_parts),
        key=numbered_part,
    )
    if [numbered_part(path) for path in part_paths] != part_references:
        raise ValueError(f"part references for product {index} are incomplete")
    result: Polynomial = set()
    names: list[str] = []
    for part_index, part_path in zip(part_references, part_paths, strict=True):
        name = f"{product_name}_part_{part_index}"
        part_text = part_path.read_text(encoding="utf-8")
        _, part_expression = definition_body(part_text, name)
        xor_into(result, parse_polynomial(part_expression))
        names.append(name)
    return result, names


def format_simp_names(names: list[str]) -> str:
    return "  simp only [\n" + "".join(f"    {name},\n" for name in names) + "  ]\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("base", type=Path)
    parser.add_argument("--stem", required=True)
    args = parser.parse_args()

    source = args.source.resolve()
    base = args.base.resolve()
    text = source.read_text(encoding="utf-8")
    base_text = base.read_text(encoding="utf-8")
    indices = sorted({
        int(value)
        for value in re.findall(
            rf"{re.escape(args.stem)}Multiplier_(\d+) v \*", text
        )
    })
    if indices != list(range(len(indices))):
        raise ValueError("the aggregate combination is not consecutively indexed")

    _, target_expression = definition_body(base_text, f"{args.stem}Target")
    target = parse_polynomial(target_expression)
    combined: Polynomial = set()
    names = [f"{args.stem}Target"]
    product_modules = {
        int(match.group(1)): path
        for path in source.parent.glob(f"{source.stem}Products*.lean")
        if (match := re.fullmatch(rf"{re.escape(source.stem)}Products(\d+)", path.stem))
    }
    part_names: list[str] = []
    for index in indices:
        product_module = product_modules.get(index // 5)
        if product_module is None:
            raise ValueError(f"could not locate the module for product {index}")
        assembly_module = product_module.with_name(
            f"{product_module.stem}Product{index}Assembly.lean"
        )
        if assembly_module.exists():
            product_module = assembly_module
        polynomial, local_part_names = product_polynomial(
            product_module, args.stem, index
        )
        xor_into(combined, polynomial)
        names.append(f"{args.stem}Product_{index}")
        part_names.extend(local_part_names)
    if combined != target:
        missing = len(target - combined)
        extra = len(combined - target)
        missing_sample = sorted(target - combined, key=lambda value: (len(value), value))[:5]
        extra_sample = sorted(combined - target, key=lambda value: (len(value), value))[:5]
        raise ValueError(
            f"product XOR does not equal the target: missing={missing}, extra={extra}, "
            f"missing_sample={missing_sample}, extra_sample={extra_sample}"
        )
    names.extend(part_names)

    certificate_at = text.index(f"private theorem {args.stem}_certificate")
    rw_at = text.index("\n  rw [", certificate_at)
    proof_at = text.index("\n", rw_at + 1) + 1
    next_theorem_at = text.index("\n\nset_option maxRecDepth", proof_at)
    replacement = (
        format_simp_names(names)
        + "  abel_nf\n"
        + "  simp [CharTwo.ofNat_eq_mod]\n"
    )
    text = text[:proof_at] + replacement + text[next_theorem_at:]
    source.write_text(text, encoding="utf-8", newline="\n")

    print(f"products={len(indices)}")
    print(f"split_product_parts={len(part_names)}")
    print(f"target_terms={len(target)}")
    print(f"validated={source}")


if __name__ == "__main__":
    main()
