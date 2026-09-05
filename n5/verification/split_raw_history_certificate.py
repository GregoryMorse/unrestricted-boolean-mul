#!/usr/bin/env python3
"""Split a generated return-history certificate into parallel Lean modules.

The aggregate generator deliberately emits a single self-contained file.  A
large certificate can nevertheless contain dozens of independent multiplier
identities, and elaborating those serially leaves most build cores idle.  This
script preserves the generated definitions and final theorem verbatim while
moving the independent identities into bounded chunks.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


PRODUCT_START = re.compile(
    r"(?m)^set_option maxHeartbeats (?:1000000|10000000) in\n"
    r"private theorem ([A-Za-z0-9_]+)_product_(\d+)"
)
CERTIFICATE_START = "set_option maxHeartbeats 3000000 in\n"
HELPER_START = "private theorem f2_mul_self"


def module_name(path: Path) -> str:
    parts = path.with_suffix("").parts
    try:
        start = parts.index("UnrestrictedBooleanMul")
    except ValueError as error:
        raise ValueError(
            "the Lean path must be below an UnrestrictedBooleanMul directory"
        ) from error
    return ".".join(parts[start:])


def namespace_footer() -> str:
    return "\nend\nend UnrestrictedBooleanMul.N5\n"


def namespace_header(import_name: str) -> str:
    return (
        f"import {import_name}\n\n"
        "namespace UnrestrictedBooleanMul.N5\n"
        "noncomputable section\n"
        "set_option linter.unreachableTactic false\n"
        "set_option linter.unusedTactic false\n"
        "set_option linter.unusedSimpArgs false\n"
        "set_option linter.unnecessarySeqFocus false\n"
        "set_option maxRecDepth 8192\n\n"
    )


def write(path: Path, value: str) -> None:
    path.write_text(value, encoding="utf-8", newline="\n")


def refine_existing_split(source: Path, text: str) -> None:
    """Move a legacy split's expanded product vector into its proof chunks."""
    stem_match = re.search(r"private theorem ([A-Za-z0-9_]+)_certificate", text)
    if stem_match is None:
        raise ValueError("no aggregate or already-split certificate found")
    stem = stem_match.group(1)
    base_path = source.with_name(source.stem + "Base.lean")
    base_text = base_path.read_text(encoding="utf-8")
    coordinate_match = re.search(
        rf"def {stem}Target \(v : Fin (\d+) → F₂\)", base_text
    )
    if coordinate_match is None:
        raise ValueError("could not recover the certificate coordinate count")
    coordinate_count = int(coordinate_match.group(1))
    chunk_modules = re.findall(
        r"(?m)^import (UnrestrictedBooleanMul\.[A-Za-z0-9_.]+Products\d+)$",
        text,
    )
    if (f"def {stem}Multiplier" in base_text and
            f"def {stem}Product" not in base_text):
        multiplier_start = base_text.index(f"def {stem}Multiplier")
        combination_start = base_text.index(
            f"def {stem}Combination", multiplier_start
        )
        helper_start = base_text.index(f"theorem {stem}_f2_mul_self")
        multiplier_source = base_text[multiplier_start:combination_start]
        multiplier_expressions = re.findall(
            r"(?m)^    -- [^\n]*\n    (.*?)(?:,)?$", multiplier_source
        )
        write(base_path, base_text[:multiplier_start] + base_text[helper_start:])
        seen: list[int] = []
        for chunk_module in chunk_modules:
            chunk_path = source.parent / (chunk_module.rsplit(".", 1)[1] + ".lean")
            chunk_text = chunk_path.read_text(encoding="utf-8")
            theorem_matches = list(re.finditer(
                rf"(?m)^set_option maxHeartbeats (?:1000000|10000000) in\n"
                rf"theorem {stem}_product_(\d+)", chunk_text
            ))
            indices = [int(match.group(1)) for match in theorem_matches]
            seen.extend(indices)
            multiplier_definitions = "".join(
                f"def {stem}Multiplier_{index} "
                f"(v : Fin {coordinate_count} → F₂) : F₂ :=\n"
                f"  {multiplier_expressions[index]}\n\n"
                for index in indices
            )
            rebuilt = chunk_text[:theorem_matches[0].start()]
            insertion = rebuilt.index("set_option maxRecDepth 8192\n")
            insertion = rebuilt.index("\n", insertion) + 1
            rebuilt = rebuilt[:insertion] + "\n" + multiplier_definitions + rebuilt[insertion:]
            for position, theorem_match in enumerate(theorem_matches):
                end = (
                    theorem_matches[position + 1].start()
                    if position + 1 < len(theorem_matches)
                    else chunk_text.index("\nend\nend UnrestrictedBooleanMul.N5")
                )
                index = int(theorem_match.group(1))
                block = chunk_text[theorem_match.start():end]
                block = block.replace(
                    f"{stem}Multiplier v {index}",
                    f"{stem}Multiplier_{index} v",
                ).replace(
                    f"{stem}Multiplier, {stem}Constraint",
                    f"{stem}Multiplier_{index}, {stem}Constraint",
                )
                rebuilt += block
            rebuilt += namespace_footer()
            write(chunk_path, rebuilt)
        if sorted(seen) != list(range(len(multiplier_expressions))):
            raise ValueError("split chunks do not cover the multiplier vector")
        combination = (
            f"private def {stem}Combination "
            f"(v : Fin {coordinate_count} → F₂) : F₂ :=\n"
            + "\n".join(
                f"  {stem}Multiplier_{index} v * {stem}Constraint v {index}"
                + (" +" if index + 1 < len(multiplier_expressions) else "")
                for index in range(len(multiplier_expressions))
            )
            + "\n\n"
        )
        certificate_at = text.index(CERTIFICATE_START)
        write(source, text[:certificate_at] + combination + text[certificate_at:])
        print(f"distributed={source}")
        return
    if f"def {stem}Product" not in base_text:
        for chunk_module in chunk_modules:
            chunk_path = source.parent / (chunk_module.rsplit(".", 1)[1] + ".lean")
            chunk_text = chunk_path.read_text(encoding="utf-8")
            theorem_matches = list(re.finditer(
                rf"(?m)^set_option maxHeartbeats (?:1000000|10000000) in\n"
                rf"theorem {stem}_product_(\d+)", chunk_text
            ))
            rebuilt = chunk_text[:theorem_matches[0].start()]
            for position, theorem_match in enumerate(theorem_matches):
                end = (
                    theorem_matches[position + 1].start()
                    if position + 1 < len(theorem_matches)
                    else chunk_text.index("\nend\nend UnrestrictedBooleanMul.N5")
                )
                index = int(theorem_match.group(1))
                block = chunk_text[theorem_match.start():end]
                block = re.sub(
                    rf"{stem}Product_\d+, add_mul",
                    f"{stem}Product_{index}, add_mul",
                    block,
                )
                rebuilt += block
            rebuilt += namespace_footer()
            write(chunk_path, rebuilt)
        print(f"repaired={source}")
        return
    product_start = base_text.index(f"def {stem}Product")
    combination_start = base_text.index(f"def {stem}Combination", product_start)
    product_source = base_text[product_start:combination_start]
    product_expressions = re.findall(
        r"(?m)^    -- [^\n]*\n    (.*?)(?:,)?$", product_source
    )
    if not product_expressions:
        raise ValueError("expanded product vector is empty")
    write(base_path, base_text[:product_start] + base_text[combination_start:])

    seen: list[int] = []
    for chunk_module in chunk_modules:
        chunk_path = source.parent / (chunk_module.rsplit(".", 1)[1] + ".lean")
        chunk_text = chunk_path.read_text(encoding="utf-8")
        indices = [
            int(value)
            for value in re.findall(rf"theorem {stem}_product_(\d+)", chunk_text)
        ]
        seen.extend(indices)
        definitions = "".join(
            f"def {stem}Product_{index} "
            f"(v : Fin {coordinate_count} → F₂) : F₂ :=\n"
            f"  {product_expressions[index]}\n\n"
            for index in indices
        )
        insertion = chunk_text.index("set_option maxRecDepth 8192\n")
        insertion = chunk_text.index("\n", insertion) + 1
        chunk_text = chunk_text[:insertion] + "\n" + definitions + chunk_text[insertion:]
        for index in indices:
            chunk_text = chunk_text.replace(
                f"{stem}Product v {index}", f"{stem}Product_{index} v"
            ).replace(
                f"{stem}Product, add_mul", f"{stem}Product_{index}, add_mul"
            )
        write(chunk_path, chunk_text)
    if sorted(seen) != list(range(len(product_expressions))):
        raise ValueError("split chunks do not cover the expanded product vector")

    product_names = ", ".join(
        f"{stem}Product_{index}" for index in range(len(product_expressions))
    )
    text = text.replace(
        f"[{stem}Target, {stem}Product]", f"[{stem}Target, {product_names}]"
    )
    write(source, text)
    print(f"refined={source}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--chunk-size", type=int, default=5)
    args = parser.parse_args()
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")

    source = args.source.resolve()
    text = source.read_text(encoding="utf-8")
    if HELPER_START not in text:
        refine_existing_split(source, text)
        return
    helper_at = text.index(HELPER_START)
    certificate_at = text.index(CERTIFICATE_START)
    matches = list(PRODUCT_START.finditer(text, helper_at, certificate_at))
    if not matches:
        raise ValueError("no generated product lemmas found")

    stem = matches[0].group(1)
    coordinate_match = re.search(
        rf"def {stem}Target \(v : Fin (\d+) → F₂\)", text
    )
    if coordinate_match is None:
        raise ValueError("could not recover the certificate coordinate count")
    coordinate_count = int(coordinate_match.group(1))
    expected = list(range(len(matches)))
    actual = [int(match.group(2)) for match in matches]
    if actual != expected or any(match.group(1) != stem for match in matches):
        raise ValueError("product lemmas are not one consecutive certificate")

    base_path = source.with_name(source.stem + "Base.lean")
    base_module = module_name(base_path)
    definitions = text[:helper_at]
    helpers = text[helper_at : matches[0].start()]
    multiplier_start = definitions.index(f"private def {stem}Multiplier")
    product_start = definitions.index(f"private def {stem}Product")
    combination_start = definitions.index(
        f"private def {stem}Combination", product_start
    )
    product_source = definitions[product_start:combination_start]
    multiplier_source = definitions[multiplier_start:product_start]
    multiplier_expressions = re.findall(
        r"(?m)^    -- [^\n]*\n    (.*?)(?:,)?$", multiplier_source
    )
    product_expressions = re.findall(
        r"(?m)^    -- [^\n]*\n    (.*?)(?:,)?$", product_source
    )
    if (len(multiplier_expressions) != len(matches) or
            len(product_expressions) != len(matches)):
        raise ValueError(
            f"expected {len(matches)} multipliers/products, found "
            f"{len(multiplier_expressions)}/{len(product_expressions)}"
        )
    definitions = definitions[:multiplier_start]
    definitions = definitions.replace(
        "set_option maxRecDepth 8192\n",
        "set_option maxRecDepth 8192\nset_option maxHeartbeats 3000000\n",
        1,
    )
    helpers = helpers.replace(
        "private theorem f2_mul_self", f"theorem {stem}_f2_mul_self"
    ).replace(
        "private theorem f2_two_eq_zero", f"theorem {stem}_f2_two_eq_zero"
    )
    write(base_path, definitions + helpers + namespace_footer())

    lemma_blocks: list[str] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else certificate_at
        block = text[match.start() : end]
        block = block.replace(
            "set_option maxHeartbeats 1000000 in",
            "set_option maxHeartbeats 10000000 in",
            1,
        )
        block = block.replace(
            f"private theorem {stem}_product_", f"theorem {stem}_product_"
        ).replace("f2_mul_self", f"{stem}_f2_mul_self").replace(
            "f2_two_eq_zero", f"{stem}_f2_two_eq_zero"
        )
        block = block.replace(
            f"{stem}Product v {index}", f"{stem}Product_{index} v"
        ).replace(
            f"{stem}Multiplier v {index}", f"{stem}Multiplier_{index} v"
        ).replace(
            f"{stem}Product, add_mul", f"{stem}Product_{index}, add_mul"
        ).replace(
            f"{stem}Multiplier, {stem}Constraint",
            f"{stem}Multiplier_{index}, {stem}Constraint",
        )
        lemma_blocks.append(block)

    chunk_paths: list[Path] = []
    for chunk_index, first in enumerate(range(0, len(lemma_blocks), args.chunk_size)):
        chunk_path = source.with_name(source.stem + f"Products{chunk_index}.lean")
        chunk_paths.append(chunk_path)
        last = min(first + args.chunk_size, len(lemma_blocks))
        local_definitions = "".join(
            f"def {stem}Multiplier_{index} "
            f"(v : Fin {coordinate_count} → F₂) : F₂ :=\n"
            f"  {multiplier_expressions[index]}\n\n"
            f"def {stem}Product_{index} "
            f"(v : Fin {coordinate_count} → F₂) : F₂ :=\n"
            f"  {product_expressions[index]}\n\n"
            for index in range(first, last)
        )
        body = local_definitions + "".join(lemma_blocks[first:last])
        write(chunk_path, namespace_header(base_module) + body + namespace_footer())

    final_body = text[certificate_at :]
    final_body = final_body.rsplit("\nend\nend UnrestrictedBooleanMul.N5", 1)[0]
    product_names = ", ".join(
        f"{stem}Product_{index}" for index in range(len(product_expressions))
    )
    final_body = final_body.replace(
        f"[{stem}Target, {stem}Product]", f"[{stem}Target, {product_names}]"
    )
    combination = (
        f"private def {stem}Combination "
        f"(v : Fin {coordinate_count} → F₂) : F₂ :=\n"
        + "\n".join(
            f"  {stem}Multiplier_{index} v * {stem}Constraint v {index}"
            + (" +" if index + 1 < len(multiplier_expressions) else "")
            for index in range(len(multiplier_expressions))
        )
        + "\n\n"
    )
    imports = "".join(f"import {module_name(path)}\n" for path in chunk_paths)
    main_text = (
        imports
        + "\nnamespace UnrestrictedBooleanMul.N5\n"
        + "noncomputable section\n"
        + "set_option linter.unreachableTactic false\n"
        + "set_option linter.unusedTactic false\n"
        + "set_option linter.unusedSimpArgs false\n"
        + "set_option linter.unnecessarySeqFocus false\n"
        + "set_option maxRecDepth 8192\n\n"
        + combination
        + final_body
        + namespace_footer()
    )
    write(source, main_text)

    print(f"base={base_path}")
    for path in chunk_paths:
        print(f"chunk={path}")
    print(f"main={source}")


if __name__ == "__main__":
    main()
