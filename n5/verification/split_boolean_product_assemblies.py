#!/usr/bin/env python3
"""Move selected split-product assembly theorems into independent modules.

``split_large_boolean_product.py`` creates many small checked multiplication
leaves and leaves their linear assembly in the original product chunk.  When
several unusually large products share that chunk, elaborating all assembly
proof terms in one Lean process retains too much state.  This post-processor
moves each chosen pair of public definitions and its theorem to a separate
module while preserving the exported names and theorem statements.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from split_large_boolean_product import module_name


def take_block(text: str, pattern: re.Pattern[str], description: str) -> tuple[str, str]:
    match = pattern.search(text)
    if match is None:
        raise ValueError(f"could not find {description}")
    block = match.group(0).rstrip() + "\n\n"
    return text[:match.start()] + text[match.end():], block


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("base", type=Path)
    parser.add_argument("--stem", required=True)
    parser.add_argument("--product-index", required=True, type=int)
    args = parser.parse_args()

    source = args.source.resolve()
    base = args.base.resolve()
    text = source.read_text(encoding="utf-8")
    index = args.product_index
    assembly_path = source.with_name(f"{source.stem}Product{index}Assembly.lean")
    assembly_module = module_name(assembly_path)

    part_import_pattern = re.compile(
        rf"(?m)^import (UnrestrictedBooleanMul\.N5\."
        rf"{re.escape(source.stem)}Product{index}Part\d+)\n"
    )
    part_imports = part_import_pattern.findall(text)
    text = part_import_pattern.sub("", text)

    blocks: list[str] = []
    for kind in ("Multiplier", "Product"):
        name = f"{args.stem}{kind}_{index}"
        pattern = re.compile(
            rf"(?ms)^def {re.escape(name)} \(v : Fin \d+ → F₂\) : F₂ :=\n"
            rf"  .*?(?=\n\ndef |\n\nset_option )\n*"
        )
        text, block = take_block(text, pattern, f"definition {name}")
        blocks.append(block)

    theorem_name = f"{args.stem}_product_{index}"
    theorem_pattern = re.compile(
        rf"(?ms)^set_option maxHeartbeats \d+ in\n"
        rf"theorem {re.escape(theorem_name)} .*?"
        rf"(?=\nset_option maxHeartbeats|\nend\nend UnrestrictedBooleanMul\.N5)\n*"
    )
    text, theorem = take_block(text, theorem_pattern, f"theorem {theorem_name}")
    blocks.append(theorem)

    import_line = f"import {assembly_module}\n"
    first_import_end = text.index("\n", text.index("import ")) + 1
    text = text[:first_import_end] + import_line + text[first_import_end:]
    source.write_text(text, encoding="utf-8", newline="\n")

    imports = f"import {module_name(base)}\n" + "".join(
        f"import {part}\n" for part in part_imports
    )
    assembly = (
        imports
        + "\nnamespace UnrestrictedBooleanMul.N5\n"
        + "noncomputable section\n"
        + "set_option linter.unreachableTactic false\n"
        + "set_option linter.unusedTactic false\n"
        + "set_option linter.unusedSimpArgs false\n"
        + "set_option linter.unnecessarySeqFocus false\n"
        + "set_option maxRecDepth 8192\n\n"
        + "".join(blocks)
        + "end\nend UnrestrictedBooleanMul.N5\n"
    )
    assembly_path.write_text(assembly, encoding="utf-8", newline="\n")
    print(f"parts={len(part_imports)}")
    print(f"assembly={assembly_path}")
    print(f"source={source}")


if __name__ == "__main__":
    main()
