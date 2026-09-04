#!/usr/bin/env python3
"""Emit the four reduced aligned return-history certificates.

The stored multiplier tables were discovered with Singular, but this script
reconstructs the reduced generators and independently checks every identity
with the repository's squarefree Boolean-polynomial engine before emitting
Lean.  The generated Lean modules then replay the identities algebraically.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXPLORATION = Path(__file__).resolve().parent / "exploration"
sys.path.insert(0, str(EXPLORATION))

from quadratic_return_history_polynomial import (  # noqa: E402
    EQUAL_FACTOR_EXCEPTIONAL_LIFT_MULTIPLIERS,
    EXCEPTIONAL_LIFT_MULTIPLIERS,
    ONE,
    ZERO,
    affine_eliminate_with_certificate,
    equations,
    lean_polynomial,
    padd,
    parse_singular_squarefree,
    pmul,
    pvar,
    r0,
)


LEAN_DIR = ROOT / "UnrestrictedBooleanMul" / "N5"


@dataclass(frozen=True)
class ExceptionalLeaf:
    camel: str
    theorem: str
    equal_factor: bool
    correction_return: int


LEAVES = (
    ExceptionalLeaf(
        "ZeroOneAlignedCorrectionZero",
        "zeroOne_aligned_correctionZero_reduced_inconsistent",
        False,
        0,
    ),
    ExceptionalLeaf(
        "ZeroOneAlignedCorrectionOne",
        "zeroOne_aligned_correctionOne_reduced_inconsistent",
        False,
        1,
    ),
    ExceptionalLeaf(
        "OneOneAlignedCorrectionZero",
        "oneOne_aligned_correctionZero_reduced_inconsistent",
        True,
        0,
    ),
    ExceptionalLeaf(
        "OneOneAlignedCorrectionOne",
        "oneOne_aligned_correctionOne_reduced_inconsistent",
        True,
        1,
    ),
)


ZERO_ONE_FIXED = {
    "ell1": 0,
    "ell2": 0,
    "ell4": 0,
    "ell6": 1,
    "ell7": 0,
    "y1": 1,
    "y2": 0,
    "y4": 0,
    "y6": 0,
    "y7": 0,
}

ONE_ONE_FIXED = {
    "m1": 0,
    "m2": 0,
    "m4": 0,
    "m6": 1,
    "m7": 0,
    "x1": 1,
    "x2": 0,
    "x4": 0,
    "x6": 0,
    "x7": 0,
}


def reduced_certificate(leaf: ExceptionalLeaf):
    q = r0 if leaf.equal_factor else 0
    constraints, target, names = equations(
        q,
        r0,
        r0,
        equal_factor_difference_coordinates=leaf.equal_factor,
    )
    fixed_values = ONE_ONE_FIXED if leaf.equal_factor else ZERO_ONE_FIXED
    assignments = {
        **fixed_values,
        "correctionReturn0": leaf.correction_return,
    }
    for name, value in assignments.items():
        index = names.index(name)
        constraints.append((
            f"fix-{name}-{value}",
            padd(pvar(index), ONE) if value else pvar(index),
        ))
    reduced, _reduced_target, _eliminated = affine_eliminate_with_certificate(
        constraints, target
    )
    tables = (
        EQUAL_FACTOR_EXCEPTIONAL_LIFT_MULTIPLIERS
        if leaf.equal_factor else EXCEPTIONAL_LIFT_MULTIPLIERS
    )
    selected = []
    combination = ZERO
    for row, expression in tables[leaf.correction_return].items():
        label, constraint, lift = reduced[row - 1]
        multiplier = parse_singular_squarefree(expression, names)
        selected.append((label, constraint, multiplier, lift))
        combination = padd(combination, pmul(multiplier, constraint))
    if combination != ONE:
        raise RuntimeError(f"{leaf.camel}: stored certificate did not replay")
    return selected


def emit(leaf: ExceptionalLeaf) -> str:
    selected = reduced_certificate(leaf)
    stem = leaf.camel[0].lower() + leaf.camel[1:] + "Reduced"
    count = len(selected)
    lines = [
        "import UnrestrictedBooleanMul.ANF",
        "",
        "/-!",
        f"# Reduced aligned certificate: `{leaf.camel}`",
        "",
        "This generated module checks a sparse Boolean-polynomial unit",
        "identity.  External algebra was used only to discover the stored",
        "multipliers; Lean replays the identity without extra axioms.",
        "-/",
        "",
        "namespace UnrestrictedBooleanMul.N5",
        "noncomputable section",
        "set_option linter.unreachableTactic false",
        "set_option linter.unusedTactic false",
        "set_option linter.unusedSimpArgs false",
        "set_option linter.unnecessarySeqFocus false",
        "set_option maxRecDepth 8192",
        "",
        f"/-- The {count} reduced semantic generators in this unit certificate. -/",
        f"def {stem}Constraint (v : Fin 71 → F₂) : Fin {count} → F₂ :=",
        "  ![",
    ]
    for index, (label, constraint, _multiplier, _lift) in enumerate(selected):
        comma = "," if index + 1 < count else ""
        lines.extend((f"    -- {label}", f"    {lean_polynomial(constraint)}{comma}"))
    lines.extend(("  ]", ""))
    lines.extend((
        f"private def {stem}Multiplier (v : Fin 71 → F₂) : Fin {count} → F₂ :=",
        "  ![",
    ))
    for index, (label, _constraint, multiplier, _lift) in enumerate(selected):
        comma = "," if index + 1 < count else ""
        lines.extend((f"    -- {label}", f"    {lean_polynomial(multiplier)}{comma}"))
    lines.extend(("  ]", ""))
    lines.extend((
        f"private def {stem}Product (v : Fin 71 → F₂) : Fin {count} → F₂ :=",
        "  ![",
    ))
    for index, (label, constraint, multiplier, _lift) in enumerate(selected):
        comma = "," if index + 1 < count else ""
        lines.extend((
            f"    -- {label}",
            f"    {lean_polynomial(pmul(multiplier, constraint))}{comma}",
        ))
    lines.extend(("  ]", ""))
    lines.append(f"private def {stem}Combination (v : Fin 71 → F₂) : F₂ :=")
    for index in range(count):
        suffix = " +" if index + 1 < count else ""
        lines.append(
            f"  {stem}Multiplier v {index} * {stem}Constraint v {index}{suffix}"
        )
    lines.extend((
        "",
        "private theorem f2_mul_self (x : F₂) : x * x = x := by",
        "  rcases f2_eq_zero_or_one x with h | h <;> simp [h]",
        "",
        "private theorem f2_two_eq_zero : (2 : F₂) = 0 :=",
        "  CharTwo.two_eq_zero",
        "",
    ))
    for index in range(count):
        lines.extend((
            "set_option maxHeartbeats 1000000 in",
            f"private theorem {stem}_product_{index} (v : Fin 71 → F₂) :",
            f"    {stem}Multiplier v {index} * {stem}Constraint v {index} =",
            f"      {stem}Product v {index} := by",
            f"  simp [{stem}Multiplier, {stem}Constraint,",
            f"    {stem}Product, add_mul, mul_add]",
            "  all_goals ring_nf",
            "  all_goals simp only [pow_two, f2_mul_self]",
            "  all_goals (try rw [f2_two_eq_zero])",
            "  all_goals (try simp only [mul_zero, add_zero, zero_add])",
            "  all_goals ring_nf",
            "  all_goals simp [f2_two_eq_zero, CharTwo.ofNat_eq_mod]",
            "",
        ))
    product_lemmas = ", ".join(
        f"{stem}_product_{index}" for index in range(count)
    )
    lines.extend((
        "set_option maxHeartbeats 3000000 in",
        "set_option maxRecDepth 8192 in",
        f"private theorem {stem}_certificate (v : Fin 71 → F₂) :",
        f"    (1 : F₂) = {stem}Combination v := by",
        f"  unfold {stem}Combination",
        f"  rw [{product_lemmas}]",
        f"  simp [{stem}Product]",
        "  all_goals ring_nf",
        "  all_goals simp [CharTwo.ofNat_eq_mod]",
        "  all_goals ring",
        "",
        "/-- The selected reduced equations generate the unit ideal. -/",
        f"theorem {leaf.theorem}",
        "    (v : Fin 71 → F₂)",
        f"    (hzero : ∀ i : Fin {count}, {stem}Constraint v i = 0) :",
        "    False := by",
        "  have hone : (1 : F₂) = 0 := by",
        f"    rw [{stem}_certificate v]",
        f"    simp [{stem}Combination, hzero]",
        "  exact one_ne_zero hone",
        "",
        "end",
        "end UnrestrictedBooleanMul.N5",
        "",
    ))
    return "\n".join(lines)


def main() -> None:
    for leaf in LEAVES:
        path = LEAN_DIR / f"QuadraticReturnHistory{leaf.camel}Raw.lean"
        selected = reduced_certificate(leaf)
        path.write_text(emit(leaf), encoding="utf-8", newline="\n")
        lift_labels = {
            label for _name, _constraint, _multiplier, lift in selected
            for label in lift
        }
        lift_monomials = sum(
            len(coefficient)
            for _name, _constraint, _multiplier, lift in selected
            for coefficient in lift.values()
        )
        print(
            f"{path.relative_to(ROOT)} "
            f"lift_labels={len(lift_labels)} lift_monomials={lift_monomials}"
        )


if __name__ == "__main__":
    main()
