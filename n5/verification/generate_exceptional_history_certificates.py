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
    affine_eliminate,
    affine_eliminate_with_substitution_certificates,
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


def normalization_data(leaf: ExceptionalLeaf):
    q = r0 if leaf.equal_factor else 0
    constraints, target, names = equations(
        q,
        r0,
        r0,
        equal_factor_difference_coordinates=leaf.equal_factor,
    )
    original_by_name = dict(constraints)
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
    _reduced, _target, substitutions = affine_eliminate(constraints, target)
    selected = reduced_certificate(leaf)
    original = [
        (label, original_by_name[label])
        for label, _constraint, _multiplier, _lift in selected
    ]
    return names, original, substitutions


def substitution_certificate_data(leaf: ExceptionalLeaf):
    """Return and independently replay every affine-substitution certificate."""
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
    (_reduced, _target, substitutions, certificates) = (
        affine_eliminate_with_substitution_certificates(constraints, target)
    )
    originals = dict(constraints)
    for index, replacement in substitutions.items():
        expanded = padd(*(
            pmul(multiplier, originals[label])
            for label, multiplier in certificates[index].items()
        ))
        if expanded != padd(pvar(index), replacement):
            raise RuntimeError(
                f"{leaf.camel}: substitution certificate {names[index]} failed"
            )
    return names, constraints, substitutions, certificates


def semantic_base_constraints(equal_factor: bool):
    """Ordered union of literal history equations needed by both bit leaves."""
    family_leaves = tuple(
        leaf for leaf in LEAVES if leaf.equal_factor == equal_factor
    )
    names, constraints, _substitutions, _certificates = (
        substitution_certificate_data(family_leaves[0])
    )
    semantic_constraints = [
        (label, polynomial)
        for label, polynomial in constraints
        if not label.startswith("fix-")
    ]
    needed: set[str] = set()
    for leaf in family_leaves:
        _names, _constraints, _substitutions, certificates = (
            substitution_certificate_data(leaf)
        )
        needed.update(
            label
            for certificate in certificates.values()
            for label in certificate
            if not label.startswith("fix-")
        )
        needed.update(
            label
            for label, _constraint, _multiplier, _lift
            in reduced_certificate(leaf)
        )
    selected = [
        (label, polynomial)
        for label, polynomial in semantic_constraints
        if label in needed
    ]
    if {label for label, _polynomial in selected} != needed:
        raise RuntimeError("semantic base omitted a required history equation")
    return names, selected


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


def emit_normalization(leaf: ExceptionalLeaf) -> str:
    names, original, substitutions = normalization_data(leaf)
    raw_stem = leaf.camel[0].lower() + leaf.camel[1:] + "Reduced"
    stem = leaf.camel[0].lower() + leaf.camel[1:]
    count = len(original)
    family = "oneOneAligned" if leaf.equal_factor else "zeroOneAligned"
    family_camel = "OneOneAligned" if leaf.equal_factor else "ZeroOneAligned"
    _base_names, base = semantic_base_constraints(leaf.equal_factor)
    base_index = {label: index for index, (label, _polynomial) in enumerate(base)}
    selected_indices = [base_index[label] for label, _polynomial in original]
    base_count = len(base)
    fields = [
        (names[index], index, replacement)
        for index, replacement in substitutions.items()
    ]
    simp_fields = ", ".join(f"h.{name}" for name, _index, _value in fields)
    lines = [
        f"import UnrestrictedBooleanMul.N5.QuadraticReturnHistory{leaf.camel}Raw",
        "import UnrestrictedBooleanMul.N3Certificate",
        f"import UnrestrictedBooleanMul.N5.QuadraticReturnHistory{family_camel}Base",
        "",
        "/-!",
        f"# Affine normalization bridge: `{leaf.camel}`",
        "",
        "The reduced unit certificate is related here to the original",
        "return-history generators by the exact affine substitutions produced",
        "during certificate reduction.",
        "-/",
        "",
        "namespace UnrestrictedBooleanMul.N5",
        "noncomputable section",
        "set_option linter.unusedSimpArgs false",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 3000000",
        "",
        f"/-- Original semantic generators selected by the `{leaf.camel}` unit certificate. -/",
        f"def {stem}OriginalConstraint (v : Fin 71 → F₂) : Fin {count} → F₂ :=",
        f"  fun i => {family}BaseConstraint v",
        "    ((![",
    ]
    lines.append(
        "      " + ", ".join(str(index) for index in selected_indices)
        + f"] : Fin {count} → Fin {base_count}) i)"
    )
    lines.append("")
    lines.extend((
        "/-- The affine substitution ledger used by the reduced certificate. -/",
        f"structure {leaf.camel}Substitutions (v : Fin 71 → F₂) : Prop where",
    ))
    for name, index, replacement in fields:
        lines.append(f"  {name} : v {index} = {lean_polynomial(replacement)}")
    lines.extend((
        "",
        "/-- Under the exact substitution ledger, each reduced generator is",
        "the corresponding original history generator. -/",
        f"theorem {stem}ReducedConstraint_eq_original",
        "    (v : Fin 71 → F₂)",
        f"    (h : {leaf.camel}Substitutions v)",
        f"    (i : Fin {count}) :",
        f"    {raw_stem}Constraint v i = {stem}OriginalConstraint v i := by",
        "  fin_cases i <;>",
        f"    simp [{raw_stem}Constraint, {stem}OriginalConstraint,",
        f"      {family}BaseConstraint, {simp_fields}] <;>",
        "    (try ring_nf) <;>",
        "    (try simp [N3Certificate.pow_two_f2, N3Certificate.two_eq_zero_f2,",
        "      CharTwo.ofNat_eq_mod]) <;>",
        "    (try ring_nf) <;>",
        "    (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])",
        "",
        "/-- Original selected equations plus the substitution ledger are",
        "inconsistent. -/",
        f"theorem {stem}_inconsistent_of_original",
        "    (v : Fin 71 → F₂)",
        f"    (hsub : {leaf.camel}Substitutions v)",
        f"    (hzero : ∀ i : Fin {count}, {stem}OriginalConstraint v i = 0) :",
        "    False := by",
        f"  apply {leaf.theorem} v",
        "  intro i",
        f"  rw [{stem}ReducedConstraint_eq_original v hsub i]",
        "  exact hzero i",
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
        _names, _constraints, substitutions, certificates = (
            substitution_certificate_data(leaf)
        )
        print(
            f"  substitutions={len(substitutions)} "
            f"certificate_labels={sum(len(c) for c in certificates.values())} "
            f"certificate_monomials={sum(len(m) for c in certificates.values() for m in c.values())}"
        )
        print(
            "  substitution_label_union="
            + ",".join(sorted({label for c in certificates.values() for label in c}))
        )
        normalization_path = LEAN_DIR / (
            f"QuadraticReturnHistory{leaf.camel}Normalization.lean"
        )
        normalization_path.write_text(
            emit_normalization(leaf), encoding="utf-8", newline="\n"
        )
        print(normalization_path.relative_to(ROOT))


if __name__ == "__main__":
    main()
