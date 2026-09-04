#!/usr/bin/env python3
"""Emit semantic Lean bridges for the four exceptional aligned leaves.

The compact unit certificates are produced by
``generate_exceptional_history_certificates.py``.  This generator closes the
remaining interface in three independently checked layers:

* every original Boolean polynomial is identified with a literal ANF high
  coefficient or a genuine target-quotient row;
* every affine substitution is replayed from an explicit ideal-membership
  certificate over those literal equations and the stated normal form;
* the correction-return bit split feeds the two compact unit certificates.
"""

from __future__ import annotations

from pathlib import Path

from generate_exceptional_history_certificates import (
    LEAN_DIR,
    LEAVES,
    ONE_ONE_FIXED,
    ROOT,
    ZERO_ONE_FIXED,
    ExceptionalLeaf,
    normalization_data,
    reduced_certificate,
    semantic_base_constraints,
    substitution_certificate_data,
)
from generate_mixed_semantic_bridges import finset, powerset
from quadratic_return_history_polynomial import lean_polynomial


QUOTIENT_ROWS = {
    6: (0, 0x081, 0x024),
    7: (1, 0x101, 0x028),
    13: (2, 0x042, 0x024),
    14: (3, 0x082, 0x028),
    16: (4, 0x202, 0x050),
    20: (5, 0x044, 0x028),
    21: (6, 0x084, 0x030),
    22: (7, 0x104, 0x050),
    23: (8, 0x204, 0x090),
    26: (9, 0x048, 0x030),
    28: (10, 0x108, 0x090),
    # The aligned certificates use the same two rows under the positions in
    # the unreduced quotient ledger.
    36: (0, 0x0A0, 0),
    39: (1, 0x0C0, 0),
}


def family_stem(equal_factor: bool) -> str:
    return "oneOneAligned" if equal_factor else "zeroOneAligned"


def family_camel(equal_factor: bool) -> str:
    return "OneOneAligned" if equal_factor else "ZeroOneAligned"


def family_kind(equal_factor: bool) -> str:
    return "oneOneDifference" if equal_factor else "zeroOne"


def family_fixed(equal_factor: bool) -> dict[str, int]:
    return ONE_ONE_FIXED if equal_factor else ZERO_ONE_FIXED


def leaves_for_family(equal_factor: bool) -> tuple[ExceptionalLeaf, ...]:
    return tuple(leaf for leaf in LEAVES if leaf.equal_factor == equal_factor)


def base_data(equal_factor: bool):
    """Return the ordered union of semantic equations needed by the family."""
    return semantic_base_constraints(equal_factor)


def boolean_normalization(equal_factor: bool) -> str:
    if not equal_factor:
        return ""
    return "  simp only [N3Certificate.pow_two_f2]\n  ring_nf\n"


def coefficient_bridge(
    equal_factor: bool, index: int, label: str,
) -> str:
    stem = family_stem(equal_factor)
    kind = family_kind(equal_factor)
    returned = label.startswith("return-high-")
    mask = int(label.rsplit("-", 1)[1], 16)
    source = "returned" if returned else "feedback"
    expression = (
        f"mixedReturnSection .{kind} p"
        if returned else f"mixedReturnFeedbackProduct .{kind} .zero p"
    )
    support = finset(mask)
    return f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem {stem}_base_constraint_{index}_eq_{source}_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    {stem}BaseConstraint p.vector {index} =
      ({expression}).coeff
        ⟨({support} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({support} : Finset (Fin 10)).powerset =
      {powerset(mask)} := by decide
  rw [hpowerset]
  simp (config := {{ decide := true }}) [{stem}BaseConstraint]
  simp_mixed_return_history
  ring_nf
{boolean_normalization(equal_factor)}\
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]
"""


def quotient_bridge(equal_factor: bool, index: int, label: str) -> str:
    stem = family_stem(equal_factor)
    kind = family_kind(equal_factor)
    position = int(label.rsplit("-", 1)[1])
    row, first, second = QUOTIENT_ROWS[position]
    if position in (36, 39):
        support = finset(first)
        return f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem {stem}_base_constraint_{index}_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    {stem}BaseConstraint p.vector {index} =
      alignedReturnQuotientCoordinate {row}
          (quadraticProjection 10 (mixedReturnSection .{kind} p)) +
        alignedReturnQuotientCoordinate {row}
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{kind} .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [alignedReturnQuotientCoordinate, alignedReturnQuotientPair,
    quadraticProjection, quadraticPair, aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({support} : Finset (Fin 10)).powerset =
      {powerset(first)} := by decide
  rw [hpowerset]
  simp (config := {{ decide := true }}) [{stem}BaseConstraint]
  simp_mixed_return_history
  ring_nf
{boolean_normalization(equal_factor)}\
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]
"""
    first_support = finset(first)
    second_support = finset(second)
    return f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem {stem}_base_constraint_{index}_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    {stem}BaseConstraint p.vector {index} =
      mixedReturnQuotientCoordinate {row}
          (quadraticProjection 10 (mixedReturnSection .{kind} p)) +
        mixedReturnQuotientCoordinate {row}
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{kind} .zero p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [mixedReturnQuotientCoordinate, mixedReturnQuotientFirstPair,
    mixedReturnQuotientSecondPair, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetFirst : ({first_support} : Finset (Fin 10)).powerset =
      {powerset(first)} := by decide
  have hpowersetSecond : ({second_support} : Finset (Fin 10)).powerset =
      {powerset(second)} := by decide
  rw [hpowersetFirst, hpowersetSecond]
  simp (config := {{ decide := true }}) [{stem}BaseConstraint]
  simp_mixed_return_history
  ring_nf
{boolean_normalization(equal_factor)}\
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod]
"""


def normal_form_structure(equal_factor: bool) -> str:
    camel = family_camel(equal_factor)
    fixed = family_fixed(equal_factor)
    accessors = {
        "ell": "p.ell",
        "m": "p.m",
        "x": "p.leftShift",
        "y": "p.rightShift",
    }
    lines = [
        "/-- The aligned representative selected by rational-place and",
        "`GL(2,F₂)` normalization. -/",
        f"structure {camel}NormalForm",
        "    (p : ZeroOneOffAxisHistoryParameters) : Prop where",
    ]
    for name, value in fixed.items():
        prefix = name.rstrip("0123456789")
        coordinate = int(name[len(prefix):])
        lines.append(
            f"  {name} : {accessors[prefix]} {coordinate} = ({value} : F₂)"
        )
    return "\n".join(lines)


def emit_base(equal_factor: bool) -> str:
    names, constraints = base_data(equal_factor)
    del names
    stem = family_stem(equal_factor)
    camel = family_camel(equal_factor)
    kind = family_kind(equal_factor)
    count = len(constraints)
    lines = [
        "import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic",
        "",
        "/-!",
        f"# Semantic equation base for `{camel}`",
        "",
        "This file computes the exact ANF meaning of every original history",
        "equation used by either correction-return branch.",
        "-/",
        "",
        "namespace UnrestrictedBooleanMul",
        "namespace N5",
        "",
        "noncomputable section",
        "",
        normal_form_structure(equal_factor),
        "",
        f"/-- Ordered union of the original history equations used by `{camel}`. -/",
        f"def {stem}BaseConstraint (v : Fin 71 → F₂) : Fin {count} → F₂ :=",
        "  ![",
    ]
    for index, (label, polynomial) in enumerate(constraints):
        comma = "," if index + 1 < count else ""
        lines.extend((f"    -- {label}", f"    {lean_polynomial(polynomial)}{comma}"))
    lines.extend(("  ]", ""))
    for index, (label, _polynomial) in enumerate(constraints):
        if label.startswith("quotient-"):
            lines.append(quotient_bridge(equal_factor, index, label))
        else:
            lines.append(coefficient_bridge(equal_factor, index, label))
    lines.extend((
        "/-- Literal quadratic-history hypotheses discharge the complete",
        f"equation base for `{camel}`. -/",
        f"theorem {stem}_base_equations_of_quadratic_history",
        "    (p : ZeroOneOffAxisHistoryParameters)",
        f"    (hreturned : mixedReturnSection .{kind} p ∈",
        "      N4.quadraticANFSpace 10)",
        f"    (hfeedback : mixedReturnFeedbackProduct .{kind} .zero p ∈",
        "      N4.quadraticANFSpace 10)",
        "    (hprojection :",
        "      quadraticQuotientProjection",
        f"          (quadraticProjection 10 (mixedReturnSection .{kind} p)) =",
        "        quadraticQuotientProjection",
        "          (quadraticProjection 10",
        f"            (mixedReturnFeedbackProduct .{kind} .zero p))) :",
        f"    ∀ i : Fin {count}, {stem}BaseConstraint p.vector i = 0 := by",
        "  intro i",
        "  fin_cases i",
    ))
    for index, (label, _polynomial) in enumerate(constraints):
        if label.startswith("return-high-"):
            mask = int(label.rsplit("-", 1)[1], 16)
            lines.extend((
                f"  · change {stem}BaseConstraint p.vector ({index} : Fin {count}) = 0",
                f"    rw [{stem}_base_constraint_{index}_eq_returned_coeff]",
                f"    exact hreturned ⟨{finset(mask)}⟩ (by decide)",
            ))
        elif label.startswith("product-high-"):
            mask = int(label.rsplit("-", 1)[1], 16)
            lines.extend((
                f"  · change {stem}BaseConstraint p.vector ({index} : Fin {count}) = 0",
                f"    rw [{stem}_base_constraint_{index}_eq_feedback_coeff]",
                f"    exact hfeedback ⟨{finset(mask)}⟩ (by decide)",
            ))
        else:
            position = int(label.rsplit("-", 1)[1])
            row = QUOTIENT_ROWS[position][0]
            theorem = (
                "alignedReturnQuotientCoordinate_add_eq_zero_of_projection"
                if position in (36, 39) else
                "mixedReturnQuotientCoordinate_add_eq_zero_of_projection"
            )
            lines.extend((
                f"  · change {stem}BaseConstraint p.vector ({index} : Fin {count}) = 0",
                f"    rw [{stem}_base_constraint_{index}_eq_quotient_row]",
                f"    exact {theorem}",
                f"      _ _ hprojection {row}",
            ))
    lines.extend(("", "end", "end N5", "end UnrestrictedBooleanMul", ""))
    return "\n".join(lines)


def source_data(leaf: ExceptionalLeaf):
    names, constraints, substitutions, certificates = (
        substitution_certificate_data(leaf)
    )
    used = {
        label for certificate in certificates.values() for label in certificate
    }
    source = [
        (label, polynomial)
        for label, polynomial in constraints
        if label in used
    ]
    return names, source, substitutions, certificates


def combination_name(leaf: ExceptionalLeaf, variable: str) -> str:
    stem = leaf.camel[0].lower() + leaf.camel[1:]
    return f"{stem}SubstitutionCombination_{variable}"


def emit_substitution_certificate(
    leaf: ExceptionalLeaf,
    names: list[str],
    source: list[tuple[str, object]],
    substitutions: dict[int, object],
    certificates: dict[int, dict[str, object]],
    index: int,
) -> str:
    stem = leaf.camel[0].lower() + leaf.camel[1:]
    variable = names[index]
    replacement = substitutions[index]
    source_index = {label: i for i, (label, _polynomial) in enumerate(source)}
    terms = [
        f"  ({lean_polynomial(multiplier)}) * {stem}SubstitutionSource v {source_index[label]}"
        for label, multiplier in certificates[index].items()
    ]
    combination = " +\n".join(terms) if terms else "  0"
    return f"""
private def {combination_name(leaf, variable)} (v : Fin 71 → F₂) : F₂ :=
{combination}

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
private theorem {stem}_substitution_{variable}_certificate
    (v : Fin 71 → F₂) :
    v {index} + ({lean_polynomial(replacement)}) =
      {combination_name(leaf, variable)} v := by
  simp [{combination_name(leaf, variable)}, {stem}SubstitutionSource,
    add_mul, mul_add]
  all_goals (try ring_nf)
  all_goals (try simp only [N3Certificate.pow_two_f2])
  all_goals (try ring_nf)
  all_goals (try simp [N3Certificate.two_eq_zero_f2, CharTwo.ofNat_eq_mod])
  all_goals ring

private theorem {stem}_substitution_{variable}_of_source_zero
    (v : Fin 71 → F₂)
    (hzero : ∀ i, {stem}SubstitutionSource v i = 0) :
    v {index} = {lean_polynomial(replacement)} := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  rw [{stem}_substitution_{variable}_certificate]
  simp [{combination_name(leaf, variable)}, hzero]
"""


def fixed_accessor(name: str) -> tuple[str, int]:
    prefix = name.rstrip("0123456789")
    coordinate = int(name[len(prefix):])
    accessors = {
        "ell": "ell",
        "m": "m",
        "x": "leftShift",
        "y": "rightShift",
    }
    return accessors[prefix], coordinate


def emit_semantic(leaf: ExceptionalLeaf) -> str:
    names, source, substitutions, certificates = source_data(leaf)
    base_names, base = base_data(leaf.equal_factor)
    del base_names
    base_index = {label: index for index, (label, _polynomial) in enumerate(base)}
    source_count = len(source)
    base_count = len(base)
    stem = leaf.camel[0].lower() + leaf.camel[1:]
    family = family_stem(leaf.equal_factor)
    family_c = family_camel(leaf.equal_factor)
    kind = family_kind(leaf.equal_factor)
    fixed = family_fixed(leaf.equal_factor)
    fixed_indices = {names.index(name): value for name, value in fixed.items()}
    correction_index = names.index("correctionReturn0")
    selected = reduced_certificate(leaf)
    selected_labels = [label for label, _c, _m, _l in selected]
    original_count = len(selected_labels)
    lines = [
        f"import UnrestrictedBooleanMul.N5.QuadraticReturnHistory{family_c}Base",
        f"import UnrestrictedBooleanMul.N5.QuadraticReturnHistory{leaf.camel}Normalization",
        "",
        "/-!",
        f"# Semantic closure of `{leaf.camel}`",
        "",
        "The affine normalizer is replayed here with explicit polynomial",
        "certificates before the compact unit certificate is applied.",
        "-/",
        "",
        "namespace UnrestrictedBooleanMul",
        "namespace N5",
        "",
        "noncomputable section",
        "set_option linter.unusedSimpArgs false",
        "set_option linter.unreachableTactic false",
        "set_option linter.unusedTactic false",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 3000000",
        "",
        "/-- The original equations actually used to derive the affine ledger. -/",
        f"private def {stem}SubstitutionSource",
        f"    (v : Fin 71 → F₂) : Fin {source_count} → F₂ :=",
        "  ![",
    ]
    for source_index, (label, polynomial) in enumerate(source):
        comma = "," if source_index + 1 < source_count else ""
        lines.extend((f"    -- {label}", f"    {lean_polynomial(polynomial)}{comma}"))
    lines.extend(("  ]", ""))
    derived = [index for index in substitutions if index not in fixed_indices and index != correction_index]
    for index in derived:
        lines.append(emit_substitution_certificate(
            leaf, names, source, substitutions, certificates, index
        ))
    lines.extend((
        "/-- The semantic high equations and normalized fixed values discharge",
        "every source equation used by affine elimination. -/",
        f"private theorem {stem}_substitution_source_eq_zero",
        "    (p : ZeroOneOffAxisHistoryParameters)",
        f"    (hnormal : {family_c}NormalForm p)",
        f"    (hcorrection : p.correctionReturn = ({leaf.correction_return} : F₂))",
        f"    (hbase : ∀ i : Fin {base_count}, {family}BaseConstraint p.vector i = 0) :",
        f"    ∀ i : Fin {source_count}, {stem}SubstitutionSource p.vector i = 0 := by",
        "  intro i",
        "  fin_cases i",
    ))
    for source_index, (label, _polynomial) in enumerate(source):
        if label.startswith("fix-"):
            fixed_name = label.removeprefix("fix-").rsplit("-", 1)[0]
            if fixed_name == "correctionReturn0":
                proof = "hcorrection"
            else:
                proof = f"hnormal.{fixed_name}"
            lines.extend((
                f"  · change {stem}SubstitutionSource p.vector ({source_index} : Fin {source_count}) = 0",
                f"    simp [{stem}SubstitutionSource,",
                f"      ZeroOneOffAxisHistoryParameters.vector, {proof}]",
            ))
        else:
            lines.extend((
                f"  · change {stem}SubstitutionSource p.vector ({source_index} : Fin {source_count}) = 0",
                f"    simpa [{stem}SubstitutionSource, {family}BaseConstraint] using",
                f"      hbase ({base_index[label]} : Fin {base_count})",
            ))
    lines.extend((
        "",
        "/-- All 29 substitutions used by the compact certificate follow from",
        "the literal history equations and the aligned normal form. -/",
        f"private theorem {stem}_substitutions_of_source_zero",
        "    (p : ZeroOneOffAxisHistoryParameters)",
        f"    (hnormal : {family_c}NormalForm p)",
        f"    (hcorrection : p.correctionReturn = ({leaf.correction_return} : F₂))",
        f"    (hsource : ∀ i : Fin {source_count},",
        f"      {stem}SubstitutionSource p.vector i = 0) :",
        f"    {leaf.camel}Substitutions p.vector := by",
        "  refine {",
    ))
    for index, replacement in substitutions.items():
        name = names[index]
        if index in fixed_indices:
            proof = (
                "by simpa [ZeroOneOffAxisHistoryParameters.vector] using "
                f"hnormal.{name}"
            )
        elif index == correction_index:
            proof = (
                "by simpa [ZeroOneOffAxisHistoryParameters.vector] using "
                "hcorrection"
            )
        else:
            proof = (
                f"{stem}_substitution_{name}_of_source_zero p.vector hsource"
            )
        lines.append(f"    {name} := {proof}")
    lines.extend(("  }", ""))
    _norm_names, original, _norm_substitutions = normalization_data(leaf)
    label_to_base = {label: base_index[label] for label, _poly in original}
    selected_map = ", ".join(
        str(label_to_base[label]) for label in selected_labels
    )
    lines.extend((
        "/-- The exceptional aligned leaf is inconsistent with the literal",
        "quadratic return-history hypotheses. -/",
        f"theorem {stem}_inconsistent_of_quadratic_history",
        "    (p : ZeroOneOffAxisHistoryParameters)",
        f"    (hnormal : {family_c}NormalForm p)",
        f"    (hcorrection : p.correctionReturn = ({leaf.correction_return} : F₂))",
        f"    (hreturned : mixedReturnSection .{kind} p ∈",
        "      N4.quadraticANFSpace 10)",
        f"    (hfeedback : mixedReturnFeedbackProduct .{kind} .zero p ∈",
        "      N4.quadraticANFSpace 10)",
        "    (hprojection :",
        "      quadraticQuotientProjection",
        f"          (quadraticProjection 10 (mixedReturnSection .{kind} p)) =",
        "        quadraticQuotientProjection",
        "          (quadraticProjection 10",
        f"            (mixedReturnFeedbackProduct .{kind} .zero p))) :",
        "    False := by",
        f"  have hbase := {family}_base_equations_of_quadratic_history p",
        "    hreturned hfeedback hprojection",
        f"  have hsource := {stem}_substitution_source_eq_zero p hnormal",
        "    hcorrection hbase",
        f"  have hsub := {stem}_substitutions_of_source_zero p hnormal",
        "    hcorrection hsource",
        f"  apply {stem}_inconsistent_of_original p.vector hsub",
        "  intro i",
        f"  simpa [{stem}OriginalConstraint] using",
        f"    hbase ((![{selected_map}] : Fin {original_count} → Fin {base_count}) i)",
        "",
        "end",
        "end N5",
        "end UnrestrictedBooleanMul",
        "",
    ))
    return "\n".join(lines)


def emit_aggregate() -> str:
    return """import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionZeroSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryZeroOneAlignedCorrectionOneSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedCorrectionZeroSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryOneOneAlignedCorrectionOneSemantic

/-!
# Aligned exceptional return-history closure

The final Boolean bit split removes the four exceptional aligned leaves.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

theorem zeroOneAligned_inconsistent_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : ZeroOneAlignedNormalForm p)
    (hreturned : mixedReturnSection .zeroOne p ∈ N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .zeroOne .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .zeroOne p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .zeroOne .zero p))) :
    False := by
  rcases f2_eq_zero_or_one p.correctionReturn with hzero | hone
  · exact zeroOneAlignedCorrectionZero_inconsistent_of_quadratic_history
      p hnormal hzero hreturned hfeedback hprojection
  · exact zeroOneAlignedCorrectionOne_inconsistent_of_quadratic_history
      p hnormal hone hreturned hfeedback hprojection

theorem oneOneAligned_inconsistent_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hnormal : OneOneAlignedNormalForm p)
    (hreturned : mixedReturnSection .oneOneDifference p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .oneOneDifference .zero p ∈
      N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnSection .oneOneDifference p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .oneOneDifference .zero p))) :
    False := by
  rcases f2_eq_zero_or_one p.correctionReturn with hzero | hone
  · exact oneOneAlignedCorrectionZero_inconsistent_of_quadratic_history
      p hnormal hzero hreturned hfeedback hprojection
  · exact oneOneAlignedCorrectionOne_inconsistent_of_quadratic_history
      p hnormal hone hreturned hfeedback hprojection

end
end N5
end UnrestrictedBooleanMul
"""


def main() -> None:
    for equal_factor in (False, True):
        path = LEAN_DIR / (
            f"QuadraticReturnHistory{family_camel(equal_factor)}Base.lean"
        )
        path.write_text(emit_base(equal_factor), encoding="utf-8", newline="\n")
        print(path.relative_to(ROOT))
    for leaf in LEAVES:
        path = LEAN_DIR / f"QuadraticReturnHistory{leaf.camel}Semantic.lean"
        path.write_text(emit_semantic(leaf), encoding="utf-8", newline="\n")
        print(path.relative_to(ROOT))
    aggregate = LEAN_DIR / "QuadraticReturnHistoryAlignedSemantic.lean"
    aggregate.write_text(emit_aggregate(), encoding="utf-8", newline="\n")
    print(aggregate.relative_to(ROOT))


if __name__ == "__main__":
    main()
