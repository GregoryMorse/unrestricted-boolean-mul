#!/usr/bin/env python3
"""Emit the six Lean semantic bridges for the mixed return certificates.

The raw certificate modules are generated polynomial identities.  This
generator emits only the auditable semantic glue: each selected raw equation
is identified with an ANF coefficient (or a target-annihilating quotient row),
then the raw identity is exposed through the literal circuit expressions.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LEAN_DIR = ROOT / "UnrestrictedBooleanMul" / "N5"


@dataclass(frozen=True)
class Leaf:
    camel: str
    raw: str
    raw_theorem: str
    kind: str
    direction: str
    return_masks: tuple[int, ...]
    product_masks: tuple[int, ...]
    quotient_positions: tuple[int, ...]
    ordered_entries: tuple[tuple[str, int], ...] = ()


SHORT_RETURN = (0x023, 0x025, 0x026, 0x061, 0x062, 0x221, 0x222)
SHORT_PRODUCT = (
    0x023, 0x025, 0x043, 0x045, 0x061, 0x062, 0x063, 0x064,
    0x065, 0x203, 0x205, 0x221, 0x222, 0x223, 0x224, 0x225,
)
SHORT_QUOTIENT = (6, 7, 13, 20)
INF_RETURN = (
    0x023, 0x025, 0x026, 0x029, 0x02A, 0x061, 0x062, 0x0A1,
    0x0A2, 0x121, 0x122,
)
INF_PRODUCT = (
    0x052, 0x058, 0x092, 0x094, 0x114, 0x118, 0x212, 0x214,
    0x218, 0x242, 0x248, 0x250, 0x252, 0x258, 0x282, 0x284,
    0x290, 0x292, 0x294, 0x304, 0x308, 0x310, 0x314, 0x318,
)
INF_QUOTIENT = (6, 7, 13, 14, 16, 21, 22, 23, 26, 28)
ONE_ONE_R1_ENTRIES = (
    *(("return", mask) for mask in (0x023, 0x031, 0x061, 0x0A1)),
    *(("product", mask) for mask in (
        0x023, 0x031, 0x043, 0x051, 0x061, 0x062, 0x063, 0x070,
        0x071, 0x083, 0x091, 0x0A1, 0x0A2, 0x0A3, 0x0B0, 0x0B1,
    )),
    *(("quotient", position) for position in (6, 7, 13, 14, 16, 23)),
    ("product", 0x0E3),
    ("product", 0x073),
)

LEAVES = (
    Leaf("OneTwoR0", "oneTwoR0", "oneTwo_R0_Raw_history_missing_eq_zero",
         "oneTwo", "zero", SHORT_RETURN, SHORT_PRODUCT, SHORT_QUOTIENT),
    Leaf("OneTwoR1", "oneTwoR1", "oneTwo_R1_Raw_history_missing_eq_zero",
         "oneTwo", "one", SHORT_RETURN, SHORT_PRODUCT, SHORT_QUOTIENT),
    Leaf("OneTwoRInf", "oneTwoRInf", "oneTwo_RInf_Raw_history_missing_eq_zero",
         "oneTwo", "infinity", INF_RETURN, INF_PRODUCT, INF_QUOTIENT),
    Leaf("OneThreeR0", "oneThreeR0", "oneThree_R0_Raw_history_missing_eq_zero",
         "oneThree", "zero", SHORT_RETURN, SHORT_PRODUCT, SHORT_QUOTIENT),
    Leaf("OneThreeR1", "oneThreeR1", "oneThree_R1_Raw_history_missing_eq_zero",
         "oneThree", "one", SHORT_RETURN, SHORT_PRODUCT, SHORT_QUOTIENT),
    Leaf("OneThreeRInf", "oneThreeRInf", "oneThree_RInf_Raw_history_missing_eq_zero",
         "oneThree", "infinity", INF_RETURN, INF_PRODUCT, INF_QUOTIENT),
    Leaf("OneOneR1", "oneOneR1", "oneOne_R1_Raw_history_missing_eq_zero",
         "oneOneDifference", "one", (), (), (), ONE_ONE_R1_ENTRIES),
)

# The quotient reducer rows are sums of two cross-plane coefficients on the
# same Hankel anti-diagonal.  The value is (index in the shared Lean table,
# first ANF support, second ANF support).
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
}


def coordinates(mask: int) -> tuple[int, ...]:
    return tuple(i for i in range(10) if mask & (1 << i))


def finset(mask: int) -> str:
    values = ", ".join(str(i) for i in coordinates(mask))
    return "{" + values + "}"


def powerset(mask: int) -> str:
    terms = [finset(subset) for subset in range(1 << 10)
             if subset & ~mask == 0]
    terms[0] = "∅"
    return "{" + ", ".join(terms) + "}"


def boolean_idempotence_normalization(leaf: Leaf) -> str:
    """Normalize squares introduced by the m = mDifference + ell chart."""
    if leaf.kind != "oneOneDifference":
        return ""
    return "  simp only [N3Certificate.pow_two_f2]\n  ring_nf\n"


def coefficient_bridge(leaf: Leaf, index: int, mask: int,
                       returned: bool) -> str:
    name = "returned" if returned else "feedback"
    expression = (f"mixedReturnSection .{leaf.kind} p" if returned else
                  f"mixedReturnFeedbackProduct .{leaf.kind} "
                  f".{leaf.direction} p")
    support = finset(mask)
    boolean_normalization = boolean_idempotence_normalization(leaf)
    return f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem {leaf.raw}_constraint_{index}_eq_{name}_coeff
    (p : ZeroOneOffAxisHistoryParameters) :
    {leaf.raw}RawConstraint p.vector {index} =
      ({expression}).coeff
        ⟨({support} : Finset (Fin 10))⟩ := by
  rw [coeff_eq_cube_eval_sum]
  have hpowerset : ({support} : Finset (Fin 10)).powerset =
      {powerset(mask)} := by decide
  rw [hpowerset]
  simp (config := {{ decide := true }}) [{leaf.raw}RawConstraint]
  simp_mixed_return_history
  ring_nf
{boolean_normalization}\
  simp [CharTwo.ofNat_eq_mod]
"""


def quotient_bridge(leaf: Leaf, index: int, position: int) -> str:
    row, first, second = QUOTIENT_ROWS[position]
    first_support = finset(first)
    second_support = finset(second)
    boolean_normalization = boolean_idempotence_normalization(leaf)
    return f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem {leaf.raw}_constraint_{index}_eq_quotient_row
    (p : ZeroOneOffAxisHistoryParameters) :
    {leaf.raw}RawConstraint p.vector {index} =
      mixedReturnQuotientCoordinate {row}
          (quadraticProjection 10 (mixedReturnSection .{leaf.kind} p)) +
        mixedReturnQuotientCoordinate {row}
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p)) := by
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
  simp (config := {{ decide := true }}) [{leaf.raw}RawConstraint]
  simp_mixed_return_history
  ring_nf
{boolean_normalization}\
  ring_nf
  simp [CharTwo.ofNat_eq_mod]
"""


def target_bridge(leaf: Leaf) -> str:
    boolean_normalization = boolean_idempotence_normalization(leaf)
    return f"""
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem {leaf.raw}RawTarget_eq_missingCoordinate
    (p : ZeroOneOffAxisHistoryParameters) :
    {leaf.raw}RawTarget p.vector =
      returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .{leaf.kind} p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p)) := by
  apply (N4.f2_eq_iff_add_eq_zero _ _).2
  simp [returnHistoryMissingCoordinate, quadraticProjection, quadraticPair,
    aCoord, bCoord]
  simp_rw [coeff_eq_cube_eval_sum]
  have hpowersetZeroSeven : ({{0, 7}} : Finset (Fin 10)).powerset =
      {{∅, {{0}}, {{7}}, {{0, 7}}}} := by decide
  have hpowersetZeroEight : ({{0, 8}} : Finset (Fin 10)).powerset =
      {{∅, {{0}}, {{8}}, {{0, 8}}}} := by decide
  have hpowersetOneNine : ({{1, 9}} : Finset (Fin 10)).powerset =
      {{∅, {{1}}, {{9}}, {{1, 9}}}} := by decide
  have hpowersetTwoNine : ({{2, 9}} : Finset (Fin 10)).powerset =
      {{∅, {{2}}, {{9}}, {{2, 9}}}} := by decide
  rw [hpowersetZeroSeven, hpowersetZeroEight, hpowersetOneNine,
    hpowersetTwoNine]
  simp (config := {{ decide := true }}) [{leaf.raw}RawTarget]
  simp_mixed_return_history
  ring_nf
{boolean_normalization}\
  ring_nf
  simp [CharTwo.ofNat_eq_mod]
"""


def aggregate(leaf: Leaf) -> str:
    entries = ordered_entries(leaf)
    count = len(entries)
    lines = []
    for index, (kind, value) in enumerate(entries):
        if kind == "return":
            lines.append(
                f"  · change {leaf.raw}RawConstraint p.vector "
                f"({index} : Fin {count}) = 0\n"
                f"    rw [{leaf.raw}_constraint_{index}_eq_returned_coeff]\n"
                f"    exact hreturned ⟨{finset(value)}⟩ (by decide)")
        elif kind == "product":
            lines.append(
                f"  · change {leaf.raw}RawConstraint p.vector "
                f"({index} : Fin {count}) = 0\n"
                f"    rw [{leaf.raw}_constraint_{index}_eq_feedback_coeff]\n"
                f"    exact hfeedback ⟨{finset(value)}⟩ (by decide)")
        else:
            row = QUOTIENT_ROWS[value][0]
            lines.append(
                f"  · change {leaf.raw}RawConstraint p.vector "
                f"({index} : Fin {count}) = 0\n"
                f"    rw [{leaf.raw}_constraint_{index}_eq_quotient_row]\n"
                f"    exact mixedReturnQuotientCoordinate_add_eq_zero_of_projection "
                f"_ _ hprojection {row}")
    cases = "\n".join(lines)
    return f"""
/-- The literal quadratic-history hypotheses discharge every equation in
the `{leaf.camel}` raw certificate. -/
theorem {leaf.raw}_equations_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .{leaf.kind} p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .{leaf.kind}
      .{leaf.direction} p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .{leaf.kind} p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p))) :
    ∀ i : Fin {count}, {leaf.raw}RawConstraint p.vector i = 0 := by
  intro i
  fin_cases i
{cases}

/-- Kernel-checked vanishing of the sparse missing-target row for this
mixed history leaf. -/
theorem {leaf.raw}_missingCoordinate_eq_zero_of_quadratic_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .{leaf.kind} p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .{leaf.kind}
      .{leaf.direction} p ∈ N4.quadraticANFSpace 10)
    (hprojection :
      quadraticQuotientProjection
          (quadraticProjection 10 (mixedReturnSection .{leaf.kind} p)) =
        quadraticQuotientProjection
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p))) :
    returnHistoryMissingCoordinate
          (quadraticProjection 10 (mixedReturnSection .{leaf.kind} p)) +
        returnHistoryMissingCoordinate
          (quadraticProjection 10
            (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p)) = 0 := by
  rw [← {leaf.raw}RawTarget_eq_missingCoordinate p]
  exact {leaf.raw_theorem} p.vector
    ({leaf.raw}_equations_of_quadratic_history p hreturned hfeedback hprojection)

/-- Circuit-facing missing-coset exclusion for this normalized mixed
history leaf. -/
theorem firstOrderMissingFunctional_eq_zero_of_{leaf.raw}_history
    (p : ZeroOneOffAxisHistoryParameters)
    (hreturned : mixedReturnSection .{leaf.kind} p ∈
      N4.quadraticANFSpace 10)
    (hfeedback : mixedReturnFeedbackProduct .{leaf.kind}
      .{leaf.direction} p ∈ N4.quadraticANFSpace 10)
    (c : TargetCoeff)
    (htarget :
      quadraticProjection 10 (mixedReturnSection .{leaf.kind} p) +
          quadraticProjection 10
            (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p) =
        targetTwo c) :
    firstOrderMissingFunctional c = 0 := by
  let q := quadraticProjection 10 (mixedReturnSection .{leaf.kind} p)
  let r := quadraticProjection 10
    (mixedReturnFeedbackProduct .{leaf.kind} .{leaf.direction} p)
  have hprojection : quadraticQuotientProjection q =
      quadraticQuotientProjection r :=
    quadraticQuotientProjection_eq_of_add_eq_target q r c htarget
  exact firstOrderMissingFunctional_eq_zero_of_missingCoordinate q r c
    ({leaf.raw}_missingCoordinate_eq_zero_of_quadratic_history p
      hreturned hfeedback hprojection) htarget
"""


def emit(leaf: Leaf) -> str:
    header = f"""import UnrestrictedBooleanMul.N5.QuadraticReturnHistoryMixedSemantic
import UnrestrictedBooleanMul.N5.QuadraticReturnHistory{leaf.camel}Raw

/-!
# Semantic bridge for the `{leaf.camel}` return-history certificate

This generated module relates every raw Boolean-polynomial generator to a
literal ANF coefficient or to a genuine target-quotient row.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section
"""
    parts = [header, target_bridge(leaf)]
    for index, (kind, value) in enumerate(ordered_entries(leaf)):
        if kind == "return":
            parts.append(coefficient_bridge(leaf, index, value, True))
        elif kind == "product":
            parts.append(coefficient_bridge(leaf, index, value, False))
        else:
            parts.append(quotient_bridge(leaf, index, value))
    parts.append(aggregate(leaf))
    parts.append("\nend\nend N5\nend UnrestrictedBooleanMul\n")
    return "".join(parts)


def ordered_entries(leaf: Leaf) -> tuple[tuple[str, int], ...]:
    if leaf.ordered_entries:
        return leaf.ordered_entries
    return (
        *(("return", mask) for mask in leaf.return_masks),
        *(("product", mask) for mask in leaf.product_masks),
        *(("quotient", position) for position in leaf.quotient_positions),
    )


def main() -> None:
    for leaf in LEAVES:
        path = LEAN_DIR / f"QuadraticReturnHistory{leaf.camel}Semantic.lean"
        path.write_text(emit(leaf), encoding="utf-8", newline="\n")
        print(path.relative_to(ROOT))


if __name__ == "__main__":
    main()
