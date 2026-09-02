import UnrestrictedBooleanMul.N5.LocalKlein

/-!
# Fixed-block rank certificates for the two-defect envelopes

This file formalizes the three `5 × 5` cross-matrix calculations in
manuscript equations (10.6), (10.8), and (10.11).  Rank at most two is
expressed algebraically by the vanishing of all `3 × 3` minors.  Only the
four target-class bits and seven displayed completion coordinates occur.
-/

namespace UnrestrictedBooleanMul
namespace N5
namespace E2

abbrev TargetClass := Fin 4 → F₂
abbrev Completion := Fin 7 → F₂
abbrev CrossMatrix := Fin 5 → Fin 5 → F₂

/-- A four-bit class written in the manuscript's left-to-right order. -/
def word (a b c d : F₂) : TargetClass := ![d, c, b, a]

theorem targetClass_eq_word (c : TargetClass) :
    c = word (c 3) (c 2) (c 1) (c 0) := by
  funext i
  fin_cases i <;> rfl

/-- The ten increasing triples of indices in a five-element set. -/
def indexTriple : Fin 10 → Fin 3 → Fin 5 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 1, 4], ![0, 2, 3], ![0, 2, 4],
    ![0, 3, 4], ![1, 2, 3], ![1, 2, 4], ![1, 3, 4], ![2, 3, 4]]

/-- A `3 × 3` determinant.  In characteristic two all six permutation
terms have positive sign. -/
def minorThree (M : CrossMatrix) (r s : Fin 10) : F₂ :=
  let i := indexTriple r
  let j := indexTriple s
  M (i 0) (j 0) * M (i 1) (j 1) * M (i 2) (j 2) +
  M (i 0) (j 1) * M (i 1) (j 2) * M (i 2) (j 0) +
  M (i 0) (j 2) * M (i 1) (j 0) * M (i 2) (j 1) +
  M (i 0) (j 2) * M (i 1) (j 1) * M (i 2) (j 0) +
  M (i 0) (j 1) * M (i 1) (j 0) * M (i 2) (j 2) +
  M (i 0) (j 0) * M (i 1) (j 2) * M (i 2) (j 1)

/-- Algebraic rank-at-most-two condition used by all three certificates. -/
def RankLETwo (M : CrossMatrix) : Prop :=
  ∀ r s : Fin 10, minorThree M r s = 0

instance (M : CrossMatrix) : Decidable (RankLETwo M) := by
  unfold RankLETwo
  infer_instance

theorem not_rankLETwo_of_minor_eq_one {M : CrossMatrix} {r s : Fin 10}
    (hminor : minorThree M r s = 1) : ¬ RankLETwo M := by
  intro hrank
  exact one_ne_zero (hminor.symm.trans (hrank r s))

/-! ## The degree-two envelope `W_*` -/

/-- The completed cross matrix in the `2+3` degree-two block coordinates.
The first four completion bits fill the arbitrary `2 × 2` local block and
the last three fill the remote diagonal. -/
def wStarMatrix (c : TargetClass) (z : Completion) : CrossMatrix :=
  ![
    ![z 0, z 1, c 0 + c 1 + c 3, c 1, c 1 + c 2],
    ![z 2, z 3, c 1 + c 2, c 2, c 2 + c 3],
    ![c 0 + c 1 + c 3, c 1 + c 2, z 4,
      c 0 + c 1 + c 2 + c 3, c 0],
    ![c 1, c 2, c 0 + c 1 + c 2 + c 3, z 5,
      c 1 + c 2 + c 3],
    ![c 1 + c 2, c 2 + c 3, c 0, c 1 + c 2 + c 3, z 6]
  ]

def WStarCompletable (c : TargetClass) : Prop :=
  ∃ z : Completion, RankLETwo (wStarMatrix c z)

instance (c : TargetClass) : Decidable (WStarCompletable c) := by
  unfold WStarCompletable
  infer_instance

/-- The three low-rank classes in manuscript equation (10.6), with `c 0`
the rightmost displayed bit. -/
def WStarLowClass (c : TargetClass) : Prop :=
  c = ![1, 0, 0, 0] ∨ c = ![1, 0, 0, 1] ∨ c = ![0, 1, 1, 1]

instance (c : TargetClass) : Decidable (WStarLowClass c) := by
  unfold WStarLowClass
  infer_instance

/-! ## The two-rational envelope `W_{0∞}` -/

/-- The completed cross matrix in the `2+2+1` two-rational coordinates.
The completion bits fill the two symmetric local blocks and the final
diagonal entry. -/
def wPQMatrix (c : TargetClass) (z : Completion) : CrossMatrix :=
  ![
    ![z 0, z 1, c 3, c 0 + c 1 + c 2 + c 3, c 1 + c 3],
    ![z 1, z 2, c 0 + c 1 + c 2, c 0 + c 2, c 1 + c 2],
    ![c 3, c 0 + c 1 + c 2, z 3, z 4, c 1],
    ![c 0 + c 1 + c 2 + c 3, c 0 + c 2, z 4, z 5, c 0 + c 1],
    ![c 1 + c 3, c 1 + c 2, c 1, c 0 + c 1, z 6]
  ]

def WPQCompletable (c : TargetClass) : Prop :=
  ∃ z : Completion, RankLETwo (wPQMatrix c z)

instance (c : TargetClass) : Decidable (WPQCompletable c) := by
  unfold WPQCompletable
  infer_instance

/-- The seven low-rank classes in manuscript equation (10.8). -/
def WPQLowClass (c : TargetClass) : Prop :=
  c = ![0, 1, 0, 0] ∨ c = ![1, 0, 1, 0] ∨
  c = ![1, 1, 1, 0] ∨ c = ![0, 0, 0, 1] ∨
  c = ![1, 0, 0, 1] ∨ c = ![1, 1, 0, 1] ∨
  c = ![1, 1, 1, 1]

instance (c : TargetClass) : Decidable (WPQLowClass c) := by
  unfold WPQLowClass
  infer_instance

/-! ## The length-three rational envelope `W_{3P}` -/

/-- The completed cross matrix in the length-three coordinates
`(x₀,x₁,x₂,z,y)`. -/
def wThreePMatrix (c : TargetClass) (z : Completion) : CrossMatrix :=
  ![
    ![z 0, z 1, z 2, c 0 + c 3, c 0 + c 2 + c 3],
    ![z 1, z 2 + z 3, c 0 + c 1 + c 2 + c 3,
      c 0 + c 2, c 0 + c 1 + c 2],
    ![z 2, c 0 + c 1 + c 2 + c 3, z 4,
      c 0 + c 1, c 1],
    ![c 0 + c 3, c 0 + c 2, c 0 + c 1, z 5, c 0],
    ![c 0 + c 2 + c 3, c 0 + c 1 + c 2, c 1, c 0, z 6]
  ]

def WThreePCompletable (c : TargetClass) : Prop :=
  ∃ z : Completion, RankLETwo (wThreePMatrix c z)

instance (c : TargetClass) : Decidable (WThreePCompletable c) := by
  unfold WThreePCompletable
  infer_instance

/-- Equation (10.11): the nonzero vectors in the hyperplane
`c₃+c₄+c₆=0`, together with the two exceptional outside vectors. -/
def WThreePLowClass (c : TargetClass) : Prop :=
  (c 3 + c 2 + c 0 = 0 ∧ c ≠ 0) ∨
    c = ![1, 0, 0, 0] ∨ c = ![1, 1, 1, 1]

instance (c : TargetClass) : Decidable (WThreePLowClass c) := by
  unfold WThreePLowClass
  infer_instance

end E2
end N5
end UnrestrictedBooleanMul
