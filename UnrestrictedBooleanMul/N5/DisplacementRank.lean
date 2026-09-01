import UnrestrictedBooleanMul.N5.DisplacementProfile

/-!
# Numerical displacement rank

This module converts the exact represented-place subspace profile into its
dimension formula.  The active directions are a subfamily of the eight
independent closed-place directions, so the argument is linear algebra rather
than an enumeration of quotient points or circuits.
-/

namespace UnrestrictedBooleanMul
namespace N5

noncomputable section

/-- The three rational evaluation directions are always active; the rational
jet directions and the two degree-two directions are active precisely when
their corresponding place is represented in `Q`. -/
def IsActiveDisplacementDirection
    (Q : Submodule F₂ QuadraticQuotient) : Fin 8 → Prop :=
  ![True, True, True,
    IsRepresentedPlace Q 0,
    IsRepresentedPlace Q 1,
    IsRepresentedPlace Q 2,
    IsRepresentedPlace Q 3,
    IsRepresentedPlace Q 3]

abbrev ActiveDisplacementDirection
    (Q : Submodule F₂ QuadraticQuotient) :=
  {i : Fin 8 // IsActiveDisplacementDirection Q i}

noncomputable instance activeDisplacementDirectionFintype
    (Q : Submodule F₂ QuadraticQuotient) :
    Fintype (ActiveDisplacementDirection Q) :=
  Fintype.ofFinite _

/-- Active closed-place coefficient directions embedded in ambient
two-forms. -/
def activeDisplacementTwoDirection
    (Q : Submodule F₂ QuadraticQuotient)
    (i : ActiveDisplacementDirection Q) : TwoForm :=
  targetTwo (closedPlaceDirections i.1)

def activeDisplacementTwoSpace
    (Q : Submodule F₂ QuadraticQuotient) : Submodule F₂ TwoForm :=
  Submodule.span F₂
    (Set.range (activeDisplacementTwoDirection Q))

theorem activeDisplacementTwoDirection_linearIndependent
    (Q : Submodule F₂ QuadraticQuotient) :
    LinearIndependent F₂ (activeDisplacementTwoDirection Q) := by
  have hcoeff : LinearIndependent F₂
      (fun i : ActiveDisplacementDirection Q =>
        closedPlaceDirections i.1) :=
    closedPlaceDirections_linearIndependent.comp
      (fun i : ActiveDisplacementDirection Q => i.1)
      Subtype.val_injective
  have hmap := hcoeff.map' targetTwoLinear
    (LinearMap.ker_eq_bot_of_injective targetTwoLinear_injective)
  exact hmap

theorem activeDisplacementTwoSpace_finrank
    (Q : Submodule F₂ QuadraticQuotient) :
    Module.finrank F₂ (activeDisplacementTwoSpace Q) =
      Fintype.card (ActiveDisplacementDirection Q) := by
  exact finrank_span_eq_card
    (activeDisplacementTwoDirection_linearIndependent Q)

/-- Number of represented rational place types. -/
noncomputable def representedRationalPlaceCount
    (Q : Submodule F₂ QuadraticQuotient) : Nat := by
  classical
  exact (if IsRepresentedPlace Q 0 then 1 else 0) +
    (if IsRepresentedPlace Q 1 then 1 else 0) +
    (if IsRepresentedPlace Q 2 then 1 else 0)

/-- Indicator for representation of the degree-two place. -/
noncomputable def representedDegreeTwoIndicator
    (Q : Submodule F₂ QuadraticQuotient) : Nat := by
  classical
  exact if IsRepresentedPlace Q 3 then 1 else 0

/-- Weighted number of represented infinitesimal directions. -/
def representedPlaceWeight
    (Q : Submodule F₂ QuadraticQuotient) : Nat :=
  representedRationalPlaceCount Q +
    2 * representedDegreeTwoIndicator Q

/-- The concrete finite set underlying `ActiveDisplacementDirection`.  Keeping
this description separate makes the cardinality calculation insensitive to
the classical decidability instance used for represented places. -/
noncomputable def activeDisplacementDirectionFinset
    (Q : Submodule F₂ QuadraticQuotient) : Finset (Fin 8) := by
  classical
  exact {0, 1, 2} ∪
    (if IsRepresentedPlace Q 0 then {3} else ∅) ∪
    (if IsRepresentedPlace Q 1 then {4} else ∅) ∪
    (if IsRepresentedPlace Q 2 then {5} else ∅) ∪
    (if IsRepresentedPlace Q 3 then {6, 7} else ∅)

noncomputable def filteredActiveDisplacementDirections
    (Q : Submodule F₂ QuadraticQuotient) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter (IsActiveDisplacementDirection Q)

theorem activeDisplacementDirection_filter_eq
    (Q : Submodule F₂ QuadraticQuotient) :
    filteredActiveDisplacementDirections Q =
      activeDisplacementDirectionFinset Q := by
  classical
  by_cases h0 : IsRepresentedPlace Q 0 <;>
    by_cases h1 : IsRepresentedPlace Q 1 <;>
      by_cases h2 : IsRepresentedPlace Q 2 <;>
        by_cases h3 : IsRepresentedPlace Q 3 <;>
          ext i <;> fin_cases i <;>
            simp [filteredActiveDisplacementDirections,
              IsActiveDisplacementDirection,
              activeDisplacementDirectionFinset, h0, h1, h2, h3]

theorem activeDisplacementDirection_card
    (Q : Submodule F₂ QuadraticQuotient) :
    Fintype.card (ActiveDisplacementDirection Q) =
      3 + representedPlaceWeight Q := by
  classical
  by_cases h0 : IsRepresentedPlace Q 0 <;>
    by_cases h1 : IsRepresentedPlace Q 1 <;>
      by_cases h2 : IsRepresentedPlace Q 2 <;>
        by_cases h3 : IsRepresentedPlace Q 3 <;>
          rw [Fintype.card_subtype] <;>
          change (filteredActiveDisplacementDirections Q).card = _ <;>
          rw [activeDisplacementDirection_filter_eq] <;>
          simp [activeDisplacementDirectionFinset,
            representedPlaceWeight, representedRationalPlaceCount,
            representedDegreeTwoIndicator, h0, h1, h2, h3]

/-! ## Identification with the intrinsic displacement space -/

theorem activeDisplacementTwoDirection_mem
    (Q : Submodule F₂ QuadraticQuotient) (i : Fin 8)
    (hi : IsActiveDisplacementDirection Q i) :
    targetTwo (closedPlaceDirections i) ∈
      activeDisplacementTwoSpace Q := by
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

theorem rationalTwoSpace_le_activeDisplacementTwoSpace
    (Q : Submodule F₂ QuadraticQuotient) :
    rationalTwoSpace ≤ activeDisplacementTwoSpace Q := by
  rintro p ⟨c, hc, rfl⟩
  refine Submodule.span_induction
    (p := fun c _ => targetTwo c ∈ activeDisplacementTwoSpace Q)
    ?_ ?_ ?_ ?_ hc
  · intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 0 (by
          simp [IsActiveDisplacementDirection])
    · simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 1 (by
          simp [IsActiveDisplacementDirection])
    · simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 2 (by
          simp [IsActiveDisplacementDirection])
  · simp [targetTwo]
  · intro x y _ _ hx hy
    simpa [targetTwo] using
      Submodule.add_mem (activeDisplacementTwoSpace Q) hx hy
  · intro a x _ hx
    simpa [targetTwo] using
      Submodule.smul_mem (activeDisplacementTwoSpace Q) a hx

/-- Every represented target plane is generated by its active jet
directions together with the three always-active rational directions. -/
theorem closedPlaceTargetTwoSpace_le_active_of_represented
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) :
    closedPlaceTargetTwoSpace place ≤ activeDisplacementTwoSpace Q := by
  rintro p ⟨z, rfl⟩
  have hr0 : targetTwo rZeroCoeff ∈ activeDisplacementTwoSpace Q := by
    simpa [closedPlaceDirections] using
      activeDisplacementTwoDirection_mem Q 0 (by
        simp [IsActiveDisplacementDirection])
  have hr1 : targetTwo rOneCoeff ∈ activeDisplacementTwoSpace Q := by
    simpa [closedPlaceDirections] using
      activeDisplacementTwoDirection_mem Q 1 (by
        simp [IsActiveDisplacementDirection])
  have hrInf : targetTwo rInfinityCoeff ∈
      activeDisplacementTwoSpace Q := by
    simpa [closedPlaceDirections] using
      activeDisplacementTwoDirection_mem Q 2 (by
        simp [IsActiveDisplacementDirection])
  fin_cases place
  · have hj : targetTwo jZeroCoeff ∈
        activeDisplacementTwoSpace Q := by
      simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 3 (by
          simpa [IsActiveDisplacementDirection] using hplace)
    simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      outsideHankelWord, rankTwoHankelWord, targetTwo] using
      Submodule.add_mem (activeDisplacementTwoSpace Q)
        (Submodule.smul_mem _ (z 0) hr0)
        (Submodule.smul_mem _ (z 1) hj)
  · have hj : targetTwo jOneCoeff ∈
        activeDisplacementTwoSpace Q := by
      simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 4 (by
          simpa [IsActiveDisplacementDirection] using hplace)
    have hout : targetTwo
        (rZeroCoeff + rOneCoeff + rInfinityCoeff + jOneCoeff) ∈
        activeDisplacementTwoSpace Q := by
      simpa [targetTwo] using
        Submodule.add_mem (activeDisplacementTwoSpace Q)
          (Submodule.add_mem _
            (Submodule.add_mem _ hr0 hr1) hrInf) hj
    simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      outsideHankelWord, rankTwoHankelWord, targetTwo] using
      Submodule.add_mem (activeDisplacementTwoSpace Q)
        (Submodule.smul_mem _ (z 0) hr1)
        (Submodule.smul_mem _ (z 1) hout)
  · have hj : targetTwo jInfinityCoeff ∈
        activeDisplacementTwoSpace Q := by
      simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 5 (by
          simpa [IsActiveDisplacementDirection] using hplace)
    have hout : targetTwo
        (rZeroCoeff + rOneCoeff + rInfinityCoeff + jInfinityCoeff) ∈
        activeDisplacementTwoSpace Q := by
      simpa [targetTwo] using
        Submodule.add_mem (activeDisplacementTwoSpace Q)
          (Submodule.add_mem _
            (Submodule.add_mem _ hr0 hr1) hrInf) hj
    simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      outsideHankelWord, rankTwoHankelWord, targetTwo] using
      Submodule.add_mem (activeDisplacementTwoSpace Q)
        (Submodule.smul_mem _ (z 0) hrInf)
        (Submodule.smul_mem _ (z 1) hout)
  · have hd0 : targetTwo dStarZeroCoeff ∈
        activeDisplacementTwoSpace Q := by
      simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 6 (by
          simpa [IsActiveDisplacementDirection] using hplace)
    have hd1 : targetTwo dStarOneCoeff ∈
        activeDisplacementTwoSpace Q := by
      simpa [closedPlaceDirections] using
        activeDisplacementTwoDirection_mem Q 7 (by
          simpa [IsActiveDisplacementDirection] using hplace)
    have hout0 : targetTwo
        (rZeroCoeff + rInfinityCoeff + dStarZeroCoeff + dStarOneCoeff) ∈
        activeDisplacementTwoSpace Q := by
      simpa [targetTwo] using
        Submodule.add_mem (activeDisplacementTwoSpace Q)
          (Submodule.add_mem _
            (Submodule.add_mem _ hr0 hrInf) hd0) hd1
    have hout1 : targetTwo
        (rZeroCoeff + rOneCoeff + dStarOneCoeff) ∈
        activeDisplacementTwoSpace Q := by
      simpa [targetTwo] using
        Submodule.add_mem (activeDisplacementTwoSpace Q)
          (Submodule.add_mem _ hr0 hr1) hd1
    simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
      outsideHankelWord, rankTwoHankelWord, targetTwo] using
      Submodule.add_mem (activeDisplacementTwoSpace Q)
        (Submodule.smul_mem _ (z 0) hout0)
        (Submodule.smul_mem _ (z 1) hout1)

theorem representedPlaceProfile_le_activeDisplacementTwoSpace
    (Q : Submodule F₂ QuadraticQuotient) :
    rationalTwoSpace ⊔ representedPlaceTargetSpace Q ≤
      activeDisplacementTwoSpace Q := by
  apply sup_le (rationalTwoSpace_le_activeDisplacementTwoSpace Q)
  apply iSup_le
  intro place
  apply iSup_le
  intro hplace
  exact closedPlaceTargetTwoSpace_le_active_of_represented Q place hplace

theorem closedPlaceTargetTwoSpace_le_representedPlaceProfile
    (Q : Submodule F₂ QuadraticQuotient) (place : Fin 4)
    (hplace : IsRepresentedPlace Q place) :
    closedPlaceTargetTwoSpace place ≤
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
  (((le_iSup
    (fun _h : IsRepresentedPlace Q place =>
      closedPlaceTargetTwoSpace place) hplace).trans
    (le_iSup
      (fun place : Fin 4 =>
        ⨆ _h : IsRepresentedPlace Q place,
          closedPlaceTargetTwoSpace place) place)).trans le_sup_right)

theorem activeDisplacementTwoDirection_mem_representedPlaceProfile
    (Q : Submodule F₂ QuadraticQuotient) (i : Fin 8)
    (hi : IsActiveDisplacementDirection Q i) :
    targetTwo (closedPlaceDirections i) ∈
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
  have hr0 : targetTwo rZeroCoeff ∈
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
    (le_sup_left : rationalTwoSpace ≤
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      ⟨rZeroCoeff, rZeroCoeff_mem_rationalCoeffSpace, rfl⟩
  have hr1 : targetTwo rOneCoeff ∈
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
    (le_sup_left : rationalTwoSpace ≤
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      ⟨rOneCoeff, rOneCoeff_mem_rationalCoeffSpace, rfl⟩
  have hrInf : targetTwo rInfinityCoeff ∈
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
    (le_sup_left : rationalTwoSpace ≤
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      ⟨rInfinityCoeff, rInfinityCoeff_mem_rationalCoeffSpace, rfl⟩
  fin_cases i
  · exact hr0
  · exact hr1
  · exact hrInf
  · have hplace : IsRepresentedPlace Q 0 := by
      simpa [IsActiveDisplacementDirection] using hi
    have hjet : closedPlaceTargetTwoLinear 0 localJetParam ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
      closedPlaceTargetTwoSpace_le_representedPlaceProfile Q 0 hplace
        ⟨localJetParam, rfl⟩
    simpa [closedPlaceDirections, closedPlaceTargetTwoLinear_apply,
      closedPlaceTargetCoeff, localJetParam, outsideHankelWord,
      rankTwoHankelWord, targetTwo] using hjet
  · have hplace : IsRepresentedPlace Q 1 := by
      simpa [IsActiveDisplacementDirection] using hi
    have hout : closedPlaceTargetTwoLinear 1 localJetParam ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
      closedPlaceTargetTwoSpace_le_representedPlaceProfile Q 1 hplace
        ⟨localJetParam, rfl⟩
    have hout' : targetTwo
        (rZeroCoeff + rOneCoeff + rInfinityCoeff + jOneCoeff) ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
      simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
        localJetParam, outsideHankelWord, rankTwoHankelWord] using hout
    have hsum := Submodule.add_mem
      (rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      (Submodule.add_mem _ (Submodule.add_mem _ hout' hr0) hr1) hrInf
    have hcoeff : jOneCoeff =
        (rZeroCoeff + rOneCoeff + rInfinityCoeff + jOneCoeff) +
          rZeroCoeff + rOneCoeff + rInfinityCoeff := by
      funext k
      fin_cases k <;> decide
    change targetTwo jOneCoeff ∈ _
    rw [hcoeff]
    simpa [targetTwo] using hsum
  · have hplace : IsRepresentedPlace Q 2 := by
      simpa [IsActiveDisplacementDirection] using hi
    have hout : closedPlaceTargetTwoLinear 2 localJetParam ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
      closedPlaceTargetTwoSpace_le_representedPlaceProfile Q 2 hplace
        ⟨localJetParam, rfl⟩
    have hout' : targetTwo
        (rZeroCoeff + rOneCoeff + rInfinityCoeff + jInfinityCoeff) ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
      simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
        localJetParam, outsideHankelWord, rankTwoHankelWord] using hout
    have hsum := Submodule.add_mem
      (rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      (Submodule.add_mem _ (Submodule.add_mem _ hout' hr0) hr1) hrInf
    have hcoeff : jInfinityCoeff =
        (rZeroCoeff + rOneCoeff + rInfinityCoeff + jInfinityCoeff) +
          rZeroCoeff + rOneCoeff + rInfinityCoeff := by
      funext k
      fin_cases k <;> decide
    change targetTwo jInfinityCoeff ∈ _
    rw [hcoeff]
    simpa [targetTwo] using hsum
  · have hplace : IsRepresentedPlace Q 3 := by
      simpa [IsActiveDisplacementDirection] using hi
    have hout0 : closedPlaceTargetTwoLinear 3 localEvaluationParam ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
      closedPlaceTargetTwoSpace_le_representedPlaceProfile Q 3 hplace
        ⟨localEvaluationParam, rfl⟩
    have hout1 : closedPlaceTargetTwoLinear 3 localJetParam ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
      closedPlaceTargetTwoSpace_le_representedPlaceProfile Q 3 hplace
        ⟨localJetParam, rfl⟩
    have hout0' : targetTwo
        (rZeroCoeff + rInfinityCoeff + dStarZeroCoeff + dStarOneCoeff) ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
      simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
        localEvaluationParam, outsideHankelWord, rankTwoHankelWord] using hout0
    have hout1' : targetTwo
        (rZeroCoeff + rOneCoeff + dStarOneCoeff) ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
      simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
        localJetParam, outsideHankelWord, rankTwoHankelWord] using hout1
    have hsum := Submodule.add_mem
      (rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      (Submodule.add_mem _ (Submodule.add_mem _ hout0' hout1') hr1) hrInf
    have hcoeff : dStarZeroCoeff =
        (rZeroCoeff + rInfinityCoeff + dStarZeroCoeff + dStarOneCoeff) +
          (rZeroCoeff + rOneCoeff + dStarOneCoeff) +
            rOneCoeff + rInfinityCoeff := by
      funext k
      fin_cases k <;> decide
    change targetTwo dStarZeroCoeff ∈ _
    rw [hcoeff]
    simpa [targetTwo] using hsum
  · have hplace : IsRepresentedPlace Q 3 := by
      simpa [IsActiveDisplacementDirection] using hi
    have hout : closedPlaceTargetTwoLinear 3 localJetParam ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q :=
      closedPlaceTargetTwoSpace_le_representedPlaceProfile Q 3 hplace
        ⟨localJetParam, rfl⟩
    have hout' : targetTwo
        (rZeroCoeff + rOneCoeff + dStarOneCoeff) ∈
        rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
      simpa [closedPlaceTargetTwoLinear_apply, closedPlaceTargetCoeff,
        localJetParam, outsideHankelWord, rankTwoHankelWord] using hout
    have hsum := Submodule.add_mem
      (rationalTwoSpace ⊔ representedPlaceTargetSpace Q)
      (Submodule.add_mem _ hout' hr0) hr1
    have hcoeff : dStarOneCoeff =
        (rZeroCoeff + rOneCoeff + dStarOneCoeff) +
          rZeroCoeff + rOneCoeff := by
      funext k
      fin_cases k <;> decide
    change targetTwo dStarOneCoeff ∈ _
    rw [hcoeff]
    simpa [targetTwo] using hsum

theorem activeDisplacementTwoSpace_le_representedPlaceProfile
    (Q : Submodule F₂ QuadraticQuotient) :
    activeDisplacementTwoSpace Q ≤
      rationalTwoSpace ⊔ representedPlaceTargetSpace Q := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  exact activeDisplacementTwoDirection_mem_representedPlaceProfile
    Q i.1 i.2

/-- The intrinsic displacement space is precisely the span of the active
subfamily of the eight independent closed-place directions. -/
theorem localDisplacementSpace_eq_activeDisplacementTwoSpace
    (Q : Submodule F₂ QuadraticQuotient) :
    localDisplacementSpace Q = activeDisplacementTwoSpace Q := by
  rw [localDisplacementSpace_eq_representedPlaceProfile]
  exact le_antisymm
    (representedPlaceProfile_le_activeDisplacementTwoSpace Q)
    (activeDisplacementTwoSpace_le_representedPlaceProfile Q)

/-- Exact numerical form of the represented-place profile:
`3 + (# represented rational places) + 2 * [degree-two represented]`. -/
theorem localDisplacement_finrank_eq_representedPlaceWeight
    (Q : Submodule F₂ QuadraticQuotient) :
    Module.finrank F₂ (localDisplacementSpace Q) =
      3 + representedPlaceWeight Q := by
  rw [localDisplacementSpace_eq_activeDisplacementTwoSpace,
    activeDisplacementTwoSpace_finrank,
    activeDisplacementDirection_card]

/-- The manuscript displacement parameter is precisely the weighted count
of represented closed places. -/
theorem displacementRank_eq_representedPlaceWeight
    (Q : Submodule F₂ QuadraticQuotient) :
    displacementRank Q = representedPlaceWeight Q := by
  unfold displacementRank
  rw [localDisplacement_finrank_eq_representedPlaceWeight]
  omega

/-- Capacity ledger with the geometric displacement term evaluated. -/
theorem targetCapacity_eq_three_add_representedPlaceWeight_add_gifts
    (Q : Submodule F₂ QuadraticQuotient) :
    targetCapacity Q =
      3 + representedPlaceWeight Q + relationGiftRank Q := by
  rw [targetCapacity_eq_three_add_displacement_add_gifts,
    displacementRank_eq_representedPlaceWeight]

end

end N5
end UnrestrictedBooleanMul
