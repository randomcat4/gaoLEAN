import GaoLean.PGGeneralWeightedStrongRecursionState

/-!
# Strong-recursion quotient block assembly

This module is deliberately downstream from both the Step 1 enlargement
certificate and the strong recursive state.  It connects the genuinely local
zero reserve in the old `H`-coset to the quotient affine pool outside that
coset.  No provider or conditional engine is introduced.
-/

namespace GaoLean

universe u

variable {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]

namespace GeneralWeightedStrongRecursionState

variable {W : Set ℤ} {G : AddSubgroup G₀} {gamma delta : G₀}
  {xs : List G₀} {n D : ℕ}

/-- Every retained label of a strong state lies in its complete old affine
container.  This is the geometric half of the later pool--reserve
disjointness proof. -/
theorem retained_subset_weightedStep1AffineContainer
    (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    S.retained ⊆
      weightedStep1AffineContainer S.H W xs S.beta := by
  intro i hi
  exact (mem_weightedStep1AffineContainer_iff_sourceCoset
    S.H W hprimitive S.alpha S.beta S.alpha_weightCoset xs i).2
      (S.retained_sourceCoset i hi)

/-- The quotient pool returned by strict Step 1 enlargement is outside the
old affine container, whereas the recursive Davenport reserve stays inside
it.  Hence the two literal occurrence sets are disjoint. -/
theorem enlargementCore_disjoint_extractDavenportReserve
    (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta)
    (DJ : ℕ) (hDJle : DJ ≤ S.DQ) :
    Disjoint C.core (S.extractDavenportReserve DJ hDJle).reserve := by
  have hpoolOutside : C.core ⊆
      weightedStep1OutsideAffineContainer S.H W xs S.beta :=
    C.core_subset_retained.trans C.retained_subset_outside
  have hreserveInside : (S.extractDavenportReserve DJ hDJle).reserve ⊆
      weightedStep1AffineContainer S.H W xs S.beta :=
    (S.extractDavenportReserve DJ hDJle).reserve_subset_retained.trans
      (S.retained_subset_weightedStep1AffineContainer hprimitive)
  exact (disjoint_weightedStep1AffineContainer_outside
    S.H W xs S.beta).symm.mono hpoolOutside hreserveInside

/-- A quotient affine-sumset member from the enlargement certificate is
realized by an exact-cardinality source block, using only the old recursive
state's honest centred reserve.  The output preserves literal occurrence
labels and exposes its complete support union. -/
theorem exists_fixedCard_quotientBlock_of_enlargement
    (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta)
    (DJ : ℕ) (hDJ : IsWeightedDavenportConstant W C.J DJ)
    (hDJle : DJ ≤ S.DQ)
    (y : G₀ ⧸ S.H)
    (hy : y ∈ weightedStep1QuotientAffineSumset
      S.H W xs S.beta C.core) :
    ∃ a : G₀, QuotientAddGroup.mk' S.H a = y ∧
      ∃ z : HasWeightedSumOfCard W xs C.core.card
          (C.core.card • S.beta + a),
        z.selected ⊆ C.core ∪
          (S.extractDavenportReserve DJ hDJle).reserve := by
  let R := S.extractDavenportReserve DJ hDJle
  have hpool : ∀ i ∈ C.core,
      QuotientAddGroup.mk' S.H (occurrenceValue xs i - S.alpha) ∈ C.J := by
    intro i hi
    exact (mem_liftedAddSubgroup_iff S.H C.J
      (occurrenceValue xs i - S.alpha)).1
        (C.retained_sourceCoset i (C.core_subset_retained hi))
  have hreserve : ∀ i ∈ R.reserve,
      occurrenceValue xs i - S.alpha ∈ S.H := by
    intro i hi
    exact S.extractDavenportReserve_sourceCoset DJ hDJle i hi
  have hdis : Disjoint C.core R.reserve := by
    exact S.enlargementCore_disjoint_extractDavenportReserve
      hprimitive C DJ hDJle
  have hreserveCard : DJ - 1 ≤ R.reserve.card := by
    rw [R.reserve_card]
  exact exists_weightedFixedCardSelection_of_mem_weightedStep1QuotientAffineSumset
    (W := W) xs S.H C.J S.alpha S.beta S.alpha_weightCoset
      C.core R.reserve hpool hreserve hdis DJ hDJ hreserveCard y hy

end GeneralWeightedStrongRecursionState

end GaoLean

#print axioms GaoLean.GeneralWeightedStrongRecursionState.retained_subset_weightedStep1AffineContainer
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargementCore_disjoint_extractDavenportReserve
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_fixedCard_quotientBlock_of_enlargement
