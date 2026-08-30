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

/-- The complete quotient pool is disjoint from every retained label of the
old strong state, not only from a particular extracted reserve. -/
theorem enlargementCore_disjoint_retained
    (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta) :
    Disjoint C.core S.retained := by
  have hpoolOutside : C.core ⊆
      weightedStep1OutsideAffineContainer S.H W xs S.beta :=
    C.core_subset_retained.trans C.retained_subset_outside
  have hretainedInside : S.retained ⊆
      weightedStep1AffineContainer S.H W xs S.beta :=
    S.retained_subset_weightedStep1AffineContainer hprimitive
  exact (disjoint_weightedStep1AffineContainer_outside
    S.H W xs S.beta).symm.mono hpoolOutside hretainedInside

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

/-- The literal carrier ledger for the lifted parent core.  It chooses a
fixed filler outside the old core, local reserve, and quotient pool, then
extends their union to an exact critical-size core inside the complete lifted
affine container.  This theorem constructs only the carrier; the following
block-expansion step supplies its operational full-spectrum witnesses. -/
theorem exists_liftedCoreCarrier
    (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta)
    (DJ : ℕ) (hDJ : IsWeightedDavenportConstant W C.J DJ)
    (hDJle : DJ ≤ S.DQ)
    (DK : ℕ)
    (hDK : IsWeightedDavenportConstant W
      (liftedAddSubgroup S.H C.J) DK)
    (hcontainerLower :
      Nat.card (liftedAddSubgroup S.H C.J) + DK - 1 ≤
        (weightedStep1AffineContainer
          (liftedAddSubgroup S.H C.J) W xs S.beta).card) :
    ∃ filler parentCore : Selection xs,
      Disjoint
        ((S.core ∪ (S.extractDavenportReserve DJ hDJle).reserve) ∪ C.core)
        filler ∧
      filler.card =
        Nat.card (liftedAddSubgroup S.H C.J) -
          (Nat.card S.H + Nat.card C.J - 1) ∧
      ((S.core ∪ (S.extractDavenportReserve DJ hDJle).reserve) ∪ C.core) ∪
          filler ⊆ parentCore ∧
      parentCore ⊆ weightedStep1AffineContainer
        (liftedAddSubgroup S.H C.J) W xs S.beta ∧
      parentCore.card =
        Nat.card (liftedAddSubgroup S.H C.J) + DK - 1 := by
  classical
  let R := S.extractDavenportReserve DJ hDJle
  let K := liftedAddSubgroup S.H C.J
  let container := weightedStep1AffineContainer K W xs S.beta
  let pre : Selection xs := (S.core ∪ R.reserve) ∪ C.core
  let fillerCard := Nat.card K - (Nat.card S.H + Nat.card C.J - 1)
  have hcoreReserve : Disjoint S.core R.reserve := R.disjoint_core_reserve
  have hOldUnionSubset : S.core ∪ R.reserve ⊆ S.retained :=
    Finset.union_subset S.core_subset_retained R.reserve_subset_retained
  have hOldUnionPool : Disjoint (S.core ∪ R.reserve) C.core :=
    (S.enlargementCore_disjoint_retained hprimitive C).symm.mono
      hOldUnionSubset (fun _ hi ↦ hi)
  have hpreCard : pre.card =
      (Nat.card S.H + S.DH - 1) + (DJ - 1) + (Nat.card C.J - 1) := by
    dsimp only [pre]
    rw [Finset.card_union_of_disjoint hOldUnionPool,
      Finset.card_union_of_disjoint hcoreReserve,
      S.core_card, R.reserve_card, C.core_card]
  have hretainedBase : S.retained ⊆
      weightedStep1AffineContainer S.H W xs S.beta :=
    S.retained_subset_weightedStep1AffineContainer hprimitive
  have hretainedEnlarged : S.retained ⊆ C.enlarged := by
    rw [C.enlarged_eq]
    exact hretainedBase.trans Finset.subset_union_left
  have hCcoreEnlarged : C.core ⊆ C.enlarged := by
    rw [C.enlarged_eq]
    exact C.core_subset_retained.trans Finset.subset_union_right
  have hpreEnlarged : pre ⊆ C.enlarged := by
    dsimp only [pre]
    exact Finset.union_subset
      (hOldUnionSubset.trans hretainedEnlarged) hCcoreEnlarged
  have hpreContainer : pre ⊆ container := by
    exact hpreEnlarged.trans C.enlarged_subset_lifted_container
  have hcapacity := weighted_liftedCore_pool_reserve_filler_capacity
    S.H C.J S.DH DJ DK S.DH_exact hDJ hDK
  have hpreAddFiller : pre.card + fillerCard ≤ Nat.card K + DK - 1 := by
    rw [hpreCard]
    simpa [K, fillerCard, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hcapacity
  have hbudget : pre.card + fillerCard ≤ container.card :=
    hpreAddFiller.trans hcontainerLower
  let F := extractOccurrenceReserveOfCoreCardAddLe
    container pre fillerCard hbudget
  have hessentialContainer : pre ∪ F.reserve ⊆ container :=
    F.core_union_reserve_subset hpreContainer
  have hessentialCard : (pre ∪ F.reserve).card = pre.card + fillerCard :=
    F.card_core_union_reserve
  have hessentialTarget : (pre ∪ F.reserve).card ≤ Nat.card K + DK - 1 := by
    rw [hessentialCard]
    exact hpreAddFiller
  obtain ⟨parentCore, hessentialCore, hcoreContainer, hcoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hessentialContainer
      hessentialTarget hcontainerLower
  refine ⟨F.reserve, parentCore, ?_, F.reserve_card, ?_, hcoreContainer, hcoreCard⟩
  · exact F.disjoint_core_reserve
  · exact hessentialCore

end GeneralWeightedStrongRecursionState

end GaoLean

#print axioms GaoLean.GeneralWeightedStrongRecursionState.retained_subset_weightedStep1AffineContainer
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargementCore_disjoint_extractDavenportReserve
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargementCore_disjoint_retained
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_fixedCard_quotientBlock_of_enlargement
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_liftedCoreCarrier
