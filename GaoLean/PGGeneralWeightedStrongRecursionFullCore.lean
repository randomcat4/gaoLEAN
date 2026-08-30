import GaoLean.PGGeneralWeightedOvergroupQuotient

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

/-- The incoming overgroup equation and a recursive state's output centre
put every weighted source value in the parent `G`-coset centred at `S.beta`.
This applies to all labelled source occurrences, not only those retained by
the old state. -/
theorem weighted_sub_beta_mem_overgroup
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (input : GeneralWeightedOvergroupInput W G gamma delta xs)
    (i : Occurrence xs) (w : ℤ) (hw : w ∈ W) :
    w • occurrenceValue xs i - S.beta ∈ G := by
  rw [show w • occurrenceValue xs i - S.beta =
      (w • occurrenceValue xs i - delta) -
        (S.beta - delta) by abel]
  exact G.sub_mem (input.weighted_mem i w hw) S.beta_sub_delta_mem

/-- The quotient subgroup produced by a Step 1 enlargement is contained in
the image of the recursive overgroup.  The proof uses the certificate's
literal quotient-sumset equality: every member is represented by a genuine
weighted source selection whose centred correction lies in `G`. -/
theorem enlargement_quotientSubgroup_le_overgroupQuotient
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (input : GeneralWeightedOvergroupInput W G gamma delta xs)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta) :
    C.J ≤ generalWeightedQuotientSubgroup S.H G := by
  classical
  intro y hyJ
  have hySum : y ∈ weightedStep1QuotientAffineSumset
      S.H W xs S.beta C.core := by
    rw [C.core_quotient_sumset]
    exact (mem_weightedStep1SubgroupFinset C.J y).2 hyJ
  obtain ⟨k, _hk, a, ha, z, _hz⟩ :=
    exists_weightedSelection_of_mem_weightedStep1QuotientAffineSumset
      W xs S.H S.beta y C.core hySum
  have hsum :
      (∑ i ∈ z.selected,
        (z.weights i • occurrenceValue xs i - S.beta)) ∈ G := by
    apply G.sum_mem
    intro i hi
    exact S.weighted_sub_beta_mem_overgroup input i (z.weights i)
      (z.weights_mem i hi)
  have hsum' :
      (∑ i ∈ z.selected, z.weights i • occurrenceValue xs i) -
          z.selected.card • S.beta ∈ G := by
    simpa [Finset.sum_sub_distrib] using hsum
  have haEq :
      (∑ i ∈ z.selected, z.weights i • occurrenceValue xs i) -
          z.selected.card • S.beta = a := by
    rw [z.weighted_sum, z.card_selected]
    abel
  rw [haEq] at hsum'
  apply (mk_mem_generalWeightedQuotientSubgroup_iff S.H_le_G a).2 at hsum'
  rw [ha] at hsum'
  exact hsum'

/-- Consequently, the lifted subgroup itself remains inside the recursive
overgroup.  This is a geometric bridge only; it does not change the ambient
quotient cardinality stored by the present Step 1 certificate. -/
theorem enlargement_liftedAddSubgroup_le_overgroup
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (input : GeneralWeightedOvergroupInput W G gamma delta xs)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta) :
    liftedAddSubgroup S.H C.J ≤ G := by
  intro x hx
  apply (mk_mem_generalWeightedQuotientSubgroup_iff S.H_le_G x).1
  exact S.enlargement_quotientSubgroup_le_overgroupQuotient input C
    ((mem_liftedAddSubgroup_iff S.H C.J x).1 hx)

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

/-- Operational expansion of a lifted carrier.  For every element of the
lifted subgroup it combines one old `H`-full block, one exact quotient block,
and the same fixed filler.  All three pieces are literal disjoint occurrence
selections, and their weighted sum is exactly `|lift(H,J)| beta + k`. -/
theorem liftedCore_full_of_carrier
    (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta)
    (DJ : ℕ) (hDJ : IsWeightedDavenportConstant W C.J DJ)
    (hDJle : DJ ≤ S.DQ)
    (filler parentCore : Selection xs)
    (hFdis : Disjoint
      ((S.core ∪ (S.extractDavenportReserve DJ hDJle).reserve) ∪ C.core)
      filler)
    (hFcard : filler.card =
      Nat.card (liftedAddSubgroup S.H C.J) -
        (Nat.card S.H + Nat.card C.J - 1))
    (hpreFsub :
      ((S.core ∪ (S.extractDavenportReserve DJ hDJle).reserve) ∪ C.core) ∪
        filler ⊆ parentCore)
    (hparentContainer : parentCore ⊆ weightedStep1AffineContainer
      (liftedAddSubgroup S.H C.J) W xs S.beta) :
    ∀ k : liftedAddSubgroup S.H C.J,
      ∃ z : HasWeightedSumOfCard W xs
          (Nat.card (liftedAddSubgroup S.H C.J))
          (Nat.card (liftedAddSubgroup S.H C.J) • S.beta + (k : G₀)),
        z.selected ⊆ parentCore := by
  classical
  obtain ⟨w₀, hw₀⟩ := hW
  let R := S.extractDavenportReserve DJ hDJle
  let K := liftedAddSubgroup S.H C.J
  let fillerSum : G₀ :=
    ∑ i ∈ filler, w₀ • occurrenceValue xs i
  let fillerWitness : HasWeightedSumOfCard W xs filler.card fillerSum := {
    selected := filler
    weights := fun _ ↦ w₀
    weights_mem := fun _ _ ↦ hw₀
    card_selected := rfl
    weighted_sum := rfl
  }
  have hFdisp : fillerSum - filler.card • S.beta ∈ K := by
    rw [show fillerSum - filler.card • S.beta =
        ∑ i ∈ filler, (w₀ • occurrenceValue xs i - S.beta) by
      simp [fillerSum, Finset.sum_sub_distrib]]
    apply K.sum_mem
    intro i hi
    apply C.lifted_container_weightCoset i
    · apply hparentContainer
      apply hpreFsub
      exact Finset.mem_union_right _ hi
    · exact hw₀
  intro k
  let y : G₀ ⧸ S.H := QuotientAddGroup.mk' S.H
    ((k : G₀) - (fillerSum - filler.card • S.beta))
  have hyJ : y ∈ weightedStep1SubgroupFinset C.J := by
    apply (mem_weightedStep1SubgroupFinset C.J y).2
    exact (mem_liftedAddSubgroup_iff S.H C.J _).1
      (K.sub_mem k.property hFdisp)
  have hySum : y ∈ weightedStep1QuotientAffineSumset
      S.H W xs S.beta C.core := by
    rw [C.core_quotient_sumset]
    exact hyJ
  obtain ⟨a, ha, block, hblockSub⟩ :=
    S.exists_fixedCard_quotientBlock_of_enlargement
      hprimitive C DJ hDJ hDJle y hySum
  let residual : G₀ :=
    (k : G₀) - (fillerSum - filler.card • S.beta) - a
  have hresidual : residual ∈ S.H := by
    have haMem := QuotientAddGroup.eq_iff_sub_mem.mp ha
    have hneg := S.H.neg_mem haMem
    dsimp only [residual, y] at hneg ⊢
    convert hneg using 1 <;> abel
  obtain ⟨old, holdSub⟩ := S.core_full ⟨residual, hresidual⟩
  have holdBlock : Disjoint old.selected block.selected := by
    rw [Finset.disjoint_left]
    intro i hiOld hiBlock
    have hiCore := holdSub hiOld
    rcases Finset.mem_union.mp (hblockSub hiBlock) with hiPool | hiReserve
    · exact (Finset.disjoint_left.mp
        (S.enlargementCore_disjoint_retained hprimitive C).symm)
          (S.core_subset_retained hiCore) hiPool
    · exact (Finset.disjoint_left.mp R.disjoint_core_reserve) hiCore hiReserve
  have hblockPre : block.selected ⊆
      (S.core ∪ R.reserve) ∪ C.core := by
    intro i hi
    rcases Finset.mem_union.mp (hblockSub hi) with hiPool | hiReserve
    · exact Finset.mem_union_right _ hiPool
    · exact Finset.mem_union_left C.core
        (Finset.mem_union_right S.core hiReserve)
  have holdBlockPre : old.selected ∪ block.selected ⊆
      (S.core ∪ R.reserve) ∪ C.core := by
    exact Finset.union_subset
      (holdSub.trans (Finset.subset_union_left.trans Finset.subset_union_left))
      hblockPre
  have holdBlockFiller : Disjoint (old.selected ∪ block.selected) filler :=
    hFdis.mono_left holdBlockPre
  let oldBlock := old.disjointUnion block holdBlock
  let all := oldBlock.disjointUnion fillerWitness holdBlockFiller
  have hbase : Nat.card S.H + Nat.card C.J - 1 ≤ Nat.card K := by
    dsimp only [K]
    rw [natCard_liftedAddSubgroup S.H C.J]
    exact generalWeighted_add_sub_one_le_mul_of_pos
      (Nat.card S.H) (Nat.card C.J) Nat.card_pos Nat.card_pos
  have htotalCard : Nat.card S.H + C.core.card + filler.card = Nat.card K := by
    rw [C.core_card, hFcard]
    have hJcardPos : 1 ≤ Nat.card C.J := Nat.card_pos
    have hbaseEq : Nat.card S.H + (Nat.card C.J - 1) =
        Nat.card S.H + Nat.card C.J - 1 := by omega
    rw [hbaseEq]
    exact Nat.add_sub_of_le hbase
  have htarget :
      ((Nat.card S.H • S.beta + residual) +
          (C.core.card • S.beta + a)) + fillerSum =
        Nat.card K • S.beta + (k : G₀) := by
    dsimp only [residual]
    rw [← htotalCard, add_nsmul, add_nsmul]
    abel
  let final : HasWeightedSumOfCard W xs (Nat.card K)
      (Nat.card K • S.beta + (k : G₀)) := {
    selected := all.selected
    weights := all.weights
    weights_mem := all.weights_mem
    card_selected := all.card_selected.trans htotalCard
    weighted_sum := all.weighted_sum.trans htarget
  }
  refine ⟨final, ?_⟩
  intro i hi
  apply hpreFsub
  change i ∈ (old.selected ∪ block.selected) ∪ filler at hi
  rcases Finset.mem_union.mp hi with hiOldBlock | hiFiller
  · exact Finset.mem_union_left filler (holdBlockPre hiOldBlock)
  · exact Finset.mem_union_right _ hiFiller

/-- A complete lifted core, packaged independently of the auxiliary filler.
The theorem first constructs an exact critical-size carrier in the lifted
affine container and then equips it with the operational full-spectrum
witnesses from `liftedCore_full_of_carrier`. -/
theorem exists_liftedFullCore_of_enlargement
    (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
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
    ∃ parentCore : Selection xs,
      parentCore ⊆ weightedStep1AffineContainer
        (liftedAddSubgroup S.H C.J) W xs S.beta ∧
      parentCore.card =
        Nat.card (liftedAddSubgroup S.H C.J) + DK - 1 ∧
      ∀ k : liftedAddSubgroup S.H C.J,
        ∃ z : HasWeightedSumOfCard W xs
            (Nat.card (liftedAddSubgroup S.H C.J))
            (Nat.card (liftedAddSubgroup S.H C.J) • S.beta + (k : G₀)),
          z.selected ⊆ parentCore := by
  obtain ⟨filler, parentCore, hFdis, hFcard, hpreFsub,
      hparentContainer, hparentCard⟩ :=
    S.exists_liftedCoreCarrier hprimitive C DJ hDJ hDJle DK hDK
      hcontainerLower
  refine ⟨parentCore, hparentContainer, hparentCard, ?_⟩
  exact S.liftedCore_full_of_carrier hW hprimitive C DJ hDJ hDJle
    filler parentCore hFdis hFcard hpreFsub hparentContainer

/-- Overgroup-aware packaging of the lifted full core.  The quotient
Davenport compatibility and containment of the lifted subgroup in `G` are
derived from the incoming equation-(3) overgroup data, rather than accepted
as separate hypotheses.  The affine-container lower bound remains explicit
until Step 1 records its internal-overgroup cardinal estimate. -/
theorem exists_liftedFullCore_of_enlargement_overgroup
    (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (input : GeneralWeightedOvergroupInput W G gamma delta xs)
    (C : GeneralWeightedStep1EnlargementCertificate
      W xs S.H S.alpha S.beta)
    (DJ : ℕ) (hDJ : IsWeightedDavenportConstant W C.J DJ)
    (DK : ℕ)
    (hDK : IsWeightedDavenportConstant W
      (liftedAddSubgroup S.H C.J) DK)
    (hcontainerLower :
      Nat.card (liftedAddSubgroup S.H C.J) + DK - 1 ≤
        (weightedStep1AffineContainer
          (liftedAddSubgroup S.H C.J) W xs S.beta).card) :
    liftedAddSubgroup S.H C.J ≤ G ∧
      ∃ parentCore : Selection xs,
        parentCore ⊆ weightedStep1AffineContainer
          (liftedAddSubgroup S.H C.J) W xs S.beta ∧
        parentCore.card =
          Nat.card (liftedAddSubgroup S.H C.J) + DK - 1 ∧
        ∀ k : liftedAddSubgroup S.H C.J,
          ∃ z : HasWeightedSumOfCard W xs
              (Nat.card (liftedAddSubgroup S.H C.J))
              (Nat.card (liftedAddSubgroup S.H C.J) • S.beta + (k : G₀)),
            z.selected ⊆ parentCore := by
  have hJle : C.J ≤ generalWeightedQuotientSubgroup S.H G :=
    S.enlargement_quotientSubgroup_le_overgroupQuotient input C
  have hDJle : DJ ≤ S.DQ :=
    weightedDavenportConstant_le_overgroupQuotient
      S.H G S.H_le_G C.J hJle DJ S.DQ hDJ S.DQ_exact
  exact ⟨S.enlargement_liftedAddSubgroup_le_overgroup input C,
    S.exists_liftedFullCore_of_enlargement hW hprimitive C DJ hDJ hDJle
      DK hDK hcontainerLower⟩

end GeneralWeightedStrongRecursionState

end GaoLean

#print axioms GaoLean.GeneralWeightedStrongRecursionState.retained_subset_weightedStep1AffineContainer
#print axioms GaoLean.GeneralWeightedStrongRecursionState.weighted_sub_beta_mem_overgroup
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargement_quotientSubgroup_le_overgroupQuotient
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargement_liftedAddSubgroup_le_overgroup
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargementCore_disjoint_extractDavenportReserve
#print axioms GaoLean.GeneralWeightedStrongRecursionState.enlargementCore_disjoint_retained
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_fixedCard_quotientBlock_of_enlargement
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_liftedCoreCarrier
#print axioms GaoLean.GeneralWeightedStrongRecursionState.liftedCore_full_of_carrier
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_liftedFullCore_of_enlargement
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_liftedFullCore_of_enlargement_overgroup
