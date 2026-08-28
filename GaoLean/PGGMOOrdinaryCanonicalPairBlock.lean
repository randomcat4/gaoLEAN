import GaoLean.PGGMOOrdinaryCanonicalCounting
import GaoLean.PGGMOOrdinaryPairPadding
import GaoLean.PGGMOOrdinaryPairSubgroupInduction

/-!
# Canonical Step 1 enlargement from a supplied pair certificate

This module performs only the final labelled assembly.  Starting with a
canonical Step 1 core `C` and an explicit honest pair-subgroup certificate
for its outside quotient values, it constructs the strictly larger lifted
canonical core.  The pair certificate remains explicit input data throughout.

The proof keeps four literal source pieces separate: the old core, a zero
reserve in the old affine container, the retained outside pair core, and a
fixed filler.  Pair padding is run in the value group `P.J`; consequently
the resulting source pair block always has exactly `|P.J|-1` occurrences.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance canonicalPairBlockDecidableEq {X : Type*} :
    DecidableEq X := Classical.decEq X
noncomputable local instance canonicalPairBlockQuotientFintype
    (H : AddSubgroup A) : Fintype (A ⧸ H) :=
  Fintype.ofFinite (A ⧸ H)

namespace CanonicalOrdinaryGMOStep1Core

/-! ## The old-coset zero reserve -/

/-- The unused part of the old canonical container contains the `d*(J)`
zero-valued labels needed to turn a pair-subset witness into an exact
`|J|-1` source block. -/
theorem exists_pairZeroReserve
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue) :
    ∃ Z : Selection xs,
      Z ⊆ C.container \ C.core ∧
        Z.card = pGroupDStar P.J := by
  classical
  let available : Selection xs := C.container \ C.core
  have hcoreCardLe : C.core.card ≤ C.container.card :=
    Finset.card_le_card C.core_subset_container
  have havailableCard : available.card =
      C.container.card - C.core.card := by
    dsimp only [available]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr C.core_subset_container]
  have hJbudget : pGroupDStar P.J ≤ pGroupDStar (A ⧸ C.H) := by
    have hconv := pGroupDStar_subgroup_quotient_le P.J
    omega
  have hambientConv := pGroupDStar_subgroup_quotient_le C.H
  have havailable : pGroupDStar P.J ≤ available.card := by
    rw [havailableCard, C.core_card]
    have hlower := C.container_card_lower
    omega
  obtain ⟨Z, hZsub, hZcard⟩ :=
    Finset.exists_subset_card_eq (s := available) havailable
  exact ⟨Z, hZsub, hZcard⟩

/-! ## Exact source pair blocks -/

/-- A pair label or an old-coset zero-reserve label, kept in a disjoint sum
so no repeated source value can collapse the occurrence ledger. -/
private abbrev PairPaddingIndex
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (Z : Selection xs) := (↑P.core) ⊕ (↑Z)

/-- Values for pair padding live in the actual quotient subgroup `P.J`.
Left labels carry their centered outside value; right labels are the honest
zero choices supplied by the old affine container. -/
private noncomputable def pairPaddingValue
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (Z : Selection xs) : PairPaddingIndex C P Z → P.J
  | Sum.inl i =>
      ⟨C.outsideQuotientValue i.1, P.core_value_mem i.1 i.2⟩
  | Sum.inr _ => 0

private noncomputable def pairPaddingPool
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (Z : Selection xs) : Finset (PairPaddingIndex C P Z) :=
  (Finset.univ : Finset (↑P.core)).map Function.Embedding.inl

private noncomputable def pairPaddingReserve
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (Z : Selection xs) : Finset (PairPaddingIndex C P Z) :=
  (Finset.univ : Finset (↑Z)).map Function.Embedding.inr

/-- Map the disjoint-sum padding ledger back to literal source occurrences.
Injectivity across the two summands follows because every pair label is
outside `C.container`, whereas every reserve label lies inside it. -/
private noncomputable def pairPaddingSourceEmbedding
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (Z : Selection xs) (hZ : Z ⊆ C.container \ C.core) :
    PairPaddingIndex C P Z ↪ Occurrence xs where
  toFun
    | Sum.inl i => i.1.1
    | Sum.inr i => i.1
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            congr 1
            apply Subtype.ext
            apply Subtype.ext
            exact hab
        | inr b =>
            exfalso
            have haOutside := (Finset.mem_sdiff.mp a.1.2).2
            have hbContainer := (Finset.mem_sdiff.mp (hZ b.2)).1
            change a.1.1 = b.1 at hab
            apply haOutside
            rw [hab]
            exact hbContainer
    | inr a =>
        cases b with
        | inl b =>
            exfalso
            have haContainer := (Finset.mem_sdiff.mp (hZ a.2)).1
            have hbOutside := (Finset.mem_sdiff.mp b.1.2).2
            change a.1 = b.1.1 at hab
            apply hbOutside
            rw [← hab]
            exact haContainer
        | inr b =>
            congr 1
            apply Subtype.ext
            exact hab

/-- Pair padding in `P.J`, transported back through the literal disjoint
source embedding.  The result has exact cardinality `|J|-1`; its centered
quotient sum is the prescribed element of `J`. -/
theorem exists_exact_source_pairBlock
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (Z : Selection xs) (hZ : Z ⊆ C.container \ C.core)
    (hZcard : Z.card = pGroupDStar P.J) (y : P.J) :
    ∃ B : Selection xs,
      B ⊆ C.mapOutsideSelection P.core ∪ Z ∧
      B.card = Nat.card P.J - 1 ∧
      QuotientAddGroup.mk' C.H
          ((∑ i ∈ B, occurrenceValue xs i) - B.card • C.beta) = y.1 := by
  classical
  let X := PairPaddingIndex C P Z
  let pool : Finset X := pairPaddingPool C P Z
  let reserve : Finset X := pairPaddingReserve C P Z
  let f : X → P.J := pairPaddingValue C P Z
  have hdis : Disjoint pool reserve := by
    dsimp only [pool, reserve, pairPaddingPool, pairPaddingReserve]
    exact Finset.disjoint_map_inl_map_inr _ _
  have hreserveZero : ∀ z ∈ reserve, f z = 0 := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hz
    rfl
  have hreserveCard : (pGroupDStar P.J + 1) - 1 ≤ reserve.card := by
    dsimp only [reserve, pairPaddingReserve]
    simp [hZcard, Nat.card_eq_fintype_card]
  have hcover : ∀ q : P.J, ∃ I : Finset X,
      I ⊆ pool ∧ (∑ z ∈ I, f z) = q := by
    intro q
    obtain ⟨t, ht, hsum⟩ := P.exists_core_subset_sum q.1 q.2
    let intoCore : ↑t ↪ ↑P.core := {
      toFun := fun i => ⟨i.1, ht i.2⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : ↑P.core => z.1) hab
    }
    let Icore : Finset (↑P.core) := t.attach.map intoCore
    let I : Finset X := Icore.map Function.Embedding.inl
    refine ⟨I, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hz
      apply Finset.mem_map.mpr
      exact ⟨i, Finset.mem_univ i, rfl⟩
    · apply Subtype.ext
      dsimp only [I, Icore]
      rw [Finset.sum_map, Finset.sum_map]
      have hterm (i : ↑t) :
          f (Function.Embedding.inl (intoCore i)) =
            ⟨C.outsideQuotientValue i.1,
              P.core_value_mem i.1 (ht i.2)⟩ := by rfl
      simp_rw [hterm]
      simpa [Finset.sum_attach] using hsum
  have hD := (pGroupDStar_spec P.J).1
  obtain ⟨T, hTsub, hTcard, hTsum⟩ :=
    forall_exists_fixedCard_sum_eq_of_pool pool reserve f
      (pGroupDStar P.J + 1) hD hdis hreserveZero hreserveCard hcover y
  let source := pairPaddingSourceEmbedding C P Z hZ
  let B : Selection xs := T.map source
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨z, hzT, rfl⟩ := Finset.mem_map.mp hi
    rcases Finset.mem_union.mp (hTsub hzT) with hzPool | hzReserve
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hzPool
      apply Finset.mem_union_left Z
      apply Finset.mem_map.mpr
      exact ⟨j.1, j.2, rfl⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hzReserve
      exact Finset.mem_union_right _ j.2
  · rw [show B.card = T.card by simp [B], hTcard]
    simp [pool, pairPaddingPool, Nat.card_eq_fintype_card, P.core_card]
  · have hpoint : ∀ z : X,
        (f z : P.J) =
          ⟨quotientDisplacement C.H C.beta
              (occurrenceValue xs (source z)), by
            cases z with
            | inl z => exact P.core_value_mem z.1 z.2
            | inr z =>
                have hzContainer := (Finset.mem_sdiff.mp (hZ z.2)).1
                have hzZero := (quotientDisplacement_eq_zero_iff C.H C.beta
                  (occurrenceValue xs z.1)).2
                    (C.container_in_coset z.1 hzContainer)
                change quotientDisplacement C.H C.beta
                    (occurrenceValue xs z.1) ∈ P.J
                rw [hzZero]
                exact P.J.zero_mem
          ⟩ := by
      intro z
      cases z with
      | inl z => rfl
      | inr z =>
          apply Subtype.ext
          have hzContainer := (Finset.mem_sdiff.mp (hZ z.2)).1
          exact ((quotientDisplacement_eq_zero_iff C.H C.beta
            (occurrenceValue xs z.1)).2
              (C.container_in_coset z.1 hzContainer)).symm
    have hTsumVal := congrArg Subtype.val hTsum
    simp_rw [hpoint] at hTsumVal
    have hsourceSum :
        QuotientAddGroup.mk' C.H
            ((∑ z ∈ T, occurrenceValue xs (source z)) - T.card • C.beta) =
          y.1 := by
      simpa [f, quotientDisplacement, Finset.sum_sub_distrib]
        using hTsumVal
    simpa [B, Finset.sum_map] using hsourceSum

/-! ## Fixed filler and enlarged core -/

/-- A subgroup has no larger `d*` than the ambient group. -/
private theorem pGroupDStar_lifted_le_ambient
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    pGroupDStar (liftedAddSubgroup H J) ≤ pGroupDStar A := by
  have hconv := pGroupDStar_subgroup_quotient_le
    (liftedAddSubgroup H J)
  omega

/-- An explicit pair certificate produces a genuinely larger canonical
Step 1 core.  Certificate existence remains outside this theorem. -/
theorem exists_strict_canonicalOrdinaryGMOStep1Core_of_pairCertificate
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (hlen : Nat.card A + pGroupDStar A ≤ xs.length) :
    ∃ C'' : CanonicalOrdinaryGMOStep1Core xs, C.H < C''.H := by
  classical
  let K := liftedAddSubgroup C.H P.J
  let pairCarrier : Selection xs := C.mapOutsideSelection P.core
  obtain ⟨Z, hZsub, hZcard⟩ := C.exists_pairZeroReserve P
  let pre : Selection xs := (C.core ∪ Z) ∪ pairCarrier
  have hcoreZ : Disjoint C.core Z := by
    rw [Finset.disjoint_left]
    intro i hiCore hiZ
    exact (Finset.mem_sdiff.mp (hZsub hiZ)).2 hiCore
  have hcontainerPair : Disjoint C.container pairCarrier := by
    exact C.disjoint_container_mapOutsideSelection P.core
  have hcoreZContainer : C.core ∪ Z ⊆ C.container := by
    exact Finset.union_subset C.core_subset_container
      (fun i hi => (Finset.mem_sdiff.mp (hZsub hi)).1)
  have hcoreZPair : Disjoint (C.core ∪ Z) pairCarrier :=
    hcontainerPair.mono_left hcoreZContainer
  have hpairCard : pairCarrier.card = Nat.card P.J - 1 := by
    rw [show pairCarrier.card = P.core.card by
      simpa [pairCarrier] using C.card_mapOutsideSelection P.core]
    exact P.core_card
  have hpreCard : pre.card =
      Nat.card C.H + pGroupDStar C.H + pGroupDStar P.J +
        (Nat.card P.J - 1) := by
    rw [show pre = (C.core ∪ Z) ∪ pairCarrier by rfl,
      Finset.card_union_of_disjoint hcoreZPair,
      Finset.card_union_of_disjoint hcoreZ,
      C.core_card, hZcard, hpairCard]
  have hpairRetained : P.core ⊆ P.retained := P.core_subset_retained
  have hpairLifted : pairCarrier ⊆ C.liftedCanonicalContainer P := by
    intro i hi
    apply Finset.mem_union_right C.container
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    apply Finset.mem_map.mpr
    exact ⟨j, hpairRetained hj, hji⟩
  have hpreLifted : pre ⊆ C.liftedCanonicalContainer P := by
    apply Finset.union_subset
    · exact (hcoreZContainer.trans Finset.subset_union_left)
    · exact hpairLifted
  let fillerCard := Nat.card K -
    (Nat.card C.H + Nat.card P.J - 1)
  have hbaseLe : Nat.card C.H + Nat.card P.J - 1 ≤ Nat.card K := by
    simpa [K] using natCard_add_natCard_sub_one_le_lifted C.H P.J
  have hpreAddFiller : pre.card + fillerCard ≤
      Nat.card K + pGroupDStar K := by
    rw [hpreCard]
    simpa [K, fillerCard, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      essentialCarrierSize_with_filler_le_lifted C.H P.J
  have hKbudget : pGroupDStar K ≤ pGroupDStar A := by
    simpa [K] using pGroupDStar_lifted_le_ambient C.H P.J
  have hliftedLower : Nat.card K + pGroupDStar A ≤
      (C.liftedCanonicalContainer P).card := by
    simpa [K] using C.card_liftedCanonicalContainer_ambient_lower P hlen
  let fillerPool := C.liftedCanonicalContainer P \ pre
  have hfillerPoolCard : fillerPool.card =
      (C.liftedCanonicalContainer P).card - pre.card := by
    dsimp only [fillerPool]
    rw [Finset.card_sdiff_of_subset hpreLifted]
  have hfillerLe : fillerCard ≤ fillerPool.card := by
    rw [hfillerPoolCard]
    have hpreLe := Finset.card_le_card hpreLifted
    omega
  obtain ⟨F, hFpool, hFcard⟩ :=
    Finset.exists_subset_card_eq (s := fillerPool) hfillerLe
  have hFdisPre : Disjoint pre F := by
    rw [Finset.disjoint_left]
    intro i hiPre hiF
    exact (Finset.mem_sdiff.mp (hFpool hiF)).2 hiPre
  have hFlifted : F ⊆ C.liftedCanonicalContainer P := by
    intro i hi
    exact (Finset.mem_sdiff.mp (hFpool hi)).1
  let essential : Selection xs := pre ∪ F
  have hessentialCard : essential.card = pre.card + fillerCard := by
    dsimp only [essential]
    rw [Finset.card_union_of_disjoint hFdisPre, hFcard]
  have hessentialLifted : essential ⊆ C.liftedCanonicalContainer P :=
    Finset.union_subset hpreLifted hFlifted
  have hessentialTarget : essential.card ≤ Nat.card K + pGroupDStar K := by
    rw [hessentialCard]
    exact hpreAddFiller
  have htargetLifted : Nat.card K + pGroupDStar K ≤
      (C.liftedCanonicalContainer P).card := by
    omega
  obtain ⟨newCore, hessentialCore, hcoreLifted, hnewCoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hessentialLifted
      hessentialTarget htargetLifted
  have hstrict : C.H < K := by
    simpa [K] using lt_liftedAddSubgroup C.H P.J P.J_ne_bot
  let C'' : CanonicalOrdinaryGMOStep1Core xs := {
    H := K
    beta := C.beta
    container := C.liftedCanonicalContainer P
    core := newCore
    core_subset_container := hcoreLifted
    container_in_coset := by
      intro i hi
      rw [C.liftedCanonicalContainer_eq_occurrencesInAddCoset P] at hi
      exact (mem_addCosetFinset_iff K C.beta _).2
        ((mem_occurrencesInAddCoset_iff xs K C.beta i).1 hi)
    container_card_lower := by simpa [K] using hliftedLower
    core_card := hnewCoreCard
    core_full := by
      intro h hh
      have hFdisp :
          (∑ i ∈ F, occurrenceValue xs i) - F.card • C.beta ∈ K := by
        rw [show (∑ i ∈ F, occurrenceValue xs i) - F.card • C.beta =
            ∑ i ∈ F, (occurrenceValue xs i - C.beta) by
          simp [Finset.sum_sub_distrib]]
        exact K.sum_mem fun i hi =>
          (mem_occurrencesInAddCoset_iff xs K C.beta i).1
            (by rw [← C.liftedCanonicalContainer_eq_occurrencesInAddCoset P];
                exact hFlifted hi)
      let y : P.J :=
        ⟨QuotientAddGroup.mk' C.H
            (h - ((∑ i ∈ F, occurrenceValue xs i) - F.card • C.beta)),
          by exact K.sub_mem hh hFdisp⟩
      obtain ⟨B, hBsub, hBcard, hBquot⟩ :=
        C.exists_exact_source_pairBlock P Z hZsub hZcard y
      have hBpre : B ⊆ pre := by
        intro i hi
        rcases Finset.mem_union.mp (hBsub hi) with hiPair | hiZ
        · exact Finset.mem_union_right _ hiPair
        · exact Finset.mem_union_left pairCarrier
            (Finset.mem_union_right C.core hiZ)
      have hBF : Disjoint B F := hFdisPre.mono_left hBpre
      have hBdispQ : QuotientAddGroup.mk' C.H
          ((∑ i ∈ B, occurrenceValue xs i) - B.card • C.beta) = y.1 :=
        hBquot
      let residual : A := h -
        ((∑ i ∈ F, occurrenceValue xs i) - F.card • C.beta) -
        ((∑ i ∈ B, occurrenceValue xs i) - B.card • C.beta)
      have hresidual : residual ∈ C.H := by
        have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hBdispQ
        have hneg := C.H.neg_mem hmem
        dsimp only [residual, y] at hneg ⊢
        convert hneg using 1 <;> abel
      obtain ⟨oldSel, holdSub, holdCard, holdSum⟩ :=
        C.core_full residual hresidual
      have holdB : Disjoint oldSel B := by
        rw [Finset.disjoint_left]
        intro i hiOld hiB
        have hiCore := holdSub hiOld
        rcases Finset.mem_union.mp (hBsub hiB) with hiPair | hiZ
        · exact (Finset.disjoint_left.mp
            (hcontainerPair.mono_left C.core_subset_container)) hiCore hiPair
        · exact (Finset.disjoint_left.mp hcoreZ) hiCore hiZ
      have holdBF : Disjoint (oldSel ∪ B) F := by
        rw [Finset.disjoint_left]
        intro i hi hiF
        rcases Finset.mem_union.mp hi with hiOld | hiB
        · exact (Finset.disjoint_left.mp hFdisPre)
            (Finset.mem_union_left pairCarrier
              (Finset.mem_union_left Z (holdSub hiOld))) hiF
        · exact (Finset.disjoint_left.mp hBF) hiB hiF
      refine ⟨(oldSel ∪ B) ∪ F, ?_, ?_, ?_⟩
      · intro i hi
        apply hessentialCore
        change i ∈ pre ∪ F
        rcases Finset.mem_union.mp hi with hiOldB | hiF
        · apply Finset.mem_union_left F
          rcases Finset.mem_union.mp hiOldB with hiOld | hiB
          · exact Finset.mem_union_left pairCarrier
              (Finset.mem_union_left Z (holdSub hiOld))
          · exact hBpre hiB
        · exact Finset.mem_union_right pre hiF
      · rw [Finset.card_union_of_disjoint holdBF,
          Finset.card_union_of_disjoint holdB,
          holdCard, hBcard, hFcard]
        have hJpos : 1 ≤ Nat.card P.J := Nat.card_pos
        have hbaseEq : Nat.card C.H + (Nat.card P.J - 1) =
            Nat.card C.H + Nat.card P.J - 1 := by omega
        rw [hbaseEq]
        dsimp only [fillerCard]
        exact Nat.add_sub_of_le hbaseLe
      · rw [Finset.sum_union holdBF, Finset.sum_union holdB, holdSum]
        dsimp only [residual]
        have htotalCard : Nat.card K =
            Nat.card C.H + B.card + F.card := by
          rw [hBcard, hFcard]
          have hJpos : 1 ≤ Nat.card P.J := Nat.card_pos
          have hbaseEq : Nat.card C.H + (Nat.card P.J - 1) =
              Nat.card C.H + Nat.card P.J - 1 := by omega
          rw [hbaseEq]
          dsimp only [fillerCard]
          exact (Nat.add_sub_of_le hbaseLe).symm
        rw [htotalCard, add_nsmul, add_nsmul]
        abel
    container_eq := C.liftedCanonicalContainer_eq_occurrencesInAddCoset P
  }
  exact ⟨C'', by simpa [C''] using hstrict⟩

end CanonicalOrdinaryGMOStep1Core

end GaoLean

#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.exists_pairZeroReserve
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.exists_exact_source_pairBlock
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.exists_strict_canonicalOrdinaryGMOStep1Core_of_pairCertificate
