import GaoLean.PGGMOClaimBQuotientSeed
import GaoLean.PGGMOQuotientLift

/-!
# Pulling the low-quotient periodic branch back to the original source

The padding zeros are used only to force the quotient-periodic coset through
zero.  Every later count is performed on genuine labelled source positions.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance claimBPeriodicQuotientFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-! ## The artificial suffix forces the quotient coset through zero -/

theorem OrdinaryGMOClaimBOutput.zero_mem_periodicCoset_of_padded
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    0 ∈ addCosetFinset Qper.H Qper.alpha := by
  classical
  by_contra hnot
  have hsuffix :
      W.paddedQuotientRArtificialSuffix hzero ⊆
        (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
          occurrencesInAddCoset (W.paddedQuotientRValues hzero)
            Qper.H Qper.alpha := by
    intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hicoset
    apply hnot
    apply (mem_addCosetFinset_iff Qper.H Qper.alpha 0).2
    have hmem := (mem_occurrencesInAddCoset_iff
      (W.paddedQuotientRValues hzero) Qper.H Qper.alpha i).1 hicoset
    rw [W.occurrenceValue_eq_zero_of_mem_artificialSuffix hzero i hi] at hmem
    exact hmem
  have hsuffixCard :
      Nat.card (A ⧸ W.K) - 1 ≤ Qper.e := by
    rw [← W.card_paddedQuotientRArtificialSuffix hzero,
      ← Qper.outside_card]
    exact Finset.card_le_card hsuffix
  have hquotientLe :
      Nat.card ((A ⧸ W.K) ⧸ Qper.H) ≤ Nat.card (A ⧸ W.K) :=
    Nat.le_of_dvd Nat.card_pos Qper.H.card_quotient_dvd_card
  have hquotientTwo : 2 ≤ Nat.card ((A ⧸ W.K) ⧸ Qper.H) :=
    two_le_natCard_quotient_of_lt_top Qper.H Qper.proper
  have hambientTwo : 2 ≤ Nat.card (A ⧸ W.K) :=
    le_trans hquotientTwo hquotientLe
  have headd : Qper.e + 2 ≤ Nat.card ((A ⧸ W.K) ⧸ Qper.H) :=
    (Nat.le_sub_iff_add_le hquotientTwo).mp Qper.outside_le
  have headdAmbient : Qper.e + 2 ≤ Nat.card (A ⧸ W.K) :=
    headd.trans hquotientLe
  have hone : 1 ≤ Nat.card (A ⧸ W.K) := by omega
  have hambientLe : Nat.card (A ⧸ W.K) ≤ Qper.e + 1 := by
    rw [← Nat.sub_add_cancel hone]
    exact Nat.add_le_add_right hsuffixCard 1
  have : Qper.e + 2 ≤ Qper.e + 1 := headdAmbient.trans hambientLe
  omega

theorem OrdinaryGMOClaimBOutput.periodicAlpha_mem
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    Qper.alpha ∈ Qper.H := by
  have hzeroCoset := W.zero_mem_periodicCoset_of_padded hzero Qper
  have hneg : -Qper.alpha ∈ Qper.H := by
    simpa using (mem_addCosetFinset_iff Qper.H Qper.alpha 0).1 hzeroCoset
  simpa using Qper.H.neg_mem hneg

/-! ## The lifted subgroup and center -/

noncomputable def OrdinaryGMOClaimBOutput.periodicLiftedCenter
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (J : AddSubgroup (A ⧸ W.K)) (alpha : A ⧸ W.K) : A :=
  W.g + liftedQuotientRepresentative W.K alpha

theorem OrdinaryGMOClaimBOutput.periodicRepresentative_mem_lifted
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    liftedQuotientRepresentative W.K Qper.alpha ∈
      liftedAddSubgroup W.K Qper.H := by
  change QuotientAddGroup.mk' W.K
      (liftedQuotientRepresentative W.K Qper.alpha) ∈ Qper.H
  rw [mk_liftedQuotientRepresentative]
  exact W.periodicAlpha_mem hzero Qper

theorem OrdinaryGMOClaimBOutput.support_mem_periodicLiftedCoset
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition)
    (i : Occurrence xs) (hi : i ∈ W.partition.support) :
    occurrenceValue xs i ∈ addCosetFinset
      (liftedAddSubgroup W.K Qper.H)
      (W.periodicLiftedCenter Qper.H Qper.alpha) := by
  have hiK := (mem_addCosetFinset_iff W.K W.g
    (occurrenceValue xs i)).1 (W.support_in_coset i hi)
  have hiL : occurrenceValue xs i - W.g ∈
      liftedAddSubgroup W.K Qper.H :=
    le_liftedAddSubgroup W.K Qper.H hiK
  have haL := W.periodicRepresentative_mem_lifted hzero Qper
  apply (mem_addCosetFinset_iff _ _ _).2
  dsimp [OrdinaryGMOClaimBOutput.periodicLiftedCenter]
  have hsub := (liftedAddSubgroup W.K Qper.H).sub_mem hiL haL
  convert hsub using 1 <;> abel

theorem OrdinaryGMOClaimBOutput.source_mem_periodicLiftedCoset_of_displacement
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (J : AddSubgroup (A ⧸ W.K)) (alpha : A ⧸ W.K)
    (i : Occurrence xs)
    (hi : W.quotientDisplacement i ∈ addCosetFinset J alpha) :
    occurrenceValue xs i ∈ addCosetFinset (liftedAddSubgroup W.K J)
      (W.periodicLiftedCenter J alpha) := by
  let a := liftedQuotientRepresentative W.K alpha
  have hdisp : occurrenceValue xs i - W.g ∈
      addCosetFinset (liftedAddSubgroup W.K J) a := by
    apply (mk_mem_addCosetFinset_iff_mem_liftedAddCoset_rep
      W.K J alpha (occurrenceValue xs i - W.g)).1
    simpa [OrdinaryGMOClaimBOutput.quotientDisplacement] using hi
  have hsub := (mem_addCosetFinset_iff
    (liftedAddSubgroup W.K J) a (occurrenceValue xs i - W.g)).1 hdisp
  apply (mem_addCosetFinset_iff _ _ _).2
  dsimp [OrdinaryGMOClaimBOutput.periodicLiftedCenter, a] at hsub ⊢
  convert hsub using 1 <;> abel

/-! ## Genuine source positions outside the lifted coset inject into the
canonical quotient outside selection -/

theorem OrdinaryGMOClaimBOutput.exists_prefixOutside_of_sourceOutside
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition)
    (i : Occurrence xs)
    (hi : i ∈ (Finset.univ : Selection xs) \
      occurrencesInAddCoset xs (liftedAddSubgroup W.K Qper.H)
        (W.periodicLiftedCenter Qper.H Qper.alpha)) :
    ∃ j : Occurrence (W.quotientRValues hzero),
      W.paddedQuotientRSeedEmbedding hzero j ∈
        (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
          occurrencesInAddCoset (W.paddedQuotientRValues hzero)
            Qper.H Qper.alpha ∧
      W.paddedQuotientRSeedOriginalEmbedding hzero j = i := by
  classical
  have hiOut := (Finset.mem_sdiff.mp hi).2
  have hiNotSupport : i ∉ W.partition.support := by
    intro hiSupport
    apply hiOut
    apply (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup W.K Qper.H)
      (W.periodicLiftedCenter Qper.H Qper.alpha) i).2
    exact (mem_addCosetFinset_iff _ _ _).1
      (W.support_mem_periodicLiftedCoset hzero Qper i hiSupport)
  have hiRemaining : i ∈ W.remainingOccurrences :=
    (W.mem_remainingOccurrences_iff i).2 hiNotSupport
  have hiRange : i ∈
      (Finset.univ : Selection W.quotientDisplacementSequence).map
        W.quotientSourceEmbedding := by
    rw [W.map_univ_quotientSourceEmbedding]
    exact hiRemaining
  obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hiRange
  have hqR : q ∈ W.quotientR hzero := by
    by_contra hnotR
    have hqCompl : q ∈
        (Finset.univ : Selection W.quotientDisplacementSequence) \
          W.quotientR hzero := Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ q, hnotR⟩
    have hqZero := W.occurrenceValue_eq_zero_of_mem_compl_quotientR
      hzero q hqCompl
    have hdispZero : W.quotientDisplacement i = 0 := by
      change W.quotientSourceOccurrence q = i at hqi
      calc
        W.quotientDisplacement i =
            W.quotientDisplacement (W.quotientSourceOccurrence q) := by
          rw [hqi]
        _ = occurrenceValue W.quotientDisplacementSequence q :=
          (W.occurrenceValue_quotientDisplacementSequence q).symm
        _ = 0 := hqZero
    have hzeroCoset := W.zero_mem_periodicCoset_of_padded hzero Qper
    have hiCoset := W.source_mem_periodicLiftedCoset_of_displacement
      Qper.H Qper.alpha i (by simpa [hdispZero] using hzeroCoset)
    apply hiOut
    apply (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup W.K Qper.H)
      (W.periodicLiftedCenter Qper.H Qper.alpha) i).2
    exact (mem_addCosetFinset_iff _ _ _).1 hiCoset
  have hqList : q ∈ (W.quotientR hzero).toList :=
    Finset.mem_toList.mpr hqR
  obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp hqList
  let j : Occurrence (W.quotientRValues hzero) :=
    ⟨j0.val, by
      simpa [OrdinaryGMOClaimBOutput.quotientRValues] using j0.isLt⟩
  have hsource : W.quotientRListSourceEmbedding hzero j = q := by
    change (W.quotientR hzero).toList.get _ = q
    have hindex :
        (⟨j.val, by
          simpa [OrdinaryGMOClaimBOutput.quotientRValues]
            using j.isLt⟩ : Fin (W.quotientR hzero).toList.length) = j0 := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hj0
  refine ⟨j, ?_, ?_⟩
  · apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hjCoset
    have hjMem := (mem_occurrencesInAddCoset_iff
      (W.paddedQuotientRValues hzero) Qper.H Qper.alpha
      (W.paddedQuotientRSeedEmbedding hzero j)).1 hjCoset
    have hdispMem : W.quotientDisplacement i ∈
        addCosetFinset Qper.H Qper.alpha := by
      apply (mem_addCosetFinset_iff Qper.H Qper.alpha _).2
      have hvalue := W.occurrenceValue_paddedSeed_eq_sourceDisplacement hzero j
      have horiginal :
          W.paddedQuotientRSeedOriginalEmbedding hzero j = i := by
        change W.quotientSourceOccurrence
          (W.quotientRListSourceEmbedding hzero j) = i
        rw [hsource]
        exact hqi
      rw [horiginal] at hvalue
      simpa [hvalue] using hjMem
    apply hiOut
    apply (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup W.K Qper.H)
      (W.periodicLiftedCenter Qper.H Qper.alpha) i).2
    exact (mem_addCosetFinset_iff _ _ _).1
      (W.source_mem_periodicLiftedCoset_of_displacement
        Qper.H Qper.alpha i hdispMem)
  · change W.quotientSourceOccurrence
      (W.quotientRListSourceEmbedding hzero j) = i
    rw [hsource]
    exact hqi

theorem OrdinaryGMOClaimBOutput.card_sourceOutside_le_periodicE
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    ((Finset.univ : Selection xs) \
      occurrencesInAddCoset xs (liftedAddSubgroup W.K Qper.H)
        (W.periodicLiftedCenter Qper.H Qper.alpha)).card ≤ Qper.e := by
  classical
  let sourceOutside : Selection xs :=
    (Finset.univ : Selection xs) \
      occurrencesInAddCoset xs (liftedAddSubgroup W.K Qper.H)
        (W.periodicLiftedCenter Qper.H Qper.alpha)
  let quotientOutside : Selection (W.paddedQuotientRValues hzero) :=
    (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
      occurrencesInAddCoset (W.paddedQuotientRValues hzero)
        Qper.H Qper.alpha
  let witness : ∀ i : ↥sourceOutside,
      ∃ j : Occurrence (W.quotientRValues hzero),
        W.paddedQuotientRSeedEmbedding hzero j ∈ quotientOutside ∧
        W.paddedQuotientRSeedOriginalEmbedding hzero j = i.1 := fun i ↦ by
    simpa [sourceOutside, quotientOutside] using
      W.exists_prefixOutside_of_sourceOutside hzero Qper i.1 i.2
  let pick : ↥sourceOutside → Occurrence (W.quotientRValues hzero) :=
    fun i ↦ Classical.choose (witness i)
  have pick_spec : ∀ i : ↥sourceOutside,
      W.paddedQuotientRSeedEmbedding hzero (pick i) ∈ quotientOutside ∧
      W.paddedQuotientRSeedOriginalEmbedding hzero (pick i) = i.1 := by
    intro i
    exact Classical.choose_spec (witness i)
  have hcard : sourceOutside.card ≤ quotientOutside.card := by
    let f : ↥sourceOutside → ↥quotientOutside := fun i ↦
      ⟨W.paddedQuotientRSeedEmbedding hzero (pick i), (pick_spec i).1⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      have hpadded := congrArg Subtype.val hij
      have hpick : pick i = pick j :=
        (W.paddedQuotientRSeedEmbedding hzero).injective hpadded
      calc
        i.1 = W.paddedQuotientRSeedOriginalEmbedding hzero (pick i) :=
          (pick_spec i).2.symm
        _ = W.paddedQuotientRSeedOriginalEmbedding hzero (pick j) := by
          rw [hpick]
        _ = j.1 := (pick_spec j).2
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  simpa [sourceOutside, quotientOutside, Qper.outside_card] using hcard

/-- Every padded quotient occurrence outside the periodic coset is genuine
and nonzero.  Thus the quotient exception count cannot be paid for by an
artificial zero or by one of the chosen genuine zeros. -/
theorem OrdinaryGMOClaimBOutput.periodicE_le_quotientRExceptionCount
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    Qper.e ≤ W.quotientRExceptionCount := by
  classical
  let quotientOutside : Selection (W.paddedQuotientRValues hzero) :=
    (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
      occurrencesInAddCoset (W.paddedQuotientRValues hzero)
        Qper.H Qper.alpha
  have hzeroCoset := W.zero_mem_periodicCoset_of_padded hzero Qper
  have outside_mem_seed : ∀ i : ↥quotientOutside,
      i.1 ∈ W.paddedQuotientRSeed hzero := by
    intro i
    by_contra hiNotSeed
    have hiArtificial : i.1 ∈ W.paddedQuotientRArtificialSuffix hzero := by
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_univ i.1, hiNotSeed⟩
    have hiNotCoset := (Finset.mem_sdiff.mp i.2).2
    apply hiNotCoset
    apply (mem_occurrencesInAddCoset_iff
      (W.paddedQuotientRValues hzero) Qper.H Qper.alpha i.1).2
    have hvalue := W.occurrenceValue_eq_zero_of_mem_artificialSuffix
      hzero i.1 hiArtificial
    have hzeroMem := (mem_addCosetFinset_iff Qper.H Qper.alpha 0).1
      hzeroCoset
    simpa [hvalue] using hzeroMem
  let prefixIndex : ↥quotientOutside →
      Occurrence (W.quotientRValues hzero) := fun i ↦
    ⟨i.1.val, (W.mem_paddedQuotientRSeed_iff hzero i.1).1
      (outside_mem_seed i)⟩
  let toNonzero : ↥quotientOutside →
      Occurrence W.quotientDisplacementSequence := fun i ↦
    W.quotientRListSourceEmbedding hzero (prefixIndex i)
  let f : ↥quotientOutside → ↥W.nonzeroQuotientOccurrences := fun i ↦ by
    let q := toNonzero i
    refine ⟨q, (W.mem_nonzeroQuotientOccurrences_iff q).2 ?_⟩
    intro hqZero
    have hiValueZero : occurrenceValue (W.paddedQuotientRValues hzero) i.1 = 0 := by
      have hemb : W.paddedQuotientRSeedEmbedding hzero (prefixIndex i) = i.1 := by
        apply Fin.ext
        rfl
      have hqZero' : occurrenceValue W.quotientDisplacementSequence
          (W.quotientRListSourceEmbedding hzero (prefixIndex i)) = 0 := by
        simpa [q, toNonzero] using hqZero
      calc
        occurrenceValue (W.paddedQuotientRValues hzero) i.1 =
            occurrenceValue (W.paddedQuotientRValues hzero)
              (W.paddedQuotientRSeedEmbedding hzero (prefixIndex i)) := by
          rw [hemb]
        _ = occurrenceValue (W.quotientRValues hzero) (prefixIndex i) :=
          W.occurrenceValue_paddedQuotientRSeedEmbedding hzero (prefixIndex i)
        _ = occurrenceValue W.quotientDisplacementSequence
            (W.quotientRListSourceEmbedding hzero (prefixIndex i)) :=
          (W.occurrenceValue_quotientRListSourceEmbedding hzero
            (prefixIndex i)).symm
        _ = 0 := hqZero'
    have hiNotCoset := (Finset.mem_sdiff.mp i.2).2
    apply hiNotCoset
    apply (mem_occurrencesInAddCoset_iff
      (W.paddedQuotientRValues hzero) Qper.H Qper.alpha i.1).2
    have hzeroMem := (mem_addCosetFinset_iff Qper.H Qper.alpha 0).1 hzeroCoset
    simpa [hiValueZero] using hzeroMem
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hq := congrArg Subtype.val hij
    have hprefix : prefixIndex i = prefixIndex j :=
      (W.quotientRListSourceEmbedding hzero).injective hq
    apply Fin.ext
    exact congrArg
      (fun q : Occurrence (W.quotientRValues hzero) ↦ q.val) hprefix
  rw [← Qper.outside_card]
  simpa only [Fintype.card_coe, quotientOutside,
    OrdinaryGMOClaimBOutput.quotientRExceptionCount] using
    Fintype.card_le_of_injective f hf

/-! ## Final source concentration -/

noncomputable def OrdinaryGMOClaimBOutput.periodicAlternativeConcentration
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    OrdinaryGMOConcentration xs := by
  classical
  let L := liftedAddSubgroup W.K Qper.H
  let a := W.periodicLiftedCenter Qper.H Qper.alpha
  have hproper : L < ⊤ :=
    liftedAddSubgroup_lt_top_of_lt_top W.K Qper.H Qper.proper
  have hquotient : Nat.card (A ⧸ L) =
      Nat.card ((A ⧸ W.K) ⧸ Qper.H) := by
    simpa [L] using natCard_quotient_liftedAddSubgroup W.K Qper.H
  have hout := W.card_sourceOutside_le_periodicE hzero Qper
  have hquotientTwo : 2 ≤ Nat.card (A ⧸ L) :=
    two_le_natCard_quotient_of_lt_top L hproper
  have headd : Qper.e + 2 ≤ Nat.card (A ⧸ L) := by
    rw [hquotient]
    exact (Nat.le_sub_iff_add_le
      (two_le_natCard_quotient_of_lt_top Qper.H Qper.proper)).mp Qper.outside_le
  let C : Selection xs := occurrencesInAddCoset xs L a
  have hC : C ⊆ (Finset.univ : Selection xs) := Finset.subset_univ C
  have hcount :
      ((Finset.univ : Selection xs) \ C).card + C.card = xs.length := by
    simpa [C] using Finset.card_sdiff_add_card_eq_card hC
  refine {
    K := L
    strict := hproper
    alpha := a
    selected := C
    sourceCoset := ?_
    card_lower := ?_
  }
  · intro i hi
    exact (mem_occurrencesInAddCoset_iff xs L a i).1 hi
  · have hout' : ((Finset.univ : Selection xs) \ C).card ≤ Qper.e := by
      simpa [C, L, a] using hout
    by_cases hwide : Nat.card (A ⧸ L) ≤ xs.length
    · have hwide' : Nat.card (A ⧸ L) ≤
          ((Finset.univ : Selection xs) \ C).card + C.card := by
        simpa [hcount] using hwide
      have hrecover := Nat.sub_add_cancel hwide'
      rw [← hcount]
      omega
    · have hKstar : 1 ≤ pGroupDStar W.K := by
        letI : Fintype W.K := Fintype.ofFinite W.K
        letI : Nontrivial W.K :=
          (AddSubgroup.nontrivial_iff_ne_bot W.K).2 W.nontrivial
        have hgt := one_lt_ordinaryDavenportValue (B := W.K)
        have hrecover := pGroupDStar_add_one W.K
        omega
      have hsupport : 1 ≤ W.supportCard := by
        have hcells : pGroupDStar W.K ≤ W.supportCard := by
          rw [← W.partition.sum_card_valueCell]
          calc
            pGroupDStar W.K = ∑ _c : Fin (pGroupDStar W.K), 1 := by simp
            _ ≤ ∑ c : Fin (pGroupDStar W.K),
                (W.partition.valueCell c).card := by
              apply Finset.sum_le_sum
              intro c hc
              rw [W.partition.card_valueCell c]
              exact Finset.card_pos.mpr (W.partition.cells_nonempty c)
        exact hKstar.trans hcells
      have hdQ : 1 ≤ dQ := by
        by_contra hdQnot
        have hdQzero : dQ = 0 := by omega
        have hvalues : Qpartition.valueCells = [] := by
          apply List.eq_nil_of_length_eq_zero
          simpa [hdQzero] using Qpartition.length_valueCells
        have hsumset : Qpartition.sumset = {0} := by
          simp [Theorem21SetPartition.sumset, hvalues,
            fullLayerSumSpectrum_nil]
        have hHne : Qper.H ≠ ⊥ := ne_of_gt Qper.nontrivial
        letI : Nontrivial Qper.H :=
          (AddSubgroup.nontrivial_iff_ne_bot Qper.H).2 hHne
        have hHtwo : 2 ≤ Nat.card Qper.H := by
          have hnontrivial : Nontrivial Qper.H := inferInstance
          exact (Finite.one_lt_card_iff_nontrivial).2 hnontrivial
        have hmul : Nat.card Qper.H ≤
            (Qper.e + 1) * Nat.card Qper.H := by
          simpa using Nat.mul_le_mul_right (Nat.card Qper.H)
            (Nat.succ_le_succ (Nat.zero_le Qper.e))
        have hspectrum := Qper.spectrum_card_lower
        rw [hsumset] at hspectrum
        simp only [Finset.card_singleton] at hspectrum
        omega
      have hRle : W.quotientRExceptionCount + dQ ≤
          W.remainingOccurrences.card := by
        rw [← W.card_quotientR hzero,
          ← W.length_quotientDisplacementSequence]
        simpa only [Fintype.card_fin] using
          Finset.card_le_univ (W.quotientR hzero)
      have hsourceCount :
          W.remainingOccurrences.card + W.supportCard = xs.length := by
        simpa [OrdinaryGMOClaimBOutput.remainingOccurrences,
          W.partition.card_support_eq] using
          Finset.card_sdiff_add_card_eq_card
            (Finset.subset_univ W.partition.support)
      have heSource : Qper.e + 2 ≤ xs.length := by
        have heR := W.periodicE_le_quotientRExceptionCount hzero Qper
        rw [← hsourceCount]
        omega
      have hselectedTwo : 2 ≤ C.card := by
        rw [← hcount] at heSource
        omega
      have hsmall : xs.length - Nat.card (A ⧸ L) = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hwide)
      rw [hsmall]
      simpa using hselectedTwo

theorem OrdinaryGMOClaimBOutput.nonempty_periodicAlternativeConcentration
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    {Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card}
    (Qper : GMOTheorem21PeriodicAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition) :
    Nonempty (OrdinaryGMOConcentration xs) :=
  ⟨W.periodicAlternativeConcentration hzero Qper⟩

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.zero_mem_periodicCoset_of_padded
#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_sourceOutside_le_periodicE
#print axioms GaoLean.OrdinaryGMOClaimBOutput.periodicAlternativeConcentration
