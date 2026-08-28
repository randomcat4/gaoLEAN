import GaoLean.PGGMOClaimBQuotientPeriodic

/-!
# Pulling a quotient concentration back to the original source

Unlike the periodic alternative, an `OrdinaryGMOConcentration` may use the
bottom subgroup and may select only part of its canonical coset.  We first
recover the canonical outside bound from its `card_lower`, then use the
artificial suffix only to force the quotient coset through zero.  All source
counts are subsequently performed on labelled genuine occurrences.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance claimBConcentrationQuotientFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-! ## Recovering the canonical quotient-coset bound -/

theorem OrdinaryGMOClaimBOutput.padded_quotientCard_le_length
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ) (J : AddSubgroup (A ⧸ W.K)) :
    Nat.card ((A ⧸ W.K) ⧸ J) ≤
      (W.paddedQuotientRValues hzero).length := by
  have hquotientLe : Nat.card ((A ⧸ W.K) ⧸ J) ≤ Nat.card (A ⧸ W.K) :=
    Nat.le_of_dvd Nat.card_pos J.card_quotient_dvd_card
  rw [W.length_paddedQuotientRValues hzero]
  have hambientPos : 1 ≤ Nat.card (A ⧸ W.K) := Nat.card_pos
  have hrecover := Nat.sub_add_cancel hambientPos
  omega

theorem OrdinaryGMOClaimBOutput.concentration_canonicalOutside_le
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero)) :
    ((Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
      occurrencesInAddCoset (W.paddedQuotientRValues hzero)
        CQ.K CQ.alpha).card ≤ Nat.card ((A ⧸ W.K) ⧸ CQ.K) - 2 := by
  classical
  let C : Selection (W.paddedQuotientRValues hzero) :=
    occurrencesInAddCoset (W.paddedQuotientRValues hzero) CQ.K CQ.alpha
  have hselected : CQ.selected ⊆ C := by
    intro i hi
    apply (mem_occurrencesInAddCoset_iff
      (W.paddedQuotientRValues hzero) CQ.K CQ.alpha i).2
    exact CQ.sourceCoset i hi
  have hselectedCard : CQ.selected.card ≤ C.card :=
    Finset.card_le_card hselected
  have hC : C ⊆
      (Finset.univ : Selection (W.paddedQuotientRValues hzero)) :=
    Finset.subset_univ C
  have hcount :
      ((Finset.univ : Selection (W.paddedQuotientRValues hzero)) \ C).card +
        C.card = (W.paddedQuotientRValues hzero).length := by
    simpa [C] using Finset.card_sdiff_add_card_eq_card hC
  have hwide := W.padded_quotientCard_le_length hzero hdQpos CQ.K
  have hrecover :
      (W.paddedQuotientRValues hzero).length -
          Nat.card ((A ⧸ W.K) ⧸ CQ.K) +
          Nat.card ((A ⧸ W.K) ⧸ CQ.K) =
        (W.paddedQuotientRValues hzero).length :=
    Nat.sub_add_cancel hwide
  have houtAdd :
      ((Finset.univ : Selection (W.paddedQuotientRValues hzero)) \ C).card + 2 ≤
        Nat.card ((A ⧸ W.K) ⧸ CQ.K) := by
    have hlower := CQ.card_lower
    omega
  have hquotientTwo : 2 ≤ Nat.card ((A ⧸ W.K) ⧸ CQ.K) :=
    two_le_natCard_quotient_of_lt_top CQ.K CQ.strict
  exact (Nat.le_sub_iff_add_le hquotientTwo).2 (by simpa [C] using houtAdd)

/-! ## Artificial zeros force the quotient coset through zero -/

theorem OrdinaryGMOClaimBOutput.zero_mem_concentrationCoset_of_padded
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero)) :
    0 ∈ addCosetFinset CQ.K CQ.alpha := by
  classical
  by_contra hnot
  have hsuffix : W.paddedQuotientRArtificialSuffix hzero ⊆
      (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
        occurrencesInAddCoset (W.paddedQuotientRValues hzero)
          CQ.K CQ.alpha := by
    intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hicoset
    apply hnot
    apply (mem_addCosetFinset_iff CQ.K CQ.alpha 0).2
    have hmem := (mem_occurrencesInAddCoset_iff
      (W.paddedQuotientRValues hzero) CQ.K CQ.alpha i).1 hicoset
    rw [W.occurrenceValue_eq_zero_of_mem_artificialSuffix hzero i hi] at hmem
    exact hmem
  have hsuffixCard : Nat.card (A ⧸ W.K) - 1 ≤
      ((Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
        occurrencesInAddCoset (W.paddedQuotientRValues hzero)
          CQ.K CQ.alpha).card := by
    rw [← W.card_paddedQuotientRArtificialSuffix hzero]
    exact Finset.card_le_card hsuffix
  have hout := W.concentration_canonicalOutside_le hzero hdQpos CQ
  have hquotientLe : Nat.card ((A ⧸ W.K) ⧸ CQ.K) ≤ Nat.card (A ⧸ W.K) :=
    Nat.le_of_dvd Nat.card_pos CQ.K.card_quotient_dvd_card
  have hquotientTwo : 2 ≤ Nat.card ((A ⧸ W.K) ⧸ CQ.K) :=
    two_le_natCard_quotient_of_lt_top CQ.K CQ.strict
  have headd := (Nat.le_sub_iff_add_le hquotientTwo).1 hout
  have headdAmbient := headd.trans hquotientLe
  have hambientPos : 1 ≤ Nat.card (A ⧸ W.K) := by omega
  have hambientLe : Nat.card (A ⧸ W.K) ≤
      ((Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
        occurrencesInAddCoset (W.paddedQuotientRValues hzero)
          CQ.K CQ.alpha).card + 1 := by
    rw [← Nat.sub_add_cancel hambientPos]
    exact Nat.add_le_add_right hsuffixCard 1
  omega

theorem OrdinaryGMOClaimBOutput.concentrationAlpha_mem
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero)) :
    CQ.alpha ∈ CQ.K := by
  have hzeroCoset := W.zero_mem_concentrationCoset_of_padded hzero hdQpos CQ
  have hneg : -CQ.alpha ∈ CQ.K := by
    simpa using (mem_addCosetFinset_iff CQ.K CQ.alpha 0).1 hzeroCoset
  simpa using CQ.K.neg_mem hneg

theorem OrdinaryGMOClaimBOutput.support_mem_concentrationLiftedCoset
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero))
    (i : Occurrence xs) (hi : i ∈ W.partition.support) :
    occurrenceValue xs i ∈ addCosetFinset (liftedAddSubgroup W.K CQ.K)
      (W.periodicLiftedCenter CQ.K CQ.alpha) := by
  have hiK := (mem_addCosetFinset_iff W.K W.g
    (occurrenceValue xs i)).1 (W.support_in_coset i hi)
  have hiL : occurrenceValue xs i - W.g ∈ liftedAddSubgroup W.K CQ.K :=
    le_liftedAddSubgroup W.K CQ.K hiK
  have haL : liftedQuotientRepresentative W.K CQ.alpha ∈
      liftedAddSubgroup W.K CQ.K := by
    change QuotientAddGroup.mk' W.K
      (liftedQuotientRepresentative W.K CQ.alpha) ∈ CQ.K
    rw [mk_liftedQuotientRepresentative]
    exact W.concentrationAlpha_mem hzero hdQpos CQ
  apply (mem_addCosetFinset_iff _ _ _).2
  dsimp [OrdinaryGMOClaimBOutput.periodicLiftedCenter]
  have hsub := (liftedAddSubgroup W.K CQ.K).sub_mem hiL haL
  convert hsub using 1 <;> abel

/-! ## Source outside positions inject into the genuine prefix outside -/

theorem OrdinaryGMOClaimBOutput.exists_prefixOutside_of_sourceOutside_concentration
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero))
    (i : Occurrence xs)
    (hi : i ∈ (Finset.univ : Selection xs) \
      occurrencesInAddCoset xs (liftedAddSubgroup W.K CQ.K)
        (W.periodicLiftedCenter CQ.K CQ.alpha)) :
    ∃ j : Occurrence (W.quotientRValues hzero),
      W.paddedQuotientRSeedEmbedding hzero j ∈
        (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
          occurrencesInAddCoset (W.paddedQuotientRValues hzero)
            CQ.K CQ.alpha ∧
      W.paddedQuotientRSeedOriginalEmbedding hzero j = i := by
  classical
  have hiOut := (Finset.mem_sdiff.mp hi).2
  have hiNotSupport : i ∉ W.partition.support := by
    intro hiSupport
    apply hiOut
    apply (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup W.K CQ.K)
      (W.periodicLiftedCenter CQ.K CQ.alpha) i).2
    exact (mem_addCosetFinset_iff _ _ _).1
      (W.support_mem_concentrationLiftedCoset hzero hdQpos CQ i hiSupport)
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
          W.quotientR hzero :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, hnotR⟩
    have hqZero := W.occurrenceValue_eq_zero_of_mem_compl_quotientR
      hzero q hqCompl
    change W.quotientSourceOccurrence q = i at hqi
    have hdispZero : W.quotientDisplacement i = 0 := by
      calc
        W.quotientDisplacement i =
            W.quotientDisplacement (W.quotientSourceOccurrence q) := by rw [hqi]
        _ = occurrenceValue W.quotientDisplacementSequence q :=
          (W.occurrenceValue_quotientDisplacementSequence q).symm
        _ = 0 := hqZero
    have hzeroCoset := W.zero_mem_concentrationCoset_of_padded hzero hdQpos CQ
    have hiCoset := W.source_mem_periodicLiftedCoset_of_displacement
      CQ.K CQ.alpha i (by simpa [hdispZero] using hzeroCoset)
    apply hiOut
    apply (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup W.K CQ.K)
      (W.periodicLiftedCenter CQ.K CQ.alpha) i).2
    exact (mem_addCosetFinset_iff _ _ _).1 hiCoset
  have hqList : q ∈ (W.quotientR hzero).toList := Finset.mem_toList.mpr hqR
  obtain ⟨j0, hj0⟩ := List.mem_iff_get.mp hqList
  let j : Occurrence (W.quotientRValues hzero) :=
    ⟨j0.val, by simpa [OrdinaryGMOClaimBOutput.quotientRValues] using j0.isLt⟩
  have hsource : W.quotientRListSourceEmbedding hzero j = q := by
    change (W.quotientR hzero).toList.get _ = q
    have hindex :
        (⟨j.val, by simpa [OrdinaryGMOClaimBOutput.quotientRValues]
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
      (W.paddedQuotientRValues hzero) CQ.K CQ.alpha
      (W.paddedQuotientRSeedEmbedding hzero j)).1 hjCoset
    have horiginal : W.paddedQuotientRSeedOriginalEmbedding hzero j = i := by
      change W.quotientSourceOccurrence
        (W.quotientRListSourceEmbedding hzero j) = i
      rw [hsource]
      exact hqi
    have hdispMem : W.quotientDisplacement i ∈ addCosetFinset CQ.K CQ.alpha := by
      apply (mem_addCosetFinset_iff CQ.K CQ.alpha _).2
      have hvalue := W.occurrenceValue_paddedSeed_eq_sourceDisplacement hzero j
      rw [horiginal] at hvalue
      simpa [hvalue] using hjMem
    apply hiOut
    apply (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup W.K CQ.K)
      (W.periodicLiftedCenter CQ.K CQ.alpha) i).2
    exact (mem_addCosetFinset_iff _ _ _).1
      (W.source_mem_periodicLiftedCoset_of_displacement
        CQ.K CQ.alpha i hdispMem)
  · change W.quotientSourceOccurrence
      (W.quotientRListSourceEmbedding hzero j) = i
    rw [hsource]
    exact hqi

theorem OrdinaryGMOClaimBOutput.card_sourceOutside_le_concentrationOutside
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero)) :
    ((Finset.univ : Selection xs) \
      occurrencesInAddCoset xs (liftedAddSubgroup W.K CQ.K)
        (W.periodicLiftedCenter CQ.K CQ.alpha)).card ≤
      ((Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
        occurrencesInAddCoset (W.paddedQuotientRValues hzero)
          CQ.K CQ.alpha).card := by
  classical
  let sourceOutside : Selection xs :=
    (Finset.univ : Selection xs) \
      occurrencesInAddCoset xs (liftedAddSubgroup W.K CQ.K)
        (W.periodicLiftedCenter CQ.K CQ.alpha)
  let quotientOutside : Selection (W.paddedQuotientRValues hzero) :=
    (Finset.univ : Selection (W.paddedQuotientRValues hzero)) \
      occurrencesInAddCoset (W.paddedQuotientRValues hzero) CQ.K CQ.alpha
  let witness : ∀ i : ↥sourceOutside,
      ∃ j : Occurrence (W.quotientRValues hzero),
        W.paddedQuotientRSeedEmbedding hzero j ∈ quotientOutside ∧
        W.paddedQuotientRSeedOriginalEmbedding hzero j = i.1 := fun i ↦ by
    simpa [sourceOutside, quotientOutside] using
      W.exists_prefixOutside_of_sourceOutside_concentration
        hzero hdQpos CQ i.1 i.2
  let pick : ↥sourceOutside → Occurrence (W.quotientRValues hzero) :=
    fun i ↦ Classical.choose (witness i)
  have pick_spec : ∀ i : ↥sourceOutside,
      W.paddedQuotientRSeedEmbedding hzero (pick i) ∈ quotientOutside ∧
      W.paddedQuotientRSeedOriginalEmbedding hzero (pick i) = i.1 :=
    fun i ↦ Classical.choose_spec (witness i)
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
      _ = W.paddedQuotientRSeedOriginalEmbedding hzero (pick j) := by rw [hpick]
      _ = j.1 := (pick_spec j).2
  simpa only [Fintype.card_coe, sourceOutside, quotientOutside] using
    Fintype.card_le_of_injective f hf

/-! ## Final lifted concentration, including the short-source ledger -/

noncomputable def OrdinaryGMOClaimBOutput.quotientConcentrationPullback
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero)) :
    OrdinaryGMOConcentration xs := by
  classical
  let L := liftedAddSubgroup W.K CQ.K
  let a := W.periodicLiftedCenter CQ.K CQ.alpha
  let C : Selection xs := occurrencesInAddCoset xs L a
  have hproper : L < ⊤ :=
    liftedAddSubgroup_lt_top_of_lt_top W.K CQ.K CQ.strict
  have hquotient : Nat.card (A ⧸ L) = Nat.card ((A ⧸ W.K) ⧸ CQ.K) := by
    simpa [L] using natCard_quotient_liftedAddSubgroup W.K CQ.K
  have houtSource := W.card_sourceOutside_le_concentrationOutside
    hzero hdQpos CQ
  have houtQuotient := W.concentration_canonicalOutside_le hzero hdQpos CQ
  have hout : ((Finset.univ : Selection xs) \ C).card ≤
      Nat.card (A ⧸ L) - 2 := by
    rw [hquotient]
    exact houtSource.trans houtQuotient
  have hC : C ⊆ (Finset.univ : Selection xs) := Finset.subset_univ C
  have hcount : ((Finset.univ : Selection xs) \ C).card + C.card =
      xs.length := by
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
  · have hquotientTwo : 2 ≤ Nat.card (A ⧸ L) :=
      two_le_natCard_quotient_of_lt_top L hproper
    have houtAdd := (Nat.le_sub_iff_add_le hquotientTwo).1 hout
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
      have hsupport : 1 ≤ W.partition.support.card := by
        rw [W.partition.card_support_eq]
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
      have hzeroFiberNonempty : (W.quotientFiber 0).Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨q, hqZeroFiber⟩ := hzeroFiberNonempty
      let iz : Occurrence xs := W.quotientSourceOccurrence q
      have hizRemaining : iz ∈ W.remainingOccurrences :=
        W.quotientSourceOccurrence_mem_remaining q
      have hizNotSupport : iz ∉ W.partition.support :=
        (W.mem_remainingOccurrences_iff iz).1 hizRemaining
      have hizDisp : W.quotientDisplacement iz = 0 := by
        rw [← W.occurrenceValue_quotientDisplacementSequence q]
        exact (W.mem_quotientFiber_iff 0 q).1 hqZeroFiber
      have hzeroCoset := W.zero_mem_concentrationCoset_of_padded
        hzero hdQpos CQ
      have hizCoset : occurrenceValue xs iz ∈ addCosetFinset L a := by
        dsimp [L, a]
        exact W.source_mem_periodicLiftedCoset_of_displacement
          CQ.K CQ.alpha iz (by simpa [hizDisp] using hzeroCoset)
      have hsupportSubset : W.partition.support ⊆ C := by
        intro i hi
        apply (mem_occurrencesInAddCoset_iff xs L a i).2
        exact (mem_addCosetFinset_iff L a _).1 (by
          dsimp [L, a]
          exact W.support_mem_concentrationLiftedCoset
            hzero hdQpos CQ i hi)
      have hizC : iz ∈ C := by
        apply (mem_occurrencesInAddCoset_iff xs L a iz).2
        exact (mem_addCosetFinset_iff L a _).1 hizCoset
      have hinsert : insert iz W.partition.support ⊆ C := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hizC
        · exact hsupportSubset hi
      have hselectedTwo : 2 ≤ C.card := by
        have hcardInsert := Finset.card_insert_of_notMem hizNotSupport
        have hle := Finset.card_le_card hinsert
        rw [hcardInsert] at hle
        omega
      have hsmall : xs.length - Nat.card (A ⧸ L) = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hwide)
      rw [hsmall]
      simpa using hselectedTwo

theorem OrdinaryGMOClaimBOutput.nonempty_quotientConcentrationPullback
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (CQ : OrdinaryGMOConcentration (W.paddedQuotientRValues hzero)) :
    Nonempty (OrdinaryGMOConcentration xs) :=
  ⟨W.quotientConcentrationPullback hzero hdQpos CQ⟩

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.concentration_canonicalOutside_le
#print axioms GaoLean.OrdinaryGMOClaimBOutput.zero_mem_concentrationCoset_of_padded
#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_sourceOutside_le_concentrationOutside
#print axioms GaoLean.OrdinaryGMOClaimBOutput.quotientConcentrationPullback
