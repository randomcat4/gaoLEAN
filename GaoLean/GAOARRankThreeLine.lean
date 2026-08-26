import GaoLean.GAOARRankThreeQuotient
import GaoLean.GAOAROneTranslation

/-!
# Rank-three line completion

This module assembles the reflection-containing quotient alternative of the
line-completion lemma.  The quotient small-Davenport bound is kept visible at
this stage and will be discharged by the manuscript's complement-lifting
argument in a separate theorem.
-/

namespace GaoLean.ConcreteGDihedral

/-- Convert fixed-cardinality coverage in the line-coordinate list into the
exact source-labelled exchange interface used by quotient extraction. -/
theorem fullExactExchange_rotationInCoordinateSequence
    {A : Type*} [AddCommGroup A] [Fintype A]
    (s : List (Group A)) (J : AddSubgroup A) (d : ℕ)
    (hfill : ∀ y : J,
      ∃ I : Selection (rotationInCoordinateSequence s J),
        I.card = d ∧ ∑ i ∈ I,
          occurrenceValue (rotationInCoordinateSequence s J) i = y) :
    FullExactExchange s (rotationOccurrencesIn s J) J d := by
  classical
  intro y hy
  obtain ⟨I, hIcard, hIsum⟩ := hfill ⟨y, hy⟩
  let D : Selection s := rotationInSourceSelection s J I
  refine ⟨D, rotationInSourceSelection_subset s J I, ?_, ?_⟩
  · simpa [D] using card_rotationInSourceSelection s J I |>.trans hIcard
  · have hsumA := congrArg Subtype.val hIsum
    unfold coordinateSum
    dsimp only [D]
    rw [rotationInSourceSelection, Finset.sum_image]
    · simpa [occurrenceValue_rotationInCoordinateSequence] using hsumA
    · intro i hi j hj hij
      exact rotationInSourceOccurrence_injective s J hij

/-- Send an inside-line coordinate occurrence directly to the same labelled
position in a translated source list. -/
noncomputable def rotationInTranslatedOccurrenceEmbedding
    {A : Type*} [AddCommGroup A] [Fintype A]
    (α : A) (s : List (Group A)) (J : AddSubgroup A) :
    Occurrence (rotationInCoordinateSequence s J) ↪
      Occurrence (translatedSequence α s) where
  toFun i := translatedOccurrenceEquiv α s
    (rotationInSourceOccurrence s J i)
  inj' := (translatedOccurrenceEquiv α s).injective.comp
    (rotationInSourceOccurrence_injective s J)

@[simp] theorem rotationInTranslatedOccurrenceEmbedding_apply
    {A : Type*} [AddCommGroup A] [Fintype A]
    (α : A) (s : List (Group A)) (J : AddSubgroup A)
    (i : Occurrence (rotationInCoordinateSequence s J)) :
    rotationInTranslatedOccurrenceEmbedding α s J i =
      translatedOccurrenceEquiv α s (rotationInSourceOccurrence s J i) := rfl

/-- Reflection-containing quotient alternative of rank-three line
completion, including maximum extraction and signed kernel lifting. -/
theorem rankThree_line_reflectionChannel_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J]
    (hJcard : Nat.card J = q) (hJne : J ≠ ⊥) (hJtop : J < ⊤)
    (hlineGMO : PlusMinusGMOStructuralProvider J)
    (hsmallQuot : QuotientSmallDavenportProductOneFreeAtMost J (2 * q - 1))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (c : ℕ) (houtside : (rotationOccurrencesOutside s J).card = c)
    (hc : c ≤ q ^ 2 - 2)
    (hchannel : ¬QuotientNoReflection s J)
    (hnonzero : q - 1 ≤
      (nonzeroOccurrences (rotationInCoordinateSequence s J)).card) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := hqPrime.pos
  have hq3 : 3 ≤ q := by
    by_contra h
    have hq2 : 2 ≤ q := hqPrime.two_le
    have hqeq : q = 2 := by omega
    rw [hqeq] at hqodd
    norm_num at hqodd
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hDQ : D ≤ Q := by
    have hqminus3 : q - 3 + 3 = q := Nat.sub_add_cancel hq3
    have hsq : 3 * q ≤ q ^ 2 := by
      nlinarith [Nat.zero_le (q * (q - 3))]
    have hcube : q ^ 2 ≤ q ^ 3 := by
      nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
    dsimp only [D, Q]
    omega
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    dsimp only [Q, D]
    omega
  have hquotcard : Nat.card (A ⧸ J) = q ^ 2 := by
    have hfactor := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup J
    rw [hJcard] at hfactor
    have hAcard : Nat.card A = q ^ 3 := by simp [A, PrimeVectorSpace]
    rw [hAcard] at hfactor
    apply Nat.mul_right_cancel hqpos
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hfactor.symm
  have hCplus : (rotationOccurrencesIn s J).card + c = b := by
    have hpart := card_rotationOccurrencesIn_add_outside s J
    rw [houtside] at hpart
    simpa [b] using hpart
  have hq2Q : q ^ 2 ≤ Q := by
    dsimp only [Q]
    nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
  have htwoQb : 2 * Q ≤ b := by
    have haD' : a ≤ D := by simpa [a, D] using haD
    omega
  have hq2b : q ^ 2 ≤ b := le_trans hq2Q (by omega)
  have hcapacity : b - Nat.card (A ⧸ J) + 2 ≤
      (rotationOccurrencesIn s J).card := by
    rw [hquotcard]
    have hq2 : 2 ≤ q ^ 2 := by nlinarith
    have hc' : c + 2 ≤ q ^ 2 :=
      (Nat.le_sub_iff_add_le hq2).mp hc
    omega
  have hDqD : 2 * q - 1 ≤ D := by
    dsimp only [D]
    omega
  obtain ⟨hpre⟩ := exists_reflectionChannelPreGMOData
    s Q D a b (2 * q - 1) J rfl rfl htotal hDQ
      (by simpa [a, D] using haD) hQcard hcapacity hsmallQuot hDqD
        hchannel
  have hRsmall : hpre.R.card ≤ 2 * q - 1 :=
    hsmallQuot s hpre.R hpre.R_free
  have hsplit : D + 1 = q + (2 * q - 1) := by
    dsimp only [D]
    omega
  have htauLower : q - 1 ≤ hpre.tau :=
    hpre.tau_ge_of_davenport_split hsplit hRsmall
  have hJpos : (⊥ : AddSubgroup A) < J := bot_lt_iff_ne_bot.mpr hJne
  have htarget : Nat.card J ≤ hpre.m :=
    hpre.target_ge_card_subgroup hQcard hDQ hJpos hJtop hcapacity
      (by simpa [a, D] using haD) htotal
  have hxslen : (rotationInCoordinateSequence s J).length = hpre.M := by
    calc
      (rotationInCoordinateSequence s J).length =
          (rotationOccurrencesIn s J).card := by
        simp [rotationInCoordinateSequence]
      _ = hpre.C.card := by rw [hpre.C_eq]
      _ = hpre.M := hpre.Ccard
  have htauUpper : hpre.tau ≤
      (rotationInCoordinateSequence s J).length := by
    rw [hxslen]
    exact hpre.tau_le_M
  have hm : (rotationInCoordinateSequence s J).length - hpre.tau =
      hpre.m := by
    rw [hxslen, hpre.m_eq]
  obtain ⟨hout⟩ := primeLine_signedLifting_of_structuralGMO
    q hqPrime hqodd hJcard hlineGMO (rotationInCoordinateSequence s J)
      hpre.tau htauLower htauUpper (by simpa [hm] using htarget)
        hnonzero (-⟨hpre.z, hpre.z_mem⟩ : J)
  have hout' : HasPlusMinusSumOfCard (rotationInCoordinateSequence s J)
      hpre.m (-⟨hpre.z, hpre.z_mem⟩ : J) := by
    simpa [hm] using hout
  exact (ReflectionChannelDirectFullOutput.ofSpectrum hpre hout').hasProductOneSubsequence

/-- Reflection-containing branch with the quotient bound discharged from the
ambient small-Davenport theorem by complement lifting. -/
theorem rankThree_line_reflectionChannel_upper_of_ambient
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J]
    (hJcard : Nat.card J = q) (hJne : J ≠ ⊥) (hJtop : J < ⊤)
    (hlineGMO : PlusMinusGMOStructuralProvider J)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (c : ℕ) (houtside : (rotationOccurrencesOutside s J).card = c)
    (hc : c ≤ q ^ 2 - 2)
    (hchannel : ¬QuotientNoReflection s J)
    (hnonzero : q - 1 ≤
      (nonzeroOccurrences (rotationInCoordinateSequence s J)).card) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  exact rankThree_line_reflectionChannel_upper q hqPrime hqodd J hJcard
    hJne hJtop hlineGMO
    (rankThree_quotientSmallDavenportProductOneFreeAtMost_of_ambient
      q hqPrime J hJne hsmallAmbient)
    s hlen ha2 haD c houtside hc hchannel hnonzero

set_option maxHeartbeats 1000000 in
/-- The no-reflection quotient alternative of the rank-three line lemma.
The fixed-cardinality branch is closed by exact exchange; the concentrated
heavy-value branch is translated once and closed by the checked zero-layer
identity-padding theorem. -/
theorem rankThree_line_noReflection_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J]
    (hJcard : Nat.card J = q) (hJne : J ≠ ⊥)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (c : ℕ) (houtside : (rotationOccurrencesOutside s J).card = c)
    (hc : c ≤ q ^ 2 - 2)
    (hguard : QuotientNoReflection s J) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hq3 : 3 ≤ q := by
    by_contra h
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hDQ : D ≤ Q := by
    have hsq : 3 * q ≤ q ^ 2 := by
      nlinarith [Nat.zero_le (q * (q - 3))]
    have hcube : q ^ 2 ≤ q ^ 3 := by
      nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
    dsimp only [D, Q]
    omega
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    dsimp only [Q, D]
    omega
  have htwoQb : 2 * Q ≤ b := by
    have haD' : a ≤ D := by simpa [a, D] using haD
    omega
  have hquotcard : Nat.card (A ⧸ J) = q ^ 2 := by
    have hfactor := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup J
    rw [hJcard] at hfactor
    have hAcard : Nat.card A = q ^ 3 := by simp [A, PrimeVectorSpace]
    rw [hAcard] at hfactor
    apply Nat.mul_right_cancel hqPrime.pos
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      hfactor.symm
  have hCplus : (rotationOccurrencesIn s J).card + c = b := by
    have hpart := card_rotationOccurrencesIn_add_outside s J
    rw [houtside] at hpart
    simpa [b] using hpart
  have hq2 : 2 ≤ q ^ 2 := by nlinarith
  have hc' : c + 2 ≤ q ^ 2 :=
    (Nat.le_sub_iff_add_le hq2).mp hc
  have hq2Q : q ^ 2 ≤ Q := by
    dsimp only [Q]
    nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
  have hq2b : q ^ 2 ≤ b := le_trans hq2Q (by omega)
  have hcapacity : b - Nat.card (A ⧸ J) + 2 ≤
      (rotationOccurrencesIn s J).card := by
    rw [hquotcard]
    omega
  have hsmallQuot : QuotientSmallDavenportProductOneFreeAtMost J
      (2 * q - 1) :=
    rankThree_quotientSmallDavenportProductOneFreeAtMost_of_ambient
      q hqPrime J hJne hsmallAmbient
  have hDqD : 2 * q - 1 ≤ D := by
    dsimp only [D]
    omega
  obtain ⟨hpre⟩ := exists_rotationChannelPreGMOData
    s Q D a b (2 * q - 1) J htotal rfl rfl hsmallQuot hDqD
      hQcard hcapacity hguard
  let xs := rotationInCoordinateSequence s J
  have hxslen : xs.length = hpre.M := by
    calc
      xs.length = (rotationOccurrencesIn s J).card := by
        simp [xs, rotationInCoordinateSequence]
      _ = hpre.C.card := by rw [hpre.C_eq]
      _ = hpre.M := hpre.Ccard
  have hMlower : 2 * q ^ 3 - q ^ 2 + 2 ≤ xs.length := by
    rw [hxslen, ← hpre.Ccard, hpre.C_eq]
    dsimp only [Q] at htwoQb
    omega
  have hfreeBound : a + hpre.B0.card ≤ 2 * q - 1 :=
    hpre.free_remainder_bound rfl hsmallQuot hguard
  have hsplit : D + 1 = q + (2 * q - 1) := by
    dsimp only [D]
    omega
  have hdLower : q - 1 ≤ hpre.d :=
    hpre.defect_ge_of_davenport_split q (2 * q - 1) hsplit hfreeBound
  have hdUpper : hpre.d ≤ 3 * q - 4 := by
    rw [hpre.d_eq]
    have ha2' : 2 ≤ a := by simpa [a] using ha2
    dsimp only [D]
    omega
  obtain ⟨g, _hglarge, hconcentrated | hfill⟩ :=
    primeLine_heavyValue_or_fixedCardinalitySums q hqPrime hqodd
      hJcard xs hMlower
  · let α : A := (g : A)
    let emb : Occurrence xs ↪ Occurrence (translatedSequence α s) :=
      rotationInTranslatedOccurrenceEmbedding α s J
    let identities : Selection (translatedSequence α s) :=
      (valueOccurrences xs g).map emb
    have hidentitiesCard : identities.card = (valueOccurrences xs g).card := by
      simp [identities]
    have hidentitiesSub : identities ⊆
        rotationOccurrencesIn (translatedSequence α s) ⊥ := by
      intro i hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
      apply (mem_rotationOccurrencesIn_bot_iff_eq_one _ _).2
      apply (isRotation_and_coordinate_eq_zero_iff_eq_one _).mp
      constructor
      · change IsRotation (occurrenceValue (translatedSequence α s)
          (translatedOccurrenceEquiv α s
            (rotationInSourceOccurrence s J j)))
        rw [occurrenceValue_translatedSequence]
        exact (isRotation_translateRotations_iff α _).2
          ((Finset.mem_filter.mp
            (rotationInSourceOccurrence_mem s J j)).2.1)
      · change coordinate (occurrenceValue (translatedSequence α s)
          (translatedOccurrenceEquiv α s
            (rotationInSourceOccurrence s J j))) = 0
        rw [occurrenceValue_translatedSequence,
          coordinate_translateRotations]
        · have hjval : occurrenceValue xs j = g := by
            simpa [valueOccurrences] using hj
          have hcoord := occurrenceValue_rotationInCoordinateSequence s J j
          rw [hjval] at hcoord
          change ((g : J) : A) = _ at hcoord
          dsimp only [α]
          rw [← hcoord]
          simp
        · exact (Finset.mem_filter.mp
            (rotationInSourceOccurrence_mem s J j)).2.1
    have hvalueOther := card_valueOccurrences_add_card_otherValueOccurrences xs g
    have hcotherQ : c + (otherValueOccurrences xs g).card + 2 ≤ Q := by
      have hpoly : q ^ 2 + q ≤ q ^ 3 := by
        have hqle : q ≤ q ^ 2 := by
          nlinarith [Nat.zero_le (q * (q - 1))]
        have htwo : 2 * q ^ 2 ≤ q ^ 3 := by
          nlinarith [Nat.zero_le ((q - 2) * q ^ 2)]
        omega
      dsimp only [Q]
      omega
    have hbotCapacity : b - Q + 2 ≤
        (rotationOccurrencesIn (translatedSequence α s) ⊥).card := by
      apply (show b - Q + 2 ≤ identities.card by
        rw [hidentitiesCard]
        have hvalueOther' : (valueOccurrences xs g).card +
            (otherValueOccurrences xs g).card = hpre.M := by
          rw [hvalueOther, hxslen]
        have hMC : hpre.M = (rotationOccurrencesIn s J).card := by
          rw [← hpre.Ccard, hpre.C_eq]
        omega).trans
      exact Finset.card_le_card hidentitiesSub
    have hQb : Q ≤ b := by omega
    have hDb : D ≤ b - Q + 2 := by omega
    have hZR : ConcreteZRStatement (translatedSequence α s) Q D a b ⊥ :=
      concreteZRStatement_bot_of_smallDavenport
        (translatedSequence α s) Q D a b hQcard hDb hsmallAmbient
    have hbotCapacity' : b - Nat.card
        (PrimeVectorSpace q 3 ⧸
          (⊥ : AddSubgroup (PrimeVectorSpace q 3))) + 2 ≤
        (rotationOccurrencesIn (translatedSequence α s) ⊥).card := by
      have hbotcard : Nat.card
          (PrimeVectorSpace q 3 ⧸
            (⊥ : AddSubgroup (PrimeVectorSpace q 3))) = Q := by
        calc
          _ = Nat.card (PrimeVectorSpace q 3) :=
            Nat.card_congr QuotientAddGroup.quotientBot.toEquiv
          _ = Q := by simp [Q, PrimeVectorSpace]
      rw [hbotcard]
      exact hbotCapacity
    have hlen' : s.length = 2 * Q + D := by
      dsimp only [Q, D]
      omega
    obtain ⟨I, hIcard, hIprod, _hIrot⟩ :=
      hasAllRotationProductOneSubsequence_of_concreteZR_translatedSequence
        α s Q D a b ⊥ J hZR
        hlen' rfl rfl hbotCapacity' bot_le
        g.property hguard hQcard
    exact ⟨I, hIcard, hIprod⟩
  · have hexchange : FullExactExchange s hpre.C J hpre.d := by
      rw [hpre.C_eq]
      apply fullExactExchange_rotationInCoordinateSequence
      intro y
      exact hfill hpre.d hdLower hdUpper y
    obtain ⟨I, hIcard, hIprod, _hIrot⟩ :=
      hasAllRotationProductOneSubsequence_of_preGMOFullExactExchange
        s Q D a b J hpre hexchange
    exact ⟨I, hIcard, hIprod⟩

/-- Initial line-completion leaf: at most `q-2` nonzero rotations in the line
leave enough literal identity rotations for the ambient greedy core and exact
padding. -/
theorem rankThree_line_fewNonzero_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J]
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (c : ℕ) (houtside : (rotationOccurrencesOutside s J).card = c)
    (hc : c ≤ q ^ 2 - 2)
    (hfew : (nonzeroOccurrences
      (rotationInCoordinateSequence s J)).card ≤ q - 2) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  let xs := rotationInCoordinateSequence s J
  have hq3 : 3 ≤ q := by
    by_contra h
    have hq2prime : 2 ≤ q := hqPrime.two_le
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  have hQcard : Q = Nat.card A := by simp [Q, A, PrimeVectorSpace]
  have hDQ : D ≤ Q := by
    have hsq : 3 * q ≤ q ^ 2 := by
      nlinarith [Nat.zero_le (q * (q - 3))]
    have hcube : q ^ 2 ≤ q ^ 3 := by
      nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
    dsimp only [D, Q]
    omega
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    dsimp only [Q, D]
    omega
  have htwoQb : 2 * Q ≤ b := by
    have haD' : a ≤ D := by simpa [a, D] using haD
    omega
  have hCplus : xs.length + c = b := by
    have hpart := card_rotationOccurrencesIn_add_outside s J
    rw [houtside] at hpart
    simpa [xs, rotationInCoordinateSequence, b] using hpart
  let identities : Selection s :=
    rotationInSourceSelection s J (zeroOccurrences xs)
  have hidentitiesCard : identities.card = (zeroOccurrences xs).card :=
    card_rotationInSourceSelection s J (zeroOccurrences xs)
  have hidentitiesSub : identities ⊆ rotationOccurrencesIn s ⊥ := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    apply (mem_rotationOccurrencesIn_bot_iff_eq_one _ _).2
    apply (isRotation_and_coordinate_eq_zero_iff_eq_one _).mp
    constructor
    · exact (Finset.mem_filter.mp
        (rotationInSourceOccurrence_mem s J j)).2.1
    · have hjzero : occurrenceValue xs j = 0 := by
        simpa [zeroOccurrences] using hj
      have hcoord := occurrenceValue_rotationInCoordinateSequence s J j
      change ((occurrenceValue xs j : J) : A) = _ at hcoord
      rw [hjzero] at hcoord
      simpa using hcoord.symm
  have hparts := card_nonzeroOccurrences_add_card_zeroOccurrences xs
  have hfew' : (nonzeroOccurrences xs).card ≤ q - 2 := by
    simpa [xs] using hfew
  have hcsmall : c + (nonzeroOccurrences xs).card + 2 ≤ Q := by
    have hq2 : 2 ≤ q ^ 2 := by nlinarith
    have hc' : c + 2 ≤ q ^ 2 :=
      (Nat.le_sub_iff_add_le hq2).mp hc
    have hpoly : q ^ 2 + q ≤ q ^ 3 := by
      have hqle : q ≤ q ^ 2 := by
        nlinarith [Nat.zero_le (q * (q - 1))]
      have htwo : 2 * q ^ 2 ≤ q ^ 3 := by
        nlinarith [Nat.zero_le ((q - 2) * q ^ 2)]
      omega
    dsimp only [Q]
    omega
  have hidentityCapacity : b - Q + 2 ≤ identities.card := by
    rw [hidentitiesCard]
    omega
  have hQb : Q ≤ b := by omega
  have hDb : D ≤ b - Q + 2 := by omega
  have hRC : RCStatement s Q b ⊥ :=
    rcStatement_bot_of_smallDavenport s Q D b
      (by
        dsimp only [Q, D]
        omega)
      hQcard hDb hsmallAmbient
  have hbotcard : Nat.card
      (PrimeVectorSpace q 3 ⧸
        (⊥ : AddSubgroup (PrimeVectorSpace q 3))) = Q := by
    calc
      _ = Nat.card (PrimeVectorSpace q 3) :=
        Nat.card_congr QuotientAddGroup.quotientBot.toEquiv
      _ = Q := by simp [Q, PrimeVectorSpace]
  apply hRC
  rw [hbotcard]
  exact hidentityCapacity.trans (Finset.card_le_card hidentitiesSub)

/-- Complete rank-three line-completion lemma, with the manuscript's line
hypotheses and both quotient alternatives assembled. -/
theorem rankThree_line_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J]
    (hJcard : Nat.card J = q) (hJne : J ≠ ⊥) (hJtop : J < ⊤)
    (hlineGMO : PlusMinusGMOStructuralProvider J)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (c : ℕ) (houtside : (rotationOccurrencesOutside s J).card = c)
    (hc : c ≤ q ^ 2 - 2)
    (_hspecial : 2 * q ≤ (reflectionOccurrences s).card + c) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  let xs := rotationInCoordinateSequence s J
  by_cases hfew : (nonzeroOccurrences xs).card ≤ q - 2
  · exact rankThree_line_fewNonzero_upper q hqPrime hqodd J hsmallAmbient
      s hlen haD c houtside hc (by simpa [xs] using hfew)
  · have hnonzero : q - 1 ≤ (nonzeroOccurrences xs).card := by omega
    by_cases hguard : QuotientNoReflection s J
    · exact rankThree_line_noReflection_upper q hqPrime hqodd J hJcard
        hJne hsmallAmbient s hlen ha2 haD c houtside hc hguard
    · exact rankThree_line_reflectionChannel_upper_of_ambient q hqPrime hqodd
        J hJcard hJne hJtop hlineGMO hsmallAmbient s hlen ha2 haD c
        houtside hc hguard (by simpa [xs] using hnonzero)

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.rankThree_line_reflectionChannel_upper
#print axioms GaoLean.ConcreteGDihedral.rankThree_line_reflectionChannel_upper_of_ambient
#print axioms GaoLean.ConcreteGDihedral.rankThree_line_noReflection_upper
#print axioms GaoLean.ConcreteGDihedral.rankThree_line_fewNonzero_upper
#print axioms GaoLean.ConcreteGDihedral.rankThree_line_upper
