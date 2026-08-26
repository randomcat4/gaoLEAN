import GaoLean.GAOARRankThreeSubgroups

/-!
# Rank-three plane-stabilizer descent

This module closes the second structural-GMO descent inside a cardinality
`q²` stabilizer.  Its non-full branch is transported occurrence-by-occurrence
back to the ambient rank-three source and then split into the zero and line
subgroups exactly as in the manuscript.
-/

namespace GaoLean.ConcreteGDihedral

set_option maxHeartbeats 1000000 in
/-- The reflection-channel second GMO call inside a `q²` plane.  The full
branch cancels the lifted defect.  A non-full branch is either the zero
subgroup (identity padding) or a prime line, where the already checked line
completion theorem applies. -/
theorem hasProductOneSubsequence_of_reflectionPreGMO_rankTwo
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K]
    (hKcard : Nat.card K = q ^ 2) (hKne : K ≠ ⊥) (hKtop : K < ⊤)
    (hplaneGMO : PlusMinusGMOStructuralProvider K)
    (hlineOrdinary : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → OrdinaryGMOPrescribedLengthProvider J q)
    (hlineGMO : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → PlusMinusGMOStructuralProvider J)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (a b : ℕ)
    (ha : a = (reflectionOccurrences s).card)
    (hb : b = (rotationOccurrences s).card)
    (htotal : a + b = 2 * q ^ 3 + (3 * q - 2))
    (hcapacity : b - q + 2 ≤ (rotationOccurrencesIn s K).card)
    (h : ReflectionChannelPreGMOData s (q ^ 3) (3 * q - 2) a b K)
    (htarget : Nat.card K ≤ h.m)
    (hthreshold : h.m + (2 * q - 2) ≤ h.M) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  letI : Fact (Nat.Prime q) := ⟨hqPrime⟩
  let Q := q ^ 3
  let D := 3 * q - 2
  let xs := rotationInCoordinateSequence s K
  have hqpos : 0 < q := hqPrime.pos
  have hq3 : 3 ≤ q := by
    by_contra hqnot
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  have hQcard : Q = Nat.card (PrimeVectorSpace q 3) := by
    simp [Q, PrimeVectorSpace]
  have hDQ : D ≤ Q := by
    have hsq : 3 * q ≤ q ^ 2 := by
      nlinarith [Nat.zero_le (q * (q - 3))]
    have hcube : q ^ 2 ≤ q ^ 3 := by
      nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
    dsimp only [D, Q]
    omega
  have hxslen : xs.length = h.M := by
    calc
      xs.length = (rotationOccurrencesIn s K).card := by
        simp [xs, rotationInCoordinateSequence]
      _ = h.C.card := by rw [h.C_eq]
      _ = h.M := h.Ccard
  have hpm : PlusMinusDavenportAtMost K (2 * q - 1) :=
    squareCard_plusMinusDavenportAtMost_two_mul_sub_one
      q hqPrime hqodd hKcard
  have hthreshold' : h.m + (2 * q - 1) - 1 ≤ xs.length := by
    rw [hxslen]
    omega
  rcases hplaneGMO xs h.m (2 * q - 1) htarget hpm hthreshold' with
      hfull | hnonfull
  · obtain ⟨hout⟩ := hfull (-⟨h.z, h.z_mem⟩ : K)
    exact (ReflectionChannelDirectFullOutput.ofSpectrum h hout).hasProductOneSubsequence
  · obtain ⟨hc⟩ := hnonfull
    let H : AddSubgroup (PrimeVectorSpace q 3) := hc.K.map K.subtype
    let X : Selection s := rotationInSourceSelection s K hc.selected
    have hXcard : X.card = hc.selected.card :=
      card_rotationInSourceSelection s K hc.selected
    have hoddK : Odd (Nat.card K) := by
      rw [hKcard]
      exact hqodd.pow
    have hXsub : X ⊆ rotationOccurrencesIn s H := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjmem : occurrenceValue xs j ∈ hc.K :=
        hc.value_mem_subgroup
          (odd_natCard_quotient_of_odd_natCard hc.K hoddK) j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Finset.mem_filter.mp
          (rotationInSourceOccurrence_mem s K j)).2.1
      · change coordinate
          (occurrenceValue s (rotationInSourceOccurrence s K j)) ∈
            hc.K.map K.subtype
        refine ⟨occurrenceValue xs j, hjmem, ?_⟩
        exact occurrenceValue_rotationInCoordinateSequence s K j
    have hMlower : b - q + 2 ≤ h.M := by
      rw [← h.Ccard, h.C_eq]
      exact hcapacity
    by_cases hHbot : hc.K = ⊥
    · have hHambient : H = ⊥ := by simp [H, hHbot]
      have hquotInternal : Nat.card (K ⧸ hc.K) = q ^ 2 := by
        rw [hHbot]
        calc
          Nat.card (K ⧸ (⊥ : AddSubgroup K)) = Nat.card K :=
            Nat.card_congr QuotientAddGroup.quotientBot.toEquiv
          _ = q ^ 2 := hKcard
      have hXlower : h.M - q ^ 2 + 2 ≤ X.card := by
        rw [hXcard]
        have hcLower := hc.card_lower
        rw [hquotInternal, hxslen] at hcLower
        exact hcLower
      have hq2two : 2 ≤ q ^ 2 := by nlinarith
      have hbotRaw : b - q * q ^ 2 + 2 ≤ X.card :=
        residual_capacity_composition b q (q ^ 2) h.M X.card
          hqPrime.two_le hq2two hMlower hXlower
      have hbotCapacity : b - Q + 2 ≤
          (rotationOccurrencesIn s
            (⊥ : AddSubgroup (PrimeVectorSpace q 3))).card := by
        have hXbot : X ⊆ rotationOccurrencesIn s
            (⊥ : AddSubgroup (PrimeVectorSpace q 3)) := by
          simpa [hHambient] using hXsub
        apply (show b - Q + 2 ≤ X.card by
          simpa [Q, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
            Nat.mul_assoc] using hbotRaw).trans
        exact Finset.card_le_card hXbot
      have hDb : D ≤ b - Q + 2 := by
        have haD' : a ≤ D := by simpa [ha, D] using haD
        dsimp only [Q, D] at htotal ⊢
        omega
      have hbotcard : Nat.card
          (PrimeVectorSpace q 3 ⧸
            (⊥ : AddSubgroup (PrimeVectorSpace q 3))) = Q := by
        calc
          Nat.card
              (PrimeVectorSpace q 3 ⧸
                (⊥ : AddSubgroup (PrimeVectorSpace q 3))) =
              Nat.card (PrimeVectorSpace q 3) :=
            Nat.card_congr QuotientAddGroup.quotientBot.toEquiv
          _ = Q := hQcard.symm
      apply rcStatement_bot_of_smallDavenport s Q D b
        (by
          dsimp only [Q, D]
          omega)
        hQcard hDb hsmallAmbient
      rw [hbotcard]
      exact hbotCapacity
    · have hHcard : Nat.card hc.K = q :=
        natCard_eq_prime_of_ne_bot_of_lt_top_of_square_subgroup_rankThree
          q hqPrime K hKcard hc.K hHbot hc.strict
      have hHambientCard : Nat.card H = q := by
        rw [natCard_map_subtype K hc.K, hHcard]
      have hHltK : H < K := by
        simpa [H] using map_subtype_lt_of_lt_top K hc.K hc.strict
      have hHne : H ≠ ⊥ := by
        intro hzero
        apply hHbot
        apply (AddSubgroup.map_injective K.subtype_injective)
        simpa [H] using hzero
      have hHtop : H < ⊤ := hHltK.trans hKtop
      have hquotInternal : Nat.card (K ⧸ hc.K) = q := by
        have hfactor :=
          AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup hc.K
        rw [hKcard, hHcard] at hfactor
        exact Nat.mul_right_cancel hqpos
          (by simpa [pow_two] using hfactor.symm)
      have hXlower : h.M - q + 2 ≤ X.card := by
        rw [hXcard]
        have hcLower := hc.card_lower
        rw [hquotInternal, hxslen] at hcLower
        exact hcLower
      have hlineRaw : b - q * q + 2 ≤ X.card :=
        residual_capacity_composition b q q h.M X.card
          hqPrime.two_le hqPrime.two_le hMlower hXlower
      have hlineCapacity : b - q ^ 2 + 2 ≤
          (rotationOccurrencesIn s H).card := by
        apply (show b - q ^ 2 + 2 ≤ X.card by
          simpa [pow_two] using hlineRaw).trans
        exact Finset.card_le_card hXsub
      let c := (rotationOccurrencesOutside s H).card
      have hpartition : (rotationOccurrencesIn s H).card + c = b := by
        have hp := card_rotationOccurrencesIn_add_outside s H
        simpa [c, hb] using hp
      have hq2leb : q ^ 2 ≤ b := by
        have haD' : a ≤ D := by simpa [ha, D] using haD
        have htwoQ : 2 * Q ≤ b := by
          dsimp only [Q, D] at haD' ⊢
          omega
        have hq2Q : q ^ 2 ≤ Q := by
          dsimp only [Q]
          have hqone : 1 ≤ q := hqpos
          calc
            q ^ 2 = q ^ 2 * 1 := by omega
            _ ≤ q ^ 2 * q := Nat.mul_le_mul_left _ hqone
            _ = q ^ 3 := by
              simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        exact hq2Q.trans (by omega)
      have hc : c ≤ q ^ 2 - 2 := by
        have hcplus : c + 2 ≤ q ^ 2 := by omega
        exact (Nat.le_sub_iff_add_le (by nlinarith : 2 ≤ q ^ 2)).2 hcplus
      by_cases hspecial : a + c ≤ 2 * q - 1
      · have hinsideThreshold : 2 * Q + q - 1 ≤
            (rotationOccurrencesIn s H).card := by
          dsimp only [Q] at ⊢
          omega
        exact hasProductOneSubsequence_of_insideOrdinaryGMO H Q q hQcard
          (by
            rw [hHambientCard]
            dsimp only [Q]
            nlinarith)
          (hlineOrdinary H hHambientCard) s hinsideThreshold
      · have hspecialLarge : 2 * q ≤
            (reflectionOccurrences s).card + c := by
          rw [← ha]
          omega
        exact rankThree_line_upper q hqPrime hqodd H hHambientCard hHne
          hHtop (hlineGMO H hHambientCard) hsmallAmbient s hlen ha2 haD c
          rfl hc hspecialLarge

set_option maxHeartbeats 1000000 in
/-- Complete `q²`-plane leaf of the first rank-three concentration.  The
small special-count branch is an ordinary prescribed-length GMO call inside
the plane.  The large branch produces a genuine reflection-containing block
in the prime quotient and invokes the checked second descent above. -/
theorem rankThree_plane_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K]
    (hKcard : Nat.card K = q ^ 2) (hKne : K ≠ ⊥)
    (hplaneOrdinary : OrdinaryGMOPrescribedLengthProvider K (2 * q - 1))
    (hplaneGMO : PlusMinusGMOStructuralProvider K)
    (hlineOrdinary : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → OrdinaryGMOPrescribedLengthProvider J q)
    (hlineGMO : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → PlusMinusGMOStructuralProvider J)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2)
    (hconc : MiddleNonfullConcentrationOutput s
      (rotationOccurrences s).card K) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  letI : Fact (Nat.Prime q) := ⟨hqPrime⟩
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  let c := (rotationOccurrencesOutside s K).card
  have hqpos : 0 < q := hqPrime.pos
  have hq3 : 3 ≤ q := by
    by_contra hqnot
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hAodd : Odd (Nat.card A) := by
    rw [← hQcard]
    exact hqodd.pow
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
  have hKtop : K < ⊤ := hconc.proper
  have hquotcard : Nat.card (A ⧸ K) = q := by
    have hfactor := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
    rw [hKcard] at hfactor
    have hAcard : Nat.card A = q ^ 3 := by simp [A, PrimeVectorSpace]
    rw [hAcard] at hfactor
    apply Nat.mul_right_cancel (pow_pos hqpos 2)
    simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      hfactor.symm
  have hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card :=
    hconc.rotationCapacity hAodd
  have hcapacityq : b - q + 2 ≤
      (rotationOccurrencesIn s K).card := by
    simpa only [hquotcard] using hcapacity
  have hpartition : (rotationOccurrencesIn s K).card + c = b := by
    have hp := card_rotationOccurrencesIn_add_outside s K
    simpa [c, b] using hp
  have hqleb : q ≤ b := by
    have haD' : a ≤ D := by simpa [a, D] using haD
    have htwoQ : 2 * Q ≤ b := by omega
    have hqQ : q ≤ Q := by
      dsimp only [Q]
      have hqone : 1 ≤ q := hqpos
      have hq2one : 1 ≤ q ^ 2 := by nlinarith
      calc
        q = q * 1 := by omega
        _ ≤ q * q ^ 2 := Nat.mul_le_mul_left _ hq2one
        _ = q ^ 3 := by simp [pow_succ, Nat.mul_comm]
    exact hqQ.trans (by omega)
  have hc : c ≤ q - 2 := by
    have hcplus : c + 2 ≤ q := by omega
    exact (Nat.le_sub_iff_add_le hqPrime.two_le).2 hcplus
  by_cases hspecial : a + c ≤ q
  · have hinsideThreshold : 2 * Q + (2 * q - 1) - 1 ≤
        (rotationOccurrencesIn s K).card := by
      omega
    exact hasProductOneSubsequence_of_insideOrdinaryGMO K Q (2 * q - 1)
      hQcard
      (by
        rw [hKcard]
        dsimp only [Q]
        nlinarith)
      hplaneOrdinary s hinsideThreshold
  · have hspecialLarge : q < (reflectionOccurrences s).card + c := by
      simpa [a] using (show q < a + c by omega)
    have hchannel : ¬QuotientNoReflection s K := by
      intro hno
      exact hno (hasReflectionContainingQuotientProductOne_of_prime_card
        hqodd K hquotcard s ha2 hspecialLarge)
    have hsmallQuot : QuotientSmallDavenportProductOneFreeAtMost K q :=
      quotientSmallDavenportProductOneFreeAtMost_of_smallDavenport K q
        (smallDavenportProductOneFreeAtMost_of_prime_card hqodd hquotcard)
    have hDqD : q ≤ D := by
      dsimp only [D]
      omega
    obtain ⟨hpre⟩ := exists_reflectionChannelPreGMOData
      s Q D a b q K rfl rfl htotal hDQ
        (by simpa [a, D] using haD) hQcard hcapacity hsmallQuot hDqD hchannel
    have hRsmall : hpre.R.card ≤ q :=
      hsmallQuot s hpre.R hpre.R_free
    have hsplit : D + 1 = (2 * q - 1) + q := by
      dsimp only [D]
      omega
    have htau : 2 * q - 2 ≤ hpre.tau :=
      hpre.tau_ge_of_davenport_split hsplit hRsmall
    have hthreshold : hpre.m + (2 * q - 2) ≤ hpre.M :=
      hpre.signed_reservoir_threshold htau
    have hKpos : (⊥ : AddSubgroup A) < K := bot_lt_iff_ne_bot.mpr hKne
    have htarget : Nat.card K ≤ hpre.m :=
      hpre.target_ge_card_subgroup hQcard hDQ hKpos hKtop hcapacity
        (by simpa [a, D] using haD) htotal
    exact hasProductOneSubsequence_of_reflectionPreGMO_rankTwo
      q hqPrime hqodd K hKcard hKne hKtop hplaneGMO hlineOrdinary hlineGMO
        hsmallAmbient s hlen ha2 haD a b rfl rfl htotal hcapacityq hpre
          htarget hthreshold

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequence_of_reflectionPreGMO_rankTwo
#print axioms GaoLean.ConcreteGDihedral.rankThree_plane_upper
