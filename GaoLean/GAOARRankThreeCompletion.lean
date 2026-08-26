import GaoLean.GAOARRankThreePlane

/-!
# Complete rank-three GAO-AR upper bound

This module reconnects the checked line and plane leaves to the first
structural-GMO concentration, then assembles the low, middle, and high
reflection ranges.  Every cited literature theorem remains an explicit
proposition parameter.
-/

namespace GaoLean

open ConcreteGDihedral

set_option maxHeartbeats 1000000 in
/-- Complete middle-reflection range in rank three. -/
theorem rankThree_middle_upper
    (q dpm : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hdpm : dpm ≤ 3 * q - 2)
    (hpm : PlusMinusDavenportAtMost (PrimeVectorSpace q 3) dpm)
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 3))
    (hlineOrdinary : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → OrdinaryGMOPrescribedLengthProvider J q)
    (hlineGMO : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → PlusMinusGMOStructuralProvider J)
    (hplaneOrdinary : ∀ (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K],
      Nat.card K = q ^ 2 →
        OrdinaryGMOPrescribedLengthProvider K (2 * q - 1))
    (hplaneGMO : ∀ (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K],
      Nat.card K = q ^ 2 → PlusMinusGMOStructuralProvider K)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  classical
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
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
  have hlen' : s.length = 2 * Q + D := by
    dsimp only [Q, D]
    omega
  rcases rankThree_middle_full_or_concentrated q dpm hqPrime hqodd hdpm
      hpm hGMO s hlen ha2 haD with hfull | hnonfull
  · exact hfull
  · obtain ⟨K, ⟨hconc⟩⟩ := hnonfull
    by_cases hKbot : K = ⊥
    · subst K
      exact hasProductOneSubsequenceOfTwice_of_middleNonfull_bot
        s Q D a b hlen' hQcard hDQ (by simpa [a, D] using haD)
          htotal hAodd hsmall hconc
    · rcases natCard_eq_prime_or_square_of_ne_bot_of_lt_top_rankThree
          q hqPrime K hKbot hconc.proper with hKline | hKplane
      · let c := (rotationOccurrencesOutside s K).card
        have hquotcard : Nat.card (PrimeVectorSpace q 3 ⧸ K) = q ^ 2 := by
          have hfactor :=
            AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
          rw [hKline] at hfactor
          have hAcard : Nat.card (PrimeVectorSpace q 3) = q ^ 3 := by
            simp [PrimeVectorSpace]
          rw [hAcard] at hfactor
          apply Nat.mul_right_cancel hqpos
          simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            hfactor.symm
        have hcapacity : b - q ^ 2 + 2 ≤
            (rotationOccurrencesIn s K).card := by
          have hcapa := hconc.rotationCapacity hAodd
          simpa only [hquotcard] using hcapa
        have hpartition : (rotationOccurrencesIn s K).card + c = b := by
          have hp := card_rotationOccurrencesIn_add_outside s K
          simpa [c, b] using hp
        have hq2leb : q ^ 2 ≤ b := by
          have haD' : a ≤ D := by simpa [a, D] using haD
          have htwoQ : 2 * Q ≤ b := by omega
          have hq2Q : q ^ 2 ≤ Q := by
            dsimp only [Q]
            have hqone : 1 ≤ q := hqpos
            calc
              q ^ 2 = q ^ 2 * 1 := by omega
              _ ≤ q ^ 2 * q := Nat.mul_le_mul_left _ hqone
              _ = q ^ 3 := by simp [pow_succ, Nat.mul_comm]
          exact hq2Q.trans (by omega)
        have hc : c ≤ q ^ 2 - 2 := by
          have hcplus : c + 2 ≤ q ^ 2 := by omega
          exact (Nat.le_sub_iff_add_le (by nlinarith : 2 ≤ q ^ 2)).2 hcplus
        by_cases hspecial : a + c ≤ 2 * q - 1
        · have hinsideThreshold : 2 * Q + q - 1 ≤
              (rotationOccurrencesIn s K).card := by omega
          exact hasProductOneSubsequence_of_insideOrdinaryGMO K Q q hQcard
            (by
              rw [hKline]
              dsimp only [Q]
              nlinarith)
            (hlineOrdinary K hKline) s hinsideThreshold
        · have hspecialLarge : 2 * q ≤
              (reflectionOccurrences s).card + c := by
            rw [← show a = (reflectionOccurrences s).card from rfl]
            omega
          exact rankThree_line_upper q hqPrime hqodd K hKline hKbot
            hconc.proper (hlineGMO K hKline) hsmall s hlen ha2 haD c rfl hc
              hspecialLarge
      · exact rankThree_plane_upper q hqPrime hqodd K hKplane hKbot
          (hplaneOrdinary K hKplane) (hplaneGMO K hKplane)
            hlineOrdinary hlineGMO hsmall s hlen ha2 haD hconc

set_option maxHeartbeats 1000000 in
/-- Complete rank-three upper bound at the manuscript threshold. -/
theorem rankThree_upper
    (q dpm : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hdpmHigh : dpm ≤ (3 * q - 1) / 2)
    (hpm : PlusMinusDavenportAtMost (PrimeVectorSpace q 3) dpm)
    (hordinary : OrdinaryGMOPrescribedLengthProvider
      (PrimeVectorSpace q 3) (3 * q - 2))
    (hweighted : WeightedGMOPrescribedLengthProvider
      (PrimeVectorSpace q 3))
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 3))
    (hlineOrdinary : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → OrdinaryGMOPrescribedLengthProvider J q)
    (hlineGMO : ∀ (J : AddSubgroup (PrimeVectorSpace q 3)) [Fintype J],
      Nat.card J = q → PlusMinusGMOStructuralProvider J)
    (hplaneOrdinary : ∀ (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K],
      Nat.card K = q ^ 2 →
        OrdinaryGMOPrescribedLengthProvider K (2 * q - 1))
    (hplaneGMO : ∀ (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K],
      Nat.card K = q ^ 2 → PlusMinusGMOStructuralProvider K)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  let a := (reflectionOccurrences s).card
  by_cases hlow : a ≤ 1
  · exact rankThree_lowReflection_upper q hordinary s hlen hlow
  by_cases hhigh : 3 * q - 1 ≤ a
  · exact rankThree_highReflection_upper q dpm hqPrime hqodd hdpmHigh hpm
      hweighted s hlen hhigh
  have ha2 : 2 ≤ (reflectionOccurrences s).card := by
    dsimp only [a] at hlow ⊢
    omega
  have haD : (reflectionOccurrences s).card ≤ 3 * q - 2 := by
    dsimp only [a] at hhigh ⊢
    omega
  have hdpmMiddle : dpm ≤ 3 * q - 2 := by
    exact hdpmHigh.trans (by
      have hqpos : 0 < q := hqPrime.pos
      omega)
  exact rankThree_middle_upper q dpm hqPrime hqodd hdpmMiddle hpm hGMO
    hlineOrdinary hlineGMO hplaneOrdinary hplaneGMO hsmall s hlen ha2 haD

end GaoLean

#print axioms GaoLean.rankThree_middle_upper
#print axioms GaoLean.rankThree_upper
