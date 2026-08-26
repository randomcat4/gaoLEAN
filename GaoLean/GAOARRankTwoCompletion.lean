import GaoLean.GAOARRankTwo
import GaoLean.GAOARRankTwoLineLarge

/-!
# Complete rank-two GAO-AR upper bound

This module assembles the two outer reflection ranges, the first structural
GMO split in the middle range, the zero-subgroup base, and the two proved
concentrated-line leaves.  All literature inputs remain explicit proposition
parameters.
-/

namespace GaoLean

open ConcreteGDihedral

/-- Complete middle-reflection range for the rank-two prime vector space. -/
theorem rankTwo_middle_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 2))
    (hlineOrdinary : ∀
      (K : AddSubgroup (PrimeVectorSpace q 2)) [Fintype K],
      OrdinaryGMOPrescribedLengthProvider K q)
    (hlineGMO : ∀
      (K : AddSubgroup (PrimeVectorSpace q 2)) [Fintype K],
      PlusMinusGMOStructuralProvider K)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 2) (2 * (q - 1) + 1))
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 2 * (q - 1) + 1) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 2) := by
  classical
  let A := PrimeVectorSpace q 2
  let Q := q ^ 2
  let D := 2 * (q - 1) + 1
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := hqPrime.pos
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hAodd : Odd (Nat.card A) := by
    rw [← hQcard]
    exact hqodd.pow
  have hDQ : D ≤ Q := by
    have hqm1 : q - 1 + 1 = q := Nat.sub_add_cancel hqpos
    dsimp only [D, Q]
    nlinarith [sq_nonneg (q - 1)]
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    simp [Q, D, Nat.add_assoc]
  have hlen' : s.length = 2 * Q + D := by
    calc
      s.length = 2 * q ^ 2 + 2 * (q - 1) + 1 := hlen
      _ = 2 * Q + D := by simp [Q, D, Nat.add_assoc]
  rcases rankTwo_middleSpectrumAlternative q hqPrime hqodd hGMO s hlen
      ha2 haD with hfull | hnonfull
  · obtain ⟨hout⟩ := hfull
    exact hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput
      s Q D a hDQ (by simpa [a] using ha2) (by simpa [a, D] using haD)
        hout
  · obtain ⟨K, hK⟩ := hnonfull
    obtain ⟨hconc⟩ := hK
    by_cases hKbot : K = ⊥
    · subst K
      exact hasProductOneSubsequenceOfTwice_of_middleNonfull_bot
        s Q D a b hlen' hQcard hDQ (by simpa [a, D] using haD)
          htotal hAodd hsmall hconc
    · have hKcard : Nat.card K = q :=
        natCard_eq_prime_of_ne_bot_of_lt_top_rankTwo
          q hqPrime K hKbot hconc.proper
      by_cases hspecial : (lineSpecialOccurrences s K).card ≤ q
      · exact rankTwo_line_smallSpecial_upper q K hKcard
          (hlineOrdinary K) s hlen hspecial
      · exact rankTwo_line_largeSpecial_upper q hqPrime hqodd hlineGMO
          hsmall s hlen ha2 haD K hKbot hconc (by omega)

/-- Complete rank-two upper bound at the manuscript threshold, with exactly
the named ordinary/weighted/structural GMO and small-Davenport inputs. -/
theorem rankTwo_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hordinary : OrdinaryGMOPrescribedLengthProvider
      (PrimeVectorSpace q 2) (2 * (q - 1) + 1))
    (hweighted : WeightedGMOPrescribedLengthProvider
      (PrimeVectorSpace q 2))
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 2))
    (hlineOrdinary : ∀
      (K : AddSubgroup (PrimeVectorSpace q 2)) [Fintype K],
      OrdinaryGMOPrescribedLengthProvider K q)
    (hlineGMO : ∀
      (K : AddSubgroup (PrimeVectorSpace q 2)) [Fintype K],
      PlusMinusGMOStructuralProvider K)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 2) (2 * (q - 1) + 1))
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 2) := by
  let a := (reflectionOccurrences s).card
  by_cases hlow : a ≤ 1
  · exact rankTwo_lowReflection_upper q hordinary s hlen hlow
  by_cases hhigh : 2 * q ≤ a
  · exact rankTwo_highReflection_upper q hqPrime hqodd hweighted s hlen hhigh
  have ha2 : 2 ≤ (reflectionOccurrences s).card := by
    dsimp only [a] at hlow ⊢
    omega
  have haD : (reflectionOccurrences s).card ≤ 2 * (q - 1) + 1 := by
    have hqpos : 0 < q := hqPrime.pos
    dsimp only [a] at hhigh ⊢
    omega
  exact rankTwo_middle_upper q hqPrime hqodd hGMO hlineOrdinary
    hlineGMO hsmall s hlen ha2 haD

end GaoLean

#print axioms GaoLean.rankTwo_middle_upper
#print axioms GaoLean.rankTwo_upper
