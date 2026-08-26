import GaoLean.GAOARRankTwoCompletion

/-!
# Rank-three outer ranges and first stabilizer descent

The occurrence and ordering mechanisms are rank-independent.  This module
specializes them to `F_q^3`, closes the two outer reflection ranges, and
formalizes the first structural-GMO alternative in the middle range.  The
published plus-minus Davenport bound for `F_q^3` remains an explicit input.
-/

namespace GaoLean

open ConcreteGDihedral

/-- Rank-three low-reflection leaf. -/
theorem rankThree_lowReflection_upper
    (q : ℕ) [NeZero q]
    (hordinary : OrdinaryGMOPrescribedLengthProvider
      (PrimeVectorSpace q 3) (3 * q - 2))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (hlow : (reflectionOccurrences s).card ≤ 1) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := NeZero.pos q
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    dsimp only [Q, D]
    omega
  obtain ⟨hout⟩ := exists_lowReflectionTargetOutput_of_ordinaryGMO
    s Q D a b hQcard rfl htotal hlow hordinary
  exact hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
    s Q hQcard hout

/-- Rank-three high-reflection leaf, conditional exactly on the cited
plus-minus Davenport bound and weighted prescribed-length GMO theorem. -/
theorem rankThree_highReflection_upper
    (q dpm : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hdpm : dpm ≤ (3 * q - 1) / 2)
    (hpm : PlusMinusDavenportAtMost (PrimeVectorSpace q 3) dpm)
    (hweighted : WeightedGMOPrescribedLengthProvider
      (PrimeVectorSpace q 3))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (hhigh : 3 * q - 1 ≤ (reflectionOccurrences s).card) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) := by
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := hqPrime.pos
  have hQpos : 0 < Q := by
    dsimp only [Q]
    positivity
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hDodd : Odd D := by
    rcases hqodd with ⟨k, hk⟩
    refine ⟨3 * k, ?_⟩
    dsimp only [D]
    omega
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    dsimp only [Q, D]
    omega
  have hhigh' : D + 1 ≤ a := by
    dsimp only [D, a]
    omega
  have hmargin : dpm ≤ (D + 1) / 2 := by
    have hdeq : D + 1 = 3 * q - 1 := by
      dsimp only [D]
      omega
    rw [hdeq]
    exact hdpm
  obtain ⟨hout⟩ := exists_highReflectionTargetOutput_of_plusMinusDavenport
    s Q D a b dpm hQpos hQcard hDodd rfl rfl htotal hhigh'
      hmargin hpm hweighted
  exact hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput
    s Q D a b hQpos hQcard rfl rfl htotal hhigh' hout

/-- Exact first structural-GMO split in the rank-three middle range. -/
theorem rankThree_middleSpectrumAlternative
    (q dpm : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hdpm : dpm ≤ 3 * q - 2)
    (hpm : PlusMinusDavenportAtMost (PrimeVectorSpace q 3) dpm)
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 3))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2) :
    MiddleSpectrumAlternative s (q ^ 3) (3 * q - 2)
      (reflectionOccurrences s).card (rotationOccurrences s).card := by
  let A := PrimeVectorSpace q 3
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hq2 : 2 ≤ q := hqPrime.two_le
  have hq3 : 3 ≤ q := by
    by_contra h
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
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
  have hbook := middle_target_bookkeeping hDQ ha2 haD
  dsimp only at hbook
  have hcardA : Nat.card A = Q := by
    simp [A, Q, PrimeVectorSpace]
  have hcard : Nat.card A ≤ middleRotationTarget Q a := by
    rw [hcardA]
    exact hbook.2.2.2.2.1
  have hbEq : b = 2 * Q + D - a := by omega
  have hsurplus := middle_rotation_surplus hDQ ha2 haD hbEq
  have hthreshold : middleRotationTarget Q a + dpm - 1 ≤ b := by
    have htgtle : middleRotationTarget Q a ≤ b := hsurplus.1
    have hsur : D - 1 ≤ b - middleRotationTarget Q a := hsurplus.2
    omega
  simpa only [A, Q, D, a, b] using
    middleSpectrumAlternative_of_plusMinusGMO
      s Q D a b dpm ha2 rfl rfl hcard hthreshold hpm hGMO

/-- The full-spectrum side of the rank-three middle alternative is already
complete; the other side exposes the precise proper-subgroup concentration
consumed by the remaining dimension descent. -/
theorem rankThree_middle_full_or_concentrated
    (q dpm : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hdpm : dpm ≤ 3 * q - 2)
    (hpm : PlusMinusDavenportAtMost (PrimeVectorSpace q 3) dpm)
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 3))
    (s : List (PrimeVectorDihedral q 3))
    (hlen : s.length = 2 * q ^ 3 + 3 * q - 2)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 3 * q - 2) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 3) ∨
      ∃ K : AddSubgroup (PrimeVectorSpace q 3),
        Nonempty (MiddleNonfullConcentrationOutput s
          (rotationOccurrences s).card K) := by
  let Q := q ^ 3
  let D := 3 * q - 2
  let a := (reflectionOccurrences s).card
  have hq3 : 3 ≤ q := by
    by_contra h
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  have hDQ : D ≤ Q := by
    have hqminus3 : q - 3 + 3 = q := Nat.sub_add_cancel hq3
    have hsq : 3 * q ≤ q ^ 2 := by
      nlinarith [Nat.zero_le (q * (q - 3))]
    have hcube : q ^ 2 ≤ q ^ 3 := by
      nlinarith [Nat.zero_le (q ^ 2 * (q - 1))]
    dsimp only [D, Q]
    omega
  rcases rankThree_middleSpectrumAlternative q dpm hqPrime hqodd hdpm
      hpm hGMO s hlen ha2 haD with hfull | hnonfull
  · obtain ⟨hout⟩ := hfull
    exact Or.inl (hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput
      s Q D a hDQ (by simpa [a] using ha2) (by simpa [a, D] using haD)
        hout)
  · exact Or.inr hnonfull

end GaoLean

#print axioms GaoLean.rankThree_lowReflection_upper
#print axioms GaoLean.rankThree_highReflection_upper
#print axioms GaoLean.rankThree_middleSpectrumAlternative
#print axioms GaoLean.rankThree_middle_full_or_concentrated
