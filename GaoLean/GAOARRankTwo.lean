import GaoLean.GAOARGMOInterfaces
import GaoLean.GAOARPlusMinusBounds
import GaoLean.PGOrdinaryGMOBridge
import GaoLean.PGWeightedGMOTransport
import GaoLean.PGSynthesis

/-!
# Rank-two GAO-AR proof

This module starts the direct rank-two proof from the frozen manuscript.  It
currently closes the two outer reflection ranges.  The middle range is not
asserted here and no theorem in this file claims the complete rank-two upper
bound.
-/

namespace GaoLean

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- High-reflection GMO preparation from the literal plus-minus Davenport
upper bound, without replacing it by a stronger restricted-coefficient
assumption. -/
theorem exists_highReflectionTargetOutput_of_plusMinusDavenport
    (s : List (Group A)) (Q D a b m : ℕ)
    (hQ : 0 < Q)
    (hQcard : Q = Nat.card A)
    (hDodd : Odd D)
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hhigh : D + 1 ≤ a)
    (hpmMargin : m ≤ (D + 1) / 2)
    (hpm : PlusMinusDavenportAtMost A m)
    (hweighted : WeightedGMOPrescribedLengthProvider A) :
    Nonempty (PrescribedSignedReservoirTargetOutput s Q) := by
  have hready := canonicalSameTypePairReservoir_highReflection_ready
    s Q D a b m hQ hDodd hreflectionCount hrotationCount htotal hhigh
      hpmMargin
  have hQle : Nat.card A ≤ Q := by omega
  have hlabelThreshold : Q + m - 1 ≤
      (canonicalPairLabelSequence s).length := by
    simpa [canonicalPairLabelSequence] using hready.1
  obtain ⟨hout⟩ := hweighted (canonicalPairLabelSequence s) Q m
    hQle hpm hlabelThreshold
  exact ⟨PrescribedSignedReservoirTargetOutput.ofWeightedGMOTargetOutput
    hout⟩

end ConcreteGDihedral

/-- The `a ≤ 1` branch of the manuscript's rank-two upper bound.  Its only
mathematical provider is the ordinary prescribed-length GMO theorem at the
explicit Olson value `2(q-1)+1`. -/
theorem rankTwo_lowReflection_upper
    (q : ℕ) [NeZero q]
    (hordinary : OrdinaryGMOPrescribedLengthProvider
      (PrimeVectorSpace q 2) (2 * (q - 1) + 1))
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1)
    (hlow : (reflectionOccurrences s).card ≤ 1) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 2) := by
  let A := PrimeVectorSpace q 2
  let Q := q ^ 2
  let D := 2 * (q - 1) + 1
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [ConcreteGDihedral.card_reflectionOccurrences_add_card_rotationOccurrences,
      hlen]
    simp [Q, D, Nat.add_assoc]
  obtain ⟨hout⟩ :=
    ConcreteGDihedral.exists_lowReflectionTargetOutput_of_ordinaryGMO
      s Q D a b hQcard rfl htotal hlow hordinary
  exact ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
    s Q hQcard hout

/-- The `a ≥ 2q` branch of the manuscript's rank-two upper bound.  Its
internal `D_±(F_q²) ≤ q` input is discharged by the self-contained
binary-subset-sum/`q = 3` proof in `GAOARPlusMinusBounds`. -/
theorem rankTwo_highReflection_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hweighted : WeightedGMOPrescribedLengthProvider
      (PrimeVectorSpace q 2))
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1)
    (hhigh : 2 * q ≤
      (reflectionOccurrences s).card) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 2) := by
  let A := PrimeVectorSpace q 2
  let Q := q ^ 2
  let D := 2 * (q - 1) + 1
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := hqPrime.pos
  have hQpos : 0 < Q := by
    positivity
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hDodd : Odd D := by
    refine ⟨q - 1, ?_⟩
    simp [D, Nat.mul_comm]
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [ConcreteGDihedral.card_reflectionOccurrences_add_card_rotationOccurrences,
      hlen]
    simp [Q, D, Nat.add_assoc]
  have hhigh' : D + 1 ≤ a := by
    dsimp only [D, a]
    omega
  have hpmMargin : q ≤ (D + 1) / 2 := by
    dsimp only [D]
    omega
  have hpm : PlusMinusDavenportAtMost A q :=
    primeRankTwo_plusMinusDavenportAtMost q hqPrime hqodd
  obtain ⟨hout⟩ :=
    ConcreteGDihedral.exists_highReflectionTargetOutput_of_plusMinusDavenport
      s Q D a b q hQpos hQcard hDodd rfl rfl htotal hhigh' hpmMargin
        hpm hweighted
  exact ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput
    s Q D a b hQpos hQcard rfl rfl htotal hhigh' hout

end GaoLean

#print axioms GaoLean.ConcreteGDihedral.exists_highReflectionTargetOutput_of_plusMinusDavenport
#print axioms GaoLean.rankTwo_lowReflection_upper
#print axioms GaoLean.rankTwo_highReflection_upper
