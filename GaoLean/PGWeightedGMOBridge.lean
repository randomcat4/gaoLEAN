import GaoLean.PGWeightedGMOTransport

/-!
# Weighted GMO source interface for the high-reflection pair reservoir

This module specializes the generic additive-list weighted GMO interface to the
canonical occurrence-labelled same-type pair-label sequence.  The transport
from a positive/negative selection of additive-list positions to the four pair
lists is proved in `PGWeightedGMOTransport`; it is no longer external.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Troi--Zannier's restricted-coefficient output, oddness of `D`, and the
uniform weighted GMO provider mechanically supply the high-reflection output.
All occurrence pairing and threshold arithmetic are internal. -/
theorem exists_highReflectionTargetOutput_of_weightedGMO
    (s : List (Group A)) (Q D a b : ℕ)
    (hQ : 0 < Q)
    (hQcard : Q = Nat.card A)
    (hDodd : Odd D)
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hhigh : D + 1 ≤ a)
    (hrestricted : RestrictedCoefficientOutputAt A ((D + 1) / 2))
    (hweighted : WeightedGMOPrescribedLengthProvider A) :
    Nonempty (PrescribedSignedReservoirTargetOutput s Q) := by
  have hpm : PlusMinusDavenportAtMost A ((D + 1) / 2) :=
    plusMinusDavenportAtMost_of_restrictedCoefficientOutput hrestricted
  have hready := canonicalSameTypePairReservoir_highReflection_ready
    s Q D a b ((D + 1) / 2) hQ hDodd hreflectionCount
      hrotationCount htotal hhigh (Nat.le_refl _)
  have hQle : Nat.card A ≤ Q := by omega
  have hlabelThreshold : Q + (D + 1) / 2 - 1 ≤
      (canonicalPairLabelSequence s).length := by
    simpa [canonicalPairLabelSequence] using hready.1
  obtain ⟨hout⟩ := hweighted (canonicalPairLabelSequence s) Q
    ((D + 1) / 2) hQle hpm hlabelThreshold
  exact ⟨PrescribedSignedReservoirTargetOutput.ofWeightedGMOTargetOutput hout⟩

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.exists_highReflectionTargetOutput_of_weightedGMO
