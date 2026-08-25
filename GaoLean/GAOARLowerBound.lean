import GaoLean.GAOARStatements
import GaoLean.PGDavenportBridge
import GaoLean.PGDavenportBound
import GaoLean.PGLowerBound

/-!
# Standard lower bound for the arbitrary-rank Gao statement

This file proves the lower-threshold half of `GAOARV1` from the exact
ordinary Davenport statement for `C_q^r`.  The latter is an explicit Olson
boundary, not a hidden axiom.  The proof uses an occurrence-labelled
zero-sum-free rotation word, appends one reflection, and pads with identities.
-/

namespace GaoLean

/-- The exact family of counterexamples below the proposed GAO-AR threshold,
conditional only on the explicitly supplied ordinary Davenport equality for
`C_q^r`. -/
theorem gaoAR_lowerThreshold_of_ordinaryDavenport
    (q r : ℕ) [NeZero q]
    (hD : IsOrdinaryDavenportConstant (PrimeVectorSpace q r)
      (r * (q - 1) + 1)) :
    ∀ n : ℕ, n < 2 * q ^ r + r * (q - 1) + 1 →
      ∃ s : List (PrimeVectorDihedral q r), s.length = n ∧
        ¬HasProductOneSubsequenceOfCard s (2 * q ^ r) := by
  let A := PrimeVectorSpace q r
  let D := r * (q - 1) + 1
  have hFcard : Fintype.card A = q ^ r := by
    simp [A, PrimeVectorSpace]
  have hcard : Nat.card A = q ^ r := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  have hDle : D ≤ Nat.card A := by
    exact ordinaryDavenportConstant_le_natCard D hD
  have hwitness : SmallDavenportWitness
      (ConcreteGDihedral.Group A) D :=
    ConcreteGDihedral.smallDavenportWitness_of_isOrdinaryDavenportConstant
      D hD
  have hcounter :=
    ConcreteGDihedral.pgGaoThresholdCounterexamples_of_smallDavenportWitness
      (A := A) D hDle hwitness
  intro n hn
  have hn' : n < 2 * Nat.card A + D := by
    simpa [D, hFcard, Nat.add_assoc] using hn
  obtain ⟨s, hslen, hsfree⟩ := hcounter n hn'
  refine ⟨s, hslen, ?_⟩
  simpa [A, hFcard] using hsfree

end GaoLean

#print axioms GaoLean.gaoAR_lowerThreshold_of_ordinaryDavenport
