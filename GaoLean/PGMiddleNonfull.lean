import GaoLean.PGMiddleReflection

/-!
# Middle-reflection non-full-spectrum front end

This file freezes the occurrence-labelled concentration output used in the
non-full middle-reflection branch of A-R6 Section 4.3.  From the two weighted
coset conditions for each concentrated rotation it proves membership in the
proper subgroup `K`, using only oddness of the ambient finite group.  The
resulting cardinality bound is then passed to the already separated `RC`
controller interface.

The concentration output and the controller skeleton are explicit theorem
parameters.  In particular, this file does not prove GMO's prescribed-length
alternative or the positive-subgroup controller steps.
-/

namespace GaoLean

section OddFiniteQuotient

variable {A : Type*} [AddCommGroup A]

/-- Every quotient of a finite additive group of odd cardinality again has
odd cardinality. -/
theorem odd_natCard_quotient_of_odd_natCard
    (K : AddSubgroup A) (hA : Odd (Nat.card A)) :
    Odd (Nat.card (A ⧸ K)) :=
  Odd.of_dvd_nat hA K.card_quotient_dvd_card

end OddFiniteQuotient

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Minimal occurrence-labelled projection consumed from the non-full
weighted GMO branch in A-R6 Section 4.3.  The center `β` may depend on the occurrence,
as in the source assertion that `x` and `-x` lie in one `K`-coset for every
concentrated rotation coordinate `x`.

The source's additional ordinary-coset condition is not stored because this
front end never uses it.  This is a structure parameter, not an assertion
that the external GMO output has been proved in Lean. -/
structure MiddleNonfullConcentrationOutput
    (s : List (Group A)) (b : ℕ) (K : AddSubgroup A) where
  concentrated : Selection s
  proper : K < ⊤
  card_lower :
    b - Nat.card (A ⧸ K) + 2 ≤ concentrated.card
  rotations : ∀ i ∈ concentrated,
    IsRotation (occurrenceValue s i)
  posNegSameCoset : ∀ i ∈ concentrated,
    ∃ β : A,
      coordinate (occurrenceValue s i) - β ∈ K ∧
      -coordinate (occurrenceValue s i) - β ∈ K

/-- Each concentrated occurrence lies in the controller's labelled
`K`-rotation pool.  This is the dangerous `2x ∈ K ⇒ x ∈ K` step, with
the odd quotient cardinality derived rather than assumed. -/
theorem MiddleNonfullConcentrationOutput.concentrated_subset_rotationOccurrencesIn
    {s : List (Group A)} {b : ℕ} {K : AddSubgroup A}
    (h : MiddleNonfullConcentrationOutput s b K)
    (hA : Odd (Nat.card A)) :
    h.concentrated ⊆ rotationOccurrencesIn s K := by
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  intro i hi
  have hoddNat : Odd (Nat.card (A ⧸ K)) :=
    odd_natCard_quotient_of_odd_natCard K hA
  have hodd : Odd (Fintype.card (A ⧸ K)) := by
    simpa using hoddNat
  obtain ⟨β, hpos, hneg⟩ := h.posNegSameCoset i hi
  have hmem : coordinate (occurrenceValue s i) ∈ K :=
    mem_of_pos_neg_mem_same_coset_of_quotient_card_odd K hodd hpos hneg
  simp only [rotationOccurrencesIn, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨h.rotations i hi, hmem⟩

/-- The external non-full concentration count therefore supplies exactly the
capacity premise expected by `RC_S(K)`. -/
theorem MiddleNonfullConcentrationOutput.rotationCapacity
    {s : List (Group A)} {b : ℕ} {K : AddSubgroup A}
    (h : MiddleNonfullConcentrationOutput s b K)
    (hA : Odd (Nat.card A)) :
    b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn s K).card := by
  exact h.card_lower.trans (Finset.card_le_card
    (h.concentrated_subset_rotationOccurrencesIn hA))

/-- Complete mechanical front end from a non-full middle concentration to
the fixed-source residual controller conclusion.  Both the GMO output `h`
and the simultaneously proved controller `hcontroller` remain explicit
parameters. -/
theorem hasProductOneSubsequenceOfTwice_of_middleNonfullConcentration
    (s : List (Group A)) (Q D a b : ℕ) (K : AddSubgroup A)
    (hA : Odd (Nat.card A))
    (hcontroller : PGO3ControllerSkeleton QuotientNoReflection
      s Q D a b)
    (h : MiddleNonfullConcentrationOutput s b K) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  exact hcontroller.1 K h.proper (h.rotationCapacity hA)

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.odd_natCard_quotient_of_odd_natCard
#print axioms GaoLean.ConcreteGDihedral.MiddleNonfullConcentrationOutput.concentrated_subset_rotationOccurrencesIn
#print axioms GaoLean.ConcreteGDihedral.MiddleNonfullConcentrationOutput.rotationCapacity
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_middleNonfullConcentration
