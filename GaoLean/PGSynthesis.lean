import GaoLean.PGReflectionRegimes
import GaoLean.PGLowerBound

/-!
# PG-O4 conditional synthesis

This module closes the purely internal top-level bookkeeping left after the
three reflection-count consumers.  It computes the reflection and rotation
counts from the source occurrence list, proves that the two types partition
all source labels, and dispatches to the applicable regime.

The external ordinary/weighted GMO outputs and the middle residual controller
remain explicit proposition inputs.  The final threshold theorem additionally
keeps the lower-bound counterexample family explicit.  Consequently no result
in this file asserts `PG-GAO-v1` without its still-unformalized predecessors.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Rotation and reflection occurrence labels are disjoint, even when their
underlying group values repeat. -/
theorem disjoint_rotationOccurrences_reflectionOccurrences
    (s : List (Group A)) :
    Disjoint (rotationOccurrences s) (reflectionOccurrences s) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiRotation hiReflection
  have hrotation : IsRotation (occurrenceValue s i) := by
    simpa [rotationOccurrences] using hiRotation
  have hreflection : ¬IsRotation (occurrenceValue s i) := by
    simpa [reflectionOccurrences] using hiReflection
  exact hreflection hrotation

/-- Every source occurrence is exactly one of a rotation or a reflection. -/
theorem rotationOccurrences_union_reflectionOccurrences
    (s : List (Group A)) :
    rotationOccurrences s ∪ reflectionOccurrences s = Finset.univ := by
  classical
  ext i
  by_cases hrotation : IsRotation (occurrenceValue s i)
  · simp [rotationOccurrences, reflectionOccurrences, hrotation]
  · simp [rotationOccurrences, reflectionOccurrences, hrotation]

/-- The actual reflection and rotation counts add to the source length. -/
theorem card_reflectionOccurrences_add_card_rotationOccurrences
    (s : List (Group A)) :
    (reflectionOccurrences s).card + (rotationOccurrences s).card =
      s.length := by
  classical
  have hdis : Disjoint (reflectionOccurrences s) (rotationOccurrences s) :=
    (disjoint_rotationOccurrences_reflectionOccurrences s).symm
  calc
    (reflectionOccurrences s).card + (rotationOccurrences s).card =
        (reflectionOccurrences s ∪ rotationOccurrences s).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ = (Finset.univ : Selection s).card := by
      congr 1
      simpa [Finset.union_comm] using
        rotationOccurrences_union_reflectionOccurrences s
    _ = s.length := by simp

/-- Source-faithful regime input package.  In contrast with the earlier
uniform dispatcher, the residual controller is required only when the actual
count lies in the middle range. -/
def ReflectionRegimeClosureInputs
    (s : List (Group A)) (Q D a b : ℕ) : Prop :=
  (a ≤ 1 → Nonempty (LowReflectionTargetOutput s Q)) ∧
  (D + 1 ≤ a → Nonempty (PrescribedSignedReservoirTargetOutput s Q)) ∧
  ((2 ≤ a ∧ a ≤ D) →
    PGO3ControllerSkeleton QuotientNoReflection s Q D a b ∧
      MiddleSpectrumAlternative s Q D a b)

/-- Exact Section 4--6 upper-bound assembly.  No controller is demanded in an
outer reflection-count regime. -/
theorem hasProductOneSubsequenceOfTwice_of_reflectionRegimeClosureInputs
    (s : List (Group A)) (Q D a b : ℕ)
    (hQpos : 0 < Q) (hQcard : Q = Nat.card A)
    (hDQ : D ≤ Q) (hAodd : Odd (Nat.card A))
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hinputs : ReflectionRegimeClosureInputs s Q D a b) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  rcases reflection_count_trichotomy a D with hlow | hhigh | hmiddle
  · rcases hinputs.1 hlow with ⟨hout⟩
    exact hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
      s Q hQcard hout
  · rcases hinputs.2.1 hhigh with ⟨hout⟩
    exact hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput
      s Q D a b hQpos hQcard hreflectionCount hrotationCount htotal
        hhigh hout
  · obtain ⟨hcontroller, halt⟩ := hinputs.2.2 hmiddle
    exact hasProductOneSubsequenceOfTwice_of_middleSpectrumAlternative
      s Q D a b hDQ hmiddle.1 hmiddle.2 hAodd hcontroller halt

/-- Exact remaining upper-input boundary, quantified over every source
sequence at the proposed threshold. -/
def PGGaoUpperInputs (A : Type*) [AddCommGroup A] [Fintype A]
    (D : ℕ) : Prop :=
  ∀ s : List (Group A), s.length = 2 * Nat.card A + D →
    ReflectionRegimeClosureInputs s (Nat.card A) D
      (reflectionOccurrences s).card (rotationOccurrences s).card

/-- The conditional PG-O4 upper bound after all source lists are routed to
their exact occurrence-labelled regime inputs. -/
theorem hasExactProductOneBlockAtLength_of_pgGaoUpperInputs
    (D : ℕ) (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hupper : PGGaoUpperInputs A D) :
    HasExactProductOneBlockAtLength (Group A)
      (2 * Nat.card A + D) (2 * Nat.card A) := by
  intro s hlen
  have hQpos : 0 < Nat.card A := Nat.card_pos
  have htotal :
      (reflectionOccurrences s).card + (rotationOccurrences s).card =
        2 * Nat.card A + D := by
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
  exact hasProductOneSubsequenceOfTwice_of_reflectionRegimeClosureInputs
    s (Nat.card A) D (reflectionOccurrences s).card
      (rotationOccurrences s).card hQpos rfl hDQ hAodd rfl rfl htotal
      (hupper s hlen)

/-- Conditional realization of the frozen `PGGaoV1` statement.  This theorem
only composes the checked upper dispatcher with an explicit lower-bound
counterexample family; it proves neither external input package. -/
theorem pgGaoV1_of_upperInputs_and_thresholdCounterexamples
    (D : ℕ) (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hupper : PGGaoUpperInputs A D)
    (hlower : PGGaoThresholdCounterexamples A D) :
    PGGaoV1 A D := by
  constructor
  · simpa only [Nat.card_eq_fintype_card] using
      hasExactProductOneBlockAtLength_of_pgGaoUpperInputs
        D hDQ hAodd hupper
  · simpa only [PGGaoThresholdCounterexamples,
      Nat.card_eq_fintype_card] using hlower

/-- Source-shaped conditional PG-GAO closure.  The entire lower bound is now
derived internally from the exact small-Davenport witness; only the upper
regime inputs and the external facts needed to produce them remain. -/
theorem pgGaoV1_of_upperInputs_and_smallDavenportWitness
    (D : ℕ) (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hupper : PGGaoUpperInputs A D)
    (hlower : SmallDavenportWitness (Group A) D) :
    PGGaoV1 A D := by
  exact pgGaoV1_of_upperInputs_and_thresholdCounterexamples
    D hDQ hAodd hupper
      (pgGaoThresholdCounterexamples_of_smallDavenportWitness
        D hDQ hlower)

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.disjoint_rotationOccurrences_reflectionOccurrences
#print axioms GaoLean.ConcreteGDihedral.rotationOccurrences_union_reflectionOccurrences
#print axioms GaoLean.ConcreteGDihedral.card_reflectionOccurrences_add_card_rotationOccurrences
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_reflectionRegimeClosureInputs
#print axioms GaoLean.ConcreteGDihedral.hasExactProductOneBlockAtLength_of_pgGaoUpperInputs
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_upperInputs_and_thresholdCounterexamples
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_upperInputs_and_smallDavenportWitness
