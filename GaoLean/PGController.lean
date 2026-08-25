import GaoLean.PGFrontend

/-!
# PG-O3 residual-controller statement skeleton

This file freezes the quantifier split between the fixed-source controller
`RC_S(K)` and the arbitrary-auxiliary-sequence controller `ZR_A(X,K)`.

The quotient no-reflection condition is an explicit predicate parameter so
the skeleton remains reusable.  `PGGuard.lean` supplies its concrete quotient
semantics and translation/descent theorems; `PGInduction.lean` specializes the
skeleton to that guard.  These definitions alone are still `STATEMENT_ONLY`,
not a proof of PG-O3.
-/

namespace GaoLean

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A]

/-- A concrete semidirect-product element lies in the rotation coset. -/
def IsRotation (g : Group A) : Prop := g.right = 1

/-- Additive coordinate of the left component. -/
def coordinate (g : Group A) : A := Multiplicative.toAdd g.left

end ConcreteGDihedral

section ControllerStatements

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Labelled rotation occurrences whose coordinates lie in `K`. -/
noncomputable def rotationOccurrencesIn
    (s : List (ConcreteGDihedral.Group A)) (K : AddSubgroup A) : Selection s := by
  classical
  exact Finset.univ.filter fun i =>
    ConcreteGDihedral.IsRotation (occurrenceValue s i) ∧
      ConcreteGDihedral.coordinate (occurrenceValue s i) ∈ K

/-- All labelled rotation occurrences. -/
noncomputable def rotationOccurrences
    (s : List (ConcreteGDihedral.Group A)) : Selection s := by
  classical
  exact Finset.univ.filter fun i =>
    ConcreteGDihedral.IsRotation (occurrenceValue s i)

/-- All labelled reflection occurrences, defined as the complement of the
rotation coset in the concrete `C₂` semidirect product. -/
noncomputable def reflectionOccurrences
    (s : List (ConcreteGDihedral.Group A)) : Selection s := by
  classical
  exact Finset.univ.filter fun i =>
    ¬ConcreteGDihedral.IsRotation (occurrenceValue s i)

/-- Exact all-rotation conclusion required from `ZR_A(X,K)`. -/
def HasAllRotationProductOneSubsequenceOfCard
    (s : List (ConcreteGDihedral.Group A)) (k : ℕ) : Prop :=
  ∃ I : Selection s, I.card = k ∧ IsProductOneSelection s I ∧
    ∀ i ∈ I, ConcreteGDihedral.IsRotation (occurrenceValue s i)

/-- Fixed-source controller `RC_S(K)`: only the original sequence `S` is
quantified outside this definition. -/
def RCStatement (S : List (ConcreteGDihedral.Group A))
    (Q b : ℕ) (K : AddSubgroup A) : Prop :=
  b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn S K).card →
    HasProductOneSubsequenceOfCard S (2 * Q)

/-- Arbitrary-sequence controller `ZR_A(X,K)`.  The guard stays parameterized
here; its concrete occurrence-sensitive realization is
`ConcreteGDihedral.QuotientNoReflection`. -/
def ZRStatement
    (quotientNoReflection :
      List (ConcreteGDihedral.Group A) → AddSubgroup A → Prop)
    (X : List (ConcreteGDihedral.Group A))
    (Q D a b : ℕ) (K : AddSubgroup A) : Prop :=
  X.length = 2 * Q + D →
  (reflectionOccurrences X).card = a →
  (rotationOccurrences X).card = b →
  b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
  quotientNoReflection X K →
  HasAllRotationProductOneSubsequenceOfCard X (2 * Q)

/-- Simultaneous PG-O3 statement skeleton.  It deliberately keeps fixed `S`
and arbitrary `X` in different quantifier positions.  Strict-induction and
quotient-guard preservation are not proved by this definition. -/
def PGO3ControllerSkeleton
    (quotientNoReflection :
      List (ConcreteGDihedral.Group A) → AddSubgroup A → Prop)
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ) : Prop :=
  (∀ K : AddSubgroup A, K < ⊤ → RCStatement S Q b K) ∧
  (∀ (X : List (ConcreteGDihedral.Group A)) (K : AddSubgroup A),
    K < ⊤ → ZRStatement quotientNoReflection X Q D a b K)

end ControllerStatements

end GaoLean
