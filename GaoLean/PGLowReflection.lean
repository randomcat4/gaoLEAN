import GaoLean.PGSpectrum

/-!
# At-most-one-reflection branch

This file closes the internal part of A-R6 Section 4.1.  The ordinary GMO
output remains an explicit occurrence-labelled parameter whose coordinate sum
lies in the published target `2Q • A`; Lean proves that target is zero when
`Q = |A|` and constructs the exact product-one block.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- In the `a≤1` regime the rotation count meets the ordinary GMO threshold
`2Q+D-1`. -/
theorem lowReflection_rotationCount_lower {Q D a b : ℕ}
    (ha : a ≤ 1) (htotal : a + b = 2 * Q + D) :
    2 * Q + D - 1 ≤ b := by
  omega

/-- Minimal occurrence-labelled ordinary-GMO output used in Section 4.1.
The coordinate sum is retained in the source-faithful target form
`(2Q) • z`, rather than assumed to be zero. -/
structure LowReflectionTargetOutput
    (s : List (Group A)) (Q : ℕ) where
  selected : Selection s
  selectedRotations : selected ⊆ rotationOccurrences s
  card_selected : selected.card = 2 * Q
  coordinateSum_mem_target :
    ∃ z : A, coordinateSum s selected = (2 * Q) • z

/-- The target `2Q • A` is `{0}` when `Q=|A|`. -/
theorem LowReflectionTargetOutput.coordinateSum_eq_zero
    {s : List (Group A)} {Q : ℕ}
    (h : LowReflectionTargetOutput s Q)
    (hQ : Q = Nat.card A) :
    coordinateSum s h.selected = 0 := by
  obtain ⟨z, hz⟩ := h.coordinateSum_mem_target
  rw [hz]
  have hQz : Q • z = 0 := by
    simpa [hQ] using (card_nsmul_eq_zero' z)
  rw [Nat.mul_comm 2 Q, mul_nsmul, hQz, nsmul_zero]

/-- Complete internal low-reflection closure from the explicit ordinary-GMO
target output to an exact all-rotation product-one block. -/
theorem hasAllRotationProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
    (s : List (Group A)) (Q : ℕ)
    (hQ : Q = Nat.card A)
    (h : LowReflectionTargetOutput s Q) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  apply hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
    s h.selected (2 * Q) h.card_selected
  · intro i hi
    have hiRotation : i ∈ rotationOccurrences s := h.selectedRotations hi
    simpa [rotationOccurrences] using hiRotation
  · exact h.coordinateSum_eq_zero hQ

/-- Product-one-facing form of the same exact `2Q` conclusion. -/
theorem hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
    (s : List (Group A)) (Q : ℕ)
    (hQ : Q = Nat.card A)
    (h : LowReflectionTargetOutput s Q) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  rcases hasAllRotationProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
      s Q hQ h with ⟨I, hcard, hprod, _⟩
  exact ⟨I, hcard, hprod⟩

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.lowReflection_rotationCount_lower
#print axioms GaoLean.ConcreteGDihedral.LowReflectionTargetOutput.coordinateSum_eq_zero
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
