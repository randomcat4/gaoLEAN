import GaoLean.PGLowReflection
import GaoLean.PGMiddleAssembly

/-!
# All reflection-count regimes

This module composes the three internally checked Section 4 consumers.  It
does not produce any prescribed-length output: the applicable ordinary,
weighted, or middle full/non-full result remains an explicit parameter.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Conditional output package for the exhaustive reflection-count split.
Only the implication whose numerical regime holds is consumed. -/
def ReflectionRegimeOutputs
    (s : List (Group A)) (Q D a b : ℕ) : Prop :=
  (a ≤ 1 → Nonempty (LowReflectionTargetOutput s Q)) ∧
  (D + 1 ≤ a → Nonempty (PrescribedSignedReservoirTargetOutput s Q)) ∧
  ((2 ≤ a ∧ a ≤ D) → MiddleSpectrumAlternative s Q D a b)

/-- Complete internal Section 4 dispatch.  Once the exact output required in
the applicable numerical regime and the residual controller are supplied,
every reflection count yields an exact `2Q` product-one subsequence. -/
theorem hasProductOneSubsequenceOfTwice_of_reflectionRegimeOutputs
    (s : List (Group A)) (Q D a b : ℕ)
    (hQpos : 0 < Q) (hQcard : Q = Nat.card A)
    (hDQ : D ≤ Q) (hAodd : Odd (Nat.card A))
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hcontroller : PGO3ControllerSkeleton QuotientNoReflection
      s Q D a b)
    (houtputs : ReflectionRegimeOutputs s Q D a b) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  rcases reflection_count_trichotomy a D with hlow | hhigh | hmiddle
  · rcases houtputs.1 hlow with ⟨hout⟩
    exact hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
      s Q hQcard hout
  · rcases houtputs.2.1 hhigh with ⟨hout⟩
    exact hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput
      s Q D a b hQpos hQcard hreflectionCount hrotationCount htotal
        hhigh hout
  · exact hasProductOneSubsequenceOfTwice_of_middleSpectrumAlternative
      s Q D a b hDQ hmiddle.1 hmiddle.2 hAodd hcontroller
        (houtputs.2.2 hmiddle)

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_reflectionRegimeOutputs
