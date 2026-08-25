import GaoLean.PGMiddleNonfull

/-!
# Middle-reflection full/non-full assembly

This file joins the two post-GMO middle-reflection consumers.  The disjunction
is an explicit theorem parameter: its left branch is the occurrence-labelled
full-spectrum output and its right branch is the proper-subgroup concentration
output.  It does not derive either branch from GMO Corollary 1.3.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Minimal post-GMO disjunction used by the middle-reflection route.  This is
the downstream projection of the full/non-full alternative, not a formalized
statement of GMO Corollary 1.3. -/
def MiddleSpectrumAlternative
    (s : List (Group A)) (Q D a b : ℕ) : Prop :=
  Nonempty (MiddleFullSpectrumOutput s Q D a) ∨
    ∃ K : AddSubgroup A, Nonempty (MiddleNonfullConcentrationOutput s b K)

/-- Once the minimal middle-spectrum alternative and the residual controller
are supplied, both branches close to the same exact `2Q` product-one
subsequence. -/
theorem hasProductOneSubsequenceOfTwice_of_middleSpectrumAlternative
    (s : List (Group A)) (Q D a b : ℕ)
    (hDQ : D ≤ Q) (ha2 : 2 ≤ a) (haD : a ≤ D)
    (hA : Odd (Nat.card A))
    (hcontroller : PGO3ControllerSkeleton QuotientNoReflection
      s Q D a b)
    (hAlt : MiddleSpectrumAlternative s Q D a b) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  rcases hAlt with hfull | hnonfull
  · rcases hfull with ⟨hfull⟩
    exact hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput
      s Q D a hDQ ha2 haD hfull
  · rcases hnonfull with ⟨K, hK⟩
    rcases hK with ⟨hnonfull⟩
    exact hasProductOneSubsequenceOfTwice_of_middleNonfullConcentration
      s Q D a b K hA hcontroller hnonfull

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_middleSpectrumAlternative
