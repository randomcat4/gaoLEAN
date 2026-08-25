import GaoLean.Sequence

/-!
# Occurrence-sensitive plus-minus zero sums

This file isolates the exact Lean bridge needed from a restricted-coefficient
theorem such as Troi--Zannier: a nonzero coefficient vector in
`{-1, 0, 1}` is converted, by deleting its zero coordinates, into a nonempty
labelled occurrence selection with a plus-minus zero sum.

No restricted-coefficient existence theorem is asserted here.  It is supplied
only through the explicit proposition `RestrictedCoefficientOutputAt`.
-/

namespace GaoLean

section PlusMinus

variable {A : Type*} [AddCommGroup A]

/-- The two signs allowed in a plus-minus zero sum. -/
inductive PlusMinusSign
  | positive
  | negative
deriving DecidableEq

namespace PlusMinusSign

/-- Action of a sign on an additive-group element. -/
def act : PlusMinusSign → A → A
  | positive, x => x
  | negative, x => -x

end PlusMinusSign

/-- A labelled, nonempty plus-minus zero-sum subsequence.  The finite set `I`
contains source positions, so repeated values remain distinct occurrences. -/
def HasNonemptyPlusMinusZeroSum (s : List A) : Prop :=
  ∃ I : Selection s, I.Nonempty ∧
    ∃ sign : Occurrence s → PlusMinusSign,
      ∑ i ∈ I, (sign i).act (occurrenceValue s i) = 0

/-- The occurrence-sensitive threshold formulation of `D_±(A) ≤ m`:
every sequence of exactly `m` labelled occurrences has a nonempty plus-minus
zero sum. -/
def PlusMinusDavenportAtMost (A : Type*) [AddCommGroup A] (m : ℕ) : Prop :=
  ∀ s : List A, s.length = m → HasNonemptyPlusMinusZeroSum s

/-- Membership in the integer coefficient set `{-1, 0, 1}`. -/
def IsRestrictedCoefficient (a : ℤ) : Prop :=
  a = -1 ∨ a = 0 ∨ a = 1

/-- The precise occurrence-labelled output expected from the specialized
Troi--Zannier restricted-coefficient theorem. -/
structure RestrictedCoefficientRelation (s : List A) where
  coefficient : Occurrence s → ℤ
  restricted : ∀ i, IsRestrictedCoefficient (coefficient i)
  nonzero : ∃ i, coefficient i ≠ 0
  weightedSum_eq_zero :
    ∑ i, coefficient i • occurrenceValue s i = 0

/-- Explicit conditional interface for the external theorem at a fixed
sequence length.  This is a proposition parameter, not a project axiom. -/
def RestrictedCoefficientOutputAt (A : Type*) [AddCommGroup A] (m : ℕ) : Prop :=
  ∀ s : List A, s.length = m → Nonempty (RestrictedCoefficientRelation s)

private def signOfCoefficient (a : ℤ) : PlusMinusSign :=
  if a = -1 then .negative else .positive

private theorem signOfCoefficient_act {a : ℤ} {x : A}
    (ha : IsRestrictedCoefficient a) (ha0 : a ≠ 0) :
    (signOfCoefficient a).act x = a • x := by
  rcases ha with hneg | hzero | hpos
  · subst a
    simp [signOfCoefficient, PlusMinusSign.act]
  · exact (ha0 hzero).elim
  · subst a
    simp [signOfCoefficient, PlusMinusSign.act]

/-- Delete the zero coordinates of a nonzero restricted-coefficient relation.
The resulting support is a nonempty set of source positions, not merely a set
of values. -/
theorem hasNonemptyPlusMinusZeroSum_of_restrictedCoefficientRelation
    {s : List A} (R : RestrictedCoefficientRelation s) :
    HasNonemptyPlusMinusZeroSum s := by
  let I : Selection s := Finset.univ.filter (fun i => R.coefficient i ≠ 0)
  refine ⟨I, ?_, fun i => signOfCoefficient (R.coefficient i), ?_⟩
  · rcases R.nonzero with ⟨i, hi⟩
    exact ⟨i, by simp [I, hi]⟩
  · have hselected :
        (∑ i ∈ I,
            (signOfCoefficient (R.coefficient i)).act (occurrenceValue s i)) =
          ∑ i ∈ I, R.coefficient i • occurrenceValue s i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : R.coefficient i ≠ 0 := by simpa [I] using hi
      exact signOfCoefficient_act (R.restricted i) hi0
    rw [hselected]
    calc
      (∑ i ∈ I, R.coefficient i • occurrenceValue s i) =
          ∑ i, R.coefficient i • occurrenceValue s i := by
        apply Finset.sum_subset (Finset.subset_univ I)
        intro i _ hi
        have hzero : R.coefficient i = 0 := by
          by_contra hne
          exact hi (by simp [I, hne])
        simp [hzero]
      _ = 0 := R.weightedSum_eq_zero

/-- The unconditional bridge from the exact external output interface to the
occurrence-sensitive plus-minus Davenport bound.  Mathematical use of this
theorem is `LEAN_CONDITIONAL` until its argument is supplied by a separately
formalized restricted-coefficient theorem. -/
theorem plusMinusDavenportAtMost_of_restrictedCoefficientOutput
    {m : ℕ} (houtput : RestrictedCoefficientOutputAt A m) :
    PlusMinusDavenportAtMost A m := by
  intro s hs
  rcases houtput s hs with ⟨R⟩
  exact hasNonemptyPlusMinusZeroSum_of_restrictedCoefficientRelation
    R

/-- Oddness closes the numerical specialization
`2 * ((D + 1) / 2) = D + 1`. -/
theorem twice_half_succ_of_odd {D : ℕ} (hD : Odd D) :
    2 * ((D + 1) / 2) = D + 1 := by
  rcases hD with ⟨k, hk⟩
  omega

/-- The strict numerical hypothesis in the restricted-coefficient theorem,
with `d*(A) = D(A) - 1`, has two units of slack. -/
theorem restricted_coefficient_budget_of_odd {D : ℕ} (hD : Odd D) :
    D - 1 < 2 * ((D + 1) / 2) := by
  rw [twice_half_succ_of_odd hD]
  omega

/-- Conditional Lean form of the PG-PM-v1 endpoint. -/
theorem pg_pm_v1_of_restrictedCoefficientOutput {D : ℕ}
    (hD : Odd D)
    (houtput : RestrictedCoefficientOutputAt A ((D + 1) / 2)) :
    PlusMinusDavenportAtMost A ((D + 1) / 2) ∧
      2 * ((D + 1) / 2) = D + 1 ∧
      D - 1 < 2 * ((D + 1) / 2) := by
  exact ⟨plusMinusDavenportAtMost_of_restrictedCoefficientOutput houtput,
    twice_half_succ_of_odd hD, restricted_coefficient_budget_of_odd hD⟩

end PlusMinus

end GaoLean

#print axioms GaoLean.hasNonemptyPlusMinusZeroSum_of_restrictedCoefficientRelation
#print axioms GaoLean.plusMinusDavenportAtMost_of_restrictedCoefficientOutput
#print axioms GaoLean.twice_half_succ_of_odd
#print axioms GaoLean.restricted_coefficient_budget_of_odd
#print axioms GaoLean.pg_pm_v1_of_restrictedCoefficientOutput
