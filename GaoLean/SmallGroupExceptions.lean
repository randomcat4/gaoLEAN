import GaoLean.PlusMinus

/-!
# Small-group exceptions to the frozen plus-minus entry bounds

This file gives proof-kernel-checkable witnesses for the `C₃` exceptions
recorded in the frozen A5/A6 research notes.  It deliberately separates the
false uniform bounds from their repaired statements: no repaired
classification theorem is asserted here.
-/

namespace GaoLean

section C3

private theorem pair_first_zero_has_pm (y : ZMod 3) :
    HasNonemptyPlusMinusZeroSum [0, y] := by
  refine ⟨{0}, by simp, fun _ => .positive, ?_⟩
  simp [PlusMinusSign.act, occurrenceValue]

private theorem pair_second_zero_has_pm (x : ZMod 3) :
    HasNonemptyPlusMinusZeroSum [x, 0] := by
  refine ⟨{1}, by simp, fun _ => .positive, ?_⟩
  simp [PlusMinusSign.act, occurrenceValue]

private theorem pair_equal_has_pm (x : ZMod 3) :
    HasNonemptyPlusMinusZeroSum [x, x] := by
  refine ⟨Finset.univ, Finset.univ_nonempty, fun i =>
    if i = 0 then .positive else .negative, ?_⟩
  change (∑ i : Fin 2,
    (if i = 0 then PlusMinusSign.positive else PlusMinusSign.negative).act
      ([x, x].get i)) = 0
  rw [Fin.sum_univ_two]
  simp [PlusMinusSign.act]

private theorem pair_opposite_has_pm (x : ZMod 3) :
    HasNonemptyPlusMinusZeroSum [x, -x] := by
  refine ⟨Finset.univ, Finset.univ_nonempty, fun _ => .positive, ?_⟩
  simp [PlusMinusSign.act, occurrenceValue]

/-- Every two-term sequence in `C₃` has a nonempty plus-minus zero sum. -/
theorem zmod3_pair_hasNonemptyPlusMinusZeroSum (x y : ZMod 3) :
    HasNonemptyPlusMinusZeroSum [x, y] := by
  fin_cases x <;> fin_cases y
  · change HasNonemptyPlusMinusZeroSum ([0, 0] : List (ZMod 3))
    exact pair_first_zero_has_pm 0
  · change HasNonemptyPlusMinusZeroSum ([0, 1] : List (ZMod 3))
    exact pair_first_zero_has_pm 1
  · change HasNonemptyPlusMinusZeroSum ([0, 2] : List (ZMod 3))
    exact pair_first_zero_has_pm 2
  · change HasNonemptyPlusMinusZeroSum ([1, 0] : List (ZMod 3))
    exact pair_second_zero_has_pm 1
  · change HasNonemptyPlusMinusZeroSum ([1, 1] : List (ZMod 3))
    exact pair_equal_has_pm 1
  · change HasNonemptyPlusMinusZeroSum ([1, 2] : List (ZMod 3))
    have hneg : -(1 : ZMod 3) = 2 := by decide
    simpa only [hneg] using pair_opposite_has_pm (1 : ZMod 3)
  · change HasNonemptyPlusMinusZeroSum ([2, 0] : List (ZMod 3))
    exact pair_second_zero_has_pm 2
  · change HasNonemptyPlusMinusZeroSum ([2, 1] : List (ZMod 3))
    have hneg : -(2 : ZMod 3) = 1 := by decide
    simpa only [hneg] using pair_opposite_has_pm (2 : ZMod 3)
  · change HasNonemptyPlusMinusZeroSum ([2, 2] : List (ZMod 3))
    exact pair_equal_has_pm 2

/-- The occurrence-sensitive plus-minus Davenport threshold of `C₃` is at
most two. -/
theorem zmod3_plusMinusDavenportAtMost_two :
    PlusMinusDavenportAtMost (ZMod 3) 2 := by
  intro s hs
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hs
  exact zmod3_pair_hasNonemptyPlusMinusZeroSum x y

/-- The one-term sequence `[1]` has no nonempty plus-minus zero sum in `C₃`. -/
theorem zmod3_singleton_one_no_plusMinusZeroSum :
    ¬ HasNonemptyPlusMinusZeroSum ([1] : List (ZMod 3)) := by
  rintro ⟨I, hI, sign, hsum⟩
  have hI_univ : I = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    fin_cases i
    rcases hI with ⟨j, hj⟩
    fin_cases j
    simpa using hj
  subst I
  change (∑ i : Fin 1, (sign i).act ([1].get i)) = 0 at hsum
  rw [Fin.sum_univ_one] at hsum
  cases h : sign 0 <;>
    norm_num [h, PlusMinusSign.act, occurrenceValue] at hsum

/-- Consequently the plus-minus Davenport threshold of `C₃` is not at most
one.  This is the concrete obstruction to the uniform A5 gap-two claim. -/
theorem zmod3_not_plusMinusDavenportAtMost_one :
    ¬ PlusMinusDavenportAtMost (ZMod 3) 1 := by
  intro h
  exact zmod3_singleton_one_no_plusMinusZeroSum (h [1] (by simp))

/-- The empty sequence has no nonempty selection. -/
theorem zmod3_empty_no_plusMinusZeroSum :
    ¬ HasNonemptyPlusMinusZeroSum ([] : List (ZMod 3)) := by
  rintro ⟨I, ⟨i, _hi⟩, _sign, _hsum⟩
  exact Fin.elim0 i

/-- In particular the threshold is not at most zero.  This is the concrete
`C₃` obstruction to any A6 raw bound forcing `D_±(C₃) ≤ 0`. -/
theorem zmod3_not_plusMinusDavenportAtMost_zero :
    ¬ PlusMinusDavenportAtMost (ZMod 3) 0 := by
  intro h
  exact zmod3_empty_no_plusMinusZeroSum (h [] rfl)

/-- Exact occurrence-sensitive threshold statement for `C₃`. -/
theorem zmod3_plusMinusDavenport_exact :
    PlusMinusDavenportAtMost (ZMod 3) 2 ∧
      ¬ PlusMinusDavenportAtMost (ZMod 3) 1 :=
  ⟨zmod3_plusMinusDavenportAtMost_two,
    zmod3_not_plusMinusDavenportAtMost_one⟩

end C3

end GaoLean

#print axioms GaoLean.zmod3_pair_hasNonemptyPlusMinusZeroSum
#print axioms GaoLean.zmod3_plusMinusDavenportAtMost_two
#print axioms GaoLean.zmod3_singleton_one_no_plusMinusZeroSum
#print axioms GaoLean.zmod3_not_plusMinusDavenportAtMost_one
#print axioms GaoLean.zmod3_empty_no_plusMinusZeroSum
#print axioms GaoLean.zmod3_not_plusMinusDavenportAtMost_zero
#print axioms GaoLean.zmod3_plusMinusDavenport_exact
