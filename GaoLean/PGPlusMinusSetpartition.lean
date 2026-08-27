import GaoLean.PGGMOSpectrum
import GaoLean.PGIteratedKneser
import GaoLean.PGDGMCore

/-!
# The `{+1,-1}` occurrence setpartition

Each source occurrence is kept as its own labelled layer and contributes the
finite block `{x,-x}`.  Repeated source values therefore give repeated layers,
not one collapsed layer.  The exact-`n` block spectrum below selects `n`
distinct occurrence layers and one element from each selected block.

The main equivalence proves that this literal union-of-`n`-sums is exactly the
existing `plusMinusExactSpectrum`: a block choice splits into disjoint positive
and negative occurrence sets, and conversely such a signed selection chooses
one member of every selected block.
-/

namespace GaoLean

open scoped BigOperators Pointwise

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The finite signed image `{x,-x}` of one value. -/
noncomputable def plusMinusValueBlock (x : A) : Finset A := by
  classical
  exact {x, -x}

/-- The two signed images contributed by one labelled source occurrence. -/
noncomputable def plusMinusOccurrenceBlock
    (xs : List A) (i : Occurrence xs) : Finset A :=
  plusMinusValueBlock (occurrenceValue xs i)

@[simp]
theorem mem_plusMinusOccurrenceBlock_iff
    (xs : List A) (i : Occurrence xs) (y : A) :
    y ∈ plusMinusOccurrenceBlock xs i ↔
      y = occurrenceValue xs i ∨ y = -occurrenceValue xs i := by
  classical
  simp [plusMinusOccurrenceBlock, plusMinusValueBlock]

theorem plusMinusOccurrenceBlock_nonempty
    (xs : List A) (i : Occurrence xs) :
    (plusMinusOccurrenceBlock xs i).Nonempty := by
  exact ⟨occurrenceValue xs i, by simp⟩

/-- The full list of signed occurrence blocks.  `List.map` preserves repeated
layers, so equal values at different positions remain distinct inputs to the
finite-list Kneser construction. -/
noncomputable def plusMinusOccurrenceSetpartition (xs : List A) :
    List (Finset A) :=
  xs.map plusMinusValueBlock

@[simp]
theorem length_plusMinusOccurrenceSetpartition (xs : List A) :
    (plusMinusOccurrenceSetpartition xs).length = xs.length := by
  classical
  simp [plusMinusOccurrenceSetpartition]

@[simp]
theorem plusMinusOccurrenceSetpartition_nil :
    plusMinusOccurrenceSetpartition ([] : List A) = [] := by
  simp [plusMinusOccurrenceSetpartition]

@[simp]
theorem plusMinusOccurrenceSetpartition_cons (x : A) (xs : List A) :
    plusMinusOccurrenceSetpartition (x :: xs) =
      plusMinusValueBlock x :: plusMinusOccurrenceSetpartition xs := by
  simp [plusMinusOccurrenceSetpartition]

/-- The signed block attached to position `i` is literally the `i`-th layer
of the occurrence setpartition. -/
theorem get_plusMinusOccurrenceSetpartition
    (xs : List A) (i : Occurrence xs) :
    (plusMinusOccurrenceSetpartition xs).get
        ⟨i.1, by simpa using i.2⟩ =
      plusMinusOccurrenceBlock xs i := by
  classical
  simp [plusMinusOccurrenceSetpartition, plusMinusOccurrenceBlock,
    occurrenceValue]

/-- Every layer of the occurrence setpartition is nonempty, in precisely the
hypothesis shape used by `iteratedFinsetSum_nonempty` and iterated Kneser. -/
theorem plusMinusOccurrenceSetpartition_nonempty
    (xs : List A) :
    ∀ B ∈ plusMinusOccurrenceSetpartition xs, B.Nonempty := by
  classical
  intro B hB
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hB
  exact ⟨x, by simp [plusMinusValueBlock]⟩

/-- The full finite-list sumset is nonempty, a direct specialization of the
`PGIteratedKneser` vocabulary. -/
theorem iteratedFinsetSum_plusMinusOccurrenceSetpartition_nonempty
    (xs : List A) [DecidableEq A] :
    (iteratedFinsetSum (plusMinusOccurrenceSetpartition xs)).Nonempty :=
  iteratedFinsetSum_nonempty _
    (plusMinusOccurrenceSetpartition_nonempty xs)

/-- Iterated Kneser specialized to the complete list of signed occurrence
blocks.  This is the finite-set inequality available to the later DGM layer. -/
theorem plusMinusOccurrenceSetpartition_iteratedKneser
    (xs : List A) [DecidableEq A] :
    (((plusMinusOccurrenceSetpartition xs).map fun B ↦
          (B + (iteratedFinsetSum
            (plusMinusOccurrenceSetpartition xs)).addStab).card).sum +
        (iteratedFinsetSum
          (plusMinusOccurrenceSetpartition xs)).addStab.card) ≤
      (iteratedFinsetSum
          (plusMinusOccurrenceSetpartition xs)).card +
        (plusMinusOccurrenceSetpartition xs).length *
          (iteratedFinsetSum
            (plusMinusOccurrenceSetpartition xs)).addStab.card := by
  classical
  exact sum_card_addStab_add_card_addStab_le
    (plusMinusOccurrenceSetpartition xs)
      (plusMinusOccurrenceSetpartition_nonempty xs)

/-- A literal choice of `n` labelled blocks and one signed value from each.
The function `chosenValue` is relevant only on `selected`; its membership
field prevents it from supplying any value outside the occurrence's block. -/
structure PlusMinusSetpartitionChoice
    (xs : List A) (n : ℕ) (y : A) where
  selected : Selection xs
  card_selected : selected.card = n
  chosenValue : Occurrence xs → A
  chosenValue_mem :
    ∀ i ∈ selected, chosenValue i ∈ plusMinusOccurrenceBlock xs i
  sum_chosen : ∑ i ∈ selected, chosenValue i = y

namespace PlusMinusSetpartitionChoice

/-- Remove the head occurrence and relabel every remaining selected occurrence
by its tail index. -/
noncomputable def tailSelection {x : A} {xs : List A}
    (I : Selection (x :: xs)) : Selection xs := by
  classical
  exact Finset.univ.filter fun j ↦ j.succ ∈ I

/-- Relabel a tail selection as occurrences of a list with one new head. -/
def liftTailSelection {x : A} {xs : List A}
    (I : Selection xs) : Selection (x :: xs) :=
  I.map ⟨Fin.succ, Fin.succ_injective _⟩

@[simp]
theorem mem_tailSelection_iff {x : A} {xs : List A}
    (I : Selection (x :: xs)) (j : Occurrence xs) :
    j ∈ tailSelection I ↔ j.succ ∈ I := by
  classical
  simp [tailSelection]

@[simp]
theorem mem_liftTailSelection_iff {x : A} {xs : List A}
    (I : Selection xs) (j : Occurrence xs) :
    j.succ ∈ liftTailSelection (x := x) I ↔ j ∈ I := by
  classical
  simp [liftTailSelection]

@[simp]
theorem zero_not_mem_liftTailSelection {x : A} {xs : List A}
    (I : Selection xs) :
    (0 : Occurrence (x :: xs)) ∉ liftTailSelection (x := x) I := by
  classical
  simp [liftTailSelection]

@[simp]
theorem card_liftTailSelection {x : A} {xs : List A}
    (I : Selection xs) :
    (liftTailSelection (x := x) I).card = I.card := by
  exact Finset.card_map _

/-- Lifting the tail part of a selection is the same as erasing its head. -/
theorem lift_tailSelection_eq_erase_zero {x : A} {xs : List A}
    (I : Selection (x :: xs)) :
    liftTailSelection (x := x) (tailSelection I) = I.erase 0 := by
  classical
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

theorem card_tailSelection_of_not_mem_zero {x : A} {xs : List A}
    (I : Selection (x :: xs)) (hzero : (0 : Occurrence (x :: xs)) ∉ I) :
    (tailSelection I).card = I.card := by
  rw [← card_liftTailSelection (x := x),
    lift_tailSelection_eq_erase_zero, Finset.erase_eq_of_notMem hzero]

theorem card_tailSelection_of_mem_zero {x : A} {xs : List A}
    (I : Selection (x :: xs)) (hzero : (0 : Occurrence (x :: xs)) ∈ I) :
    (tailSelection I).card + 1 = I.card := by
  rw [← card_liftTailSelection (x := x),
    lift_tailSelection_eq_erase_zero, Finset.card_erase_of_mem hzero]
  have hpos : 0 < I.card := Finset.card_pos.mpr ⟨0, hzero⟩
  omega

/-- Reindexing the tail does not change its finite sum. -/
theorem sum_tailSelection {x : A} {xs : List A}
    (I : Selection (x :: xs)) (f : Occurrence (x :: xs) → A) :
    (∑ j ∈ tailSelection I, f j.succ) =
      ∑ i ∈ I.erase 0, f i := by
  classical
  rw [← lift_tailSelection_eq_erase_zero (x := x) I]
  simp [liftTailSelection]

end PlusMinusSetpartitionChoice

/-- Union of all sums obtained from exactly `n` distinct labelled occurrence
blocks, choosing one element from each block. -/
noncomputable def plusMinusSetpartitionSpectrum
    (xs : List A) (n : ℕ) : Finset A := by
  classical
  exact Finset.univ.filter fun y ↦
    Nonempty (PlusMinusSetpartitionChoice xs n y)

@[simp]
theorem mem_plusMinusSetpartitionSpectrum_iff
    (xs : List A) (n : ℕ) (y : A) :
    y ∈ plusMinusSetpartitionSpectrum xs n ↔
      Nonempty (PlusMinusSetpartitionChoice xs n y) := by
  classical
  simp [plusMinusSetpartitionSpectrum]

/-- The literal block spectrum obeys the same skip/take recursion as DGM's
`layerSubsumSpectrum`: either the head occurrence is not selected, or one of
its two signed values is added to an exact tail choice. -/
theorem plusMinusSetpartitionSpectrum_cons_succ
    (x : A) (xs : List A) (n : ℕ) [DecidableEq A] :
    plusMinusSetpartitionSpectrum (x :: xs) (n + 1) =
      plusMinusSetpartitionSpectrum xs (n + 1) ∪
        (plusMinusValueBlock x + plusMinusSetpartitionSpectrum xs n) := by
  classical
  ext y
  simp only [mem_plusMinusSetpartitionSpectrum_iff, Finset.mem_union]
  constructor
  · rintro ⟨h⟩
    by_cases hzero : (0 : Occurrence (x :: xs)) ∈ h.selected
    · right
      let J := PlusMinusSetpartitionChoice.tailSelection h.selected
      let f : Occurrence xs → A := fun j ↦ h.chosenValue j.succ
      let w : A := ∑ j ∈ J, f j
      have hJcard : J.card = n := by
        have hc := PlusMinusSetpartitionChoice.card_tailSelection_of_mem_zero
          h.selected hzero
        change J.card + 1 = h.selected.card at hc
        rw [h.card_selected] at hc
        omega
      have hJmem : ∀ j ∈ J,
          f j ∈ plusMinusOccurrenceBlock xs j := by
        intro j hj
        have hjsucc : j.succ ∈ h.selected :=
          (PlusMinusSetpartitionChoice.mem_tailSelection_iff
            h.selected j).1 hj
        simpa [f, plusMinusOccurrenceBlock, occurrenceValue] using
          h.chosenValue_mem j.succ hjsucc
      have htail : PlusMinusSetpartitionChoice xs n w := {
        selected := J
        card_selected := hJcard
        chosenValue := f
        chosenValue_mem := hJmem
        sum_chosen := rfl
      }
      have hheadBlock : h.chosenValue 0 ∈ plusMinusValueBlock x := by
        simpa [plusMinusOccurrenceBlock, occurrenceValue] using
          h.chosenValue_mem 0 hzero
      have htailSpectrum : w ∈ plusMinusSetpartitionSpectrum xs n :=
        (mem_plusMinusSetpartitionSpectrum_iff xs n w).2 ⟨htail⟩
      have hsumTail :
          w = ∑ i ∈ h.selected.erase 0, h.chosenValue i := by
        dsimp only [w, J, f]
        exact PlusMinusSetpartitionChoice.sum_tailSelection
          h.selected h.chosenValue
      have hy : h.chosenValue 0 + w = y := by
        calc
          h.chosenValue 0 + w =
              h.chosenValue 0 +
                ∑ i ∈ h.selected.erase 0, h.chosenValue i := by
                  rw [hsumTail]
          _ = ∑ i ∈ h.selected, h.chosenValue i := by
                rw [add_comm]
                exact h.selected.sum_erase_add h.chosenValue hzero
          _ = y := h.sum_chosen
      exact Finset.mem_add.mpr
        ⟨h.chosenValue 0, hheadBlock, w, htailSpectrum, hy⟩
    · left
      let J := PlusMinusSetpartitionChoice.tailSelection h.selected
      let f : Occurrence xs → A := fun j ↦ h.chosenValue j.succ
      have hJcard : J.card = n + 1 := by
        rw [PlusMinusSetpartitionChoice.card_tailSelection_of_not_mem_zero
          h.selected hzero]
        exact h.card_selected
      have hJmem : ∀ j ∈ J,
          f j ∈ plusMinusOccurrenceBlock xs j := by
        intro j hj
        have hjsucc : j.succ ∈ h.selected :=
          (PlusMinusSetpartitionChoice.mem_tailSelection_iff
            h.selected j).1 hj
        simpa [f, plusMinusOccurrenceBlock, occurrenceValue] using
          h.chosenValue_mem j.succ hjsucc
      have hJsum : ∑ j ∈ J, f j = y := by
        calc
          (∑ j ∈ J, f j) =
              ∑ i ∈ h.selected.erase 0, h.chosenValue i := by
                exact PlusMinusSetpartitionChoice.sum_tailSelection
                  h.selected h.chosenValue
          _ = ∑ i ∈ h.selected, h.chosenValue i := by
                rw [Finset.erase_eq_of_notMem hzero]
          _ = y := h.sum_chosen
      exact ⟨{
        selected := J
        card_selected := hJcard
        chosenValue := f
        chosenValue_mem := hJmem
        sum_chosen := hJsum
      }⟩
  · rintro (htail | htake)
    · obtain ⟨h⟩ := htail
      let J := PlusMinusSetpartitionChoice.liftTailSelection
        (x := x) h.selected
      let f : Occurrence (x :: xs) → A :=
        Fin.cases 0 h.chosenValue
      refine ⟨{
        selected := J
        card_selected := ?_
        chosenValue := f
        chosenValue_mem := ?_
        sum_chosen := ?_
      }⟩
      · simpa [J] using h.card_selected
      · intro i hi
        induction i using Fin.cases with
        | zero =>
          exact (PlusMinusSetpartitionChoice.zero_not_mem_liftTailSelection
            (x := x) h.selected hi).elim
        | succ j =>
          have hj : j ∈ h.selected :=
            (PlusMinusSetpartitionChoice.mem_liftTailSelection_iff
              (x := x) h.selected j).1 hi
          simpa [f, plusMinusOccurrenceBlock, occurrenceValue] using
            h.chosenValue_mem j hj
      · simpa [J, f, PlusMinusSetpartitionChoice.liftTailSelection]
          using h.sum_chosen
    · rcases Finset.mem_add.mp htake with ⟨z, hz, w, hw, rfl⟩
      obtain ⟨h⟩ :=
        (mem_plusMinusSetpartitionSpectrum_iff xs n w).1 hw
      let J := PlusMinusSetpartitionChoice.liftTailSelection
        (x := x) h.selected
      let I : Selection (x :: xs) :=
        Finset.cons 0 J
          (PlusMinusSetpartitionChoice.zero_not_mem_liftTailSelection
            (x := x) h.selected)
      let f : Occurrence (x :: xs) → A :=
        Fin.cases z h.chosenValue
      refine ⟨{
        selected := I
        card_selected := ?_
        chosenValue := f
        chosenValue_mem := ?_
        sum_chosen := ?_
      }⟩
      · simp [I, J, h.card_selected]
      · intro i hi
        induction i using Fin.cases with
        | zero =>
          simpa [f, plusMinusOccurrenceBlock, occurrenceValue] using hz
        | succ j =>
          have hj : j ∈ h.selected := by
            have hjsucc : j.succ ∈ J := by
              simpa [I] using hi
            exact (PlusMinusSetpartitionChoice.mem_liftTailSelection_iff
              (x := x) h.selected j).1 hjsucc
          simpa [f, plusMinusOccurrenceBlock, occurrenceValue] using
            h.chosenValue_mem j hj
      · simp [I, J, f, PlusMinusSetpartitionChoice.liftTailSelection,
          h.sum_chosen]

@[simp]
theorem plusMinusSetpartitionSpectrum_zero (xs : List A) :
    plusMinusSetpartitionSpectrum xs 0 = {0} := by
  classical
  ext y
  rw [mem_plusMinusSetpartitionSpectrum_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨h⟩
    have hselected : h.selected = ∅ := Finset.card_eq_zero.mp h.card_selected
    have hsum : (0 : A) = y := by
      simpa [hselected] using h.sum_chosen
    exact hsum.symm
  · rintro rfl
    exact ⟨{
      selected := ∅
      card_selected := by simp
      chosenValue := fun _ ↦ 0
      chosenValue_mem := by simp
      sum_chosen := by simp
    }⟩

@[simp]
theorem plusMinusSetpartitionSpectrum_nil_succ (n : ℕ) :
    plusMinusSetpartitionSpectrum ([] : List A) (n + 1) = ∅ := by
  classical
  ext y
  rw [mem_plusMinusSetpartitionSpectrum_iff]
  constructor
  · rintro ⟨h⟩
    have hselected : h.selected = ∅ := by
      ext i
      exact Fin.elim0 i
    have hzero : 0 = n + 1 := by
      simpa [hselected] using h.card_selected
    omega
  · intro h
    simpa using h

/-- The occurrence-choice spectrum is literally DGM's exact-`n`
`layerSubsumSpectrum` for the signed occurrence setpartition.  This is the
bridge which lets DGM finite-set inequalities speak about the manuscript's
labelled signed spectrum. -/
theorem plusMinusSetpartitionSpectrum_eq_layerSubsumSpectrum
    (xs : List A) (n : ℕ) [DecidableEq A] :
    plusMinusSetpartitionSpectrum xs n =
      layerSubsumSpectrum (plusMinusOccurrenceSetpartition xs) n := by
  classical
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero => simp
      | succ n => simp [Nat.succ_eq_add_one]
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [show n + 1 = Nat.succ n by omega,
            plusMinusSetpartitionSpectrum_cons_succ,
            plusMinusOccurrenceSetpartition_cons,
            layerSubsumSpectrum_cons_succ,
            ih, ih]

/-- Split a signed block choice into positive and negative occurrence sets.
The two filters partition the exact selected set, so disjointness and exact
cardinality are consequences rather than extra assumptions. -/
noncomputable def hasPlusMinusSumOfCard_of_setpartitionChoice
    {xs : List A} {n : ℕ} {y : A}
    (h : PlusMinusSetpartitionChoice xs n y) :
    HasPlusMinusSumOfCard xs n y := by
  classical
  let P := h.selected.filter fun i ↦
    h.chosenValue i = occurrenceValue xs i
  let N := h.selected.filter fun i ↦
    h.chosenValue i ≠ occurrenceValue xs i
  refine {
    positive := P
    negative := N
    disjoint := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · exact Finset.disjoint_filter_filter_not h.selected h.selected _
  · dsimp only [P, N]
    rw [Finset.card_filter_add_card_filter_not, h.card_selected]
  · have hpositive :
        (∑ i ∈ P, occurrenceValue xs i) =
          ∑ i ∈ P, h.chosenValue i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Finset.mem_filter.mp hi).2.symm
    have hnegative :
        -(∑ i ∈ N, occurrenceValue xs i) =
          ∑ i ∈ N, h.chosenValue i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hiSelected : i ∈ h.selected := (Finset.mem_filter.mp hi).1
      have hiNotPositive :
          h.chosenValue i ≠ occurrenceValue xs i :=
        (Finset.mem_filter.mp hi).2
      rcases (mem_plusMinusOccurrenceBlock_iff
        xs i (h.chosenValue i)).1
          (h.chosenValue_mem i hiSelected) with hpos | hneg
      · exact (hiNotPositive hpos).elim
      · exact hneg.symm
    rw [sub_eq_add_neg, hpositive, hnegative]
    calc
      (∑ i ∈ P, h.chosenValue i) +
          ∑ i ∈ N, h.chosenValue i =
          ∑ i ∈ h.selected, h.chosenValue i := by
            dsimp only [P, N]
            exact Finset.sum_filter_add_sum_filter_not _ _ _
      _ = y := h.sum_chosen

/-- Conversely, disjoint positive and negative occurrence selections choose
one element from each selected signed block. -/
noncomputable def setpartitionChoice_of_hasPlusMinusSumOfCard
    {xs : List A} {n : ℕ} {y : A}
    (h : HasPlusMinusSumOfCard xs n y) :
    PlusMinusSetpartitionChoice xs n y := by
  classical
  let I := h.positive ∪ h.negative
  let choose : Occurrence xs → A := fun i ↦
    if i ∈ h.positive then occurrenceValue xs i
    else -occurrenceValue xs i
  refine {
    selected := I
    card_selected := ?_
    chosenValue := choose
    chosenValue_mem := ?_
    sum_chosen := ?_
  }
  · dsimp only [I]
    rw [Finset.card_union_of_disjoint h.disjoint, h.card_selected]
  · intro i hi
    simp only [I, Finset.mem_union] at hi
    rcases hi with hiPositive | hiNegative
    · simp [choose, hiPositive, plusMinusOccurrenceBlock,
        plusMinusValueBlock]
    · have hiNotPositive : i ∉ h.positive := by
        intro hiPositive
        exact Finset.disjoint_left.mp h.disjoint hiPositive hiNegative
      simp [choose, hiNotPositive, plusMinusOccurrenceBlock,
        plusMinusValueBlock]
  · dsimp only [I]
    rw [Finset.sum_union h.disjoint]
    have hpositive :
        (∑ i ∈ h.positive, choose i) =
          ∑ i ∈ h.positive, occurrenceValue xs i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [choose, hi]
    have hnegative :
        (∑ i ∈ h.negative, choose i) =
          -(∑ i ∈ h.negative, occurrenceValue xs i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hiNotPositive : i ∉ h.positive := by
        intro hiPositive
        exact Finset.disjoint_left.mp h.disjoint hiPositive hi
      simp [choose, hiNotPositive]
    rw [hpositive, hnegative, ← sub_eq_add_neg]
    exact h.weighted_sum

theorem nonempty_setpartitionChoice_iff_hasPlusMinusSumOfCard
    (xs : List A) (n : ℕ) (y : A) :
    Nonempty (PlusMinusSetpartitionChoice xs n y) ↔
      Nonempty (HasPlusMinusSumOfCard xs n y) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨hasPlusMinusSumOfCard_of_setpartitionChoice h⟩
  · rintro ⟨h⟩
    exact ⟨setpartitionChoice_of_hasPlusMinusSumOfCard h⟩

/-- Exact identification of the labelled `{+1,-1}` block spectrum with the
signed occurrence spectrum used by the GMO interfaces. -/
theorem plusMinusSetpartitionSpectrum_eq_plusMinusExactSpectrum
    (xs : List A) (n : ℕ) :
    plusMinusSetpartitionSpectrum xs n = plusMinusExactSpectrum xs n := by
  classical
  ext y
  rw [mem_plusMinusSetpartitionSpectrum_iff,
    mem_plusMinusExactSpectrum_iff]
  exact nonempty_setpartitionChoice_iff_hasPlusMinusSumOfCard xs n y

/-- Direct DGM-facing form: the manuscript's exact signed occurrence spectrum
is the exact-`n` layer spectrum of the `{x,-x}` occurrence setpartition. -/
theorem plusMinusExactSpectrum_eq_layerSubsumSpectrum
    (xs : List A) (n : ℕ) [DecidableEq A] :
    plusMinusExactSpectrum xs n =
      layerSubsumSpectrum (plusMinusOccurrenceSetpartition xs) n := by
  rw [← plusMinusSetpartitionSpectrum_eq_plusMinusExactSpectrum xs n,
    plusMinusSetpartitionSpectrum_eq_layerSubsumSpectrum]

/-- Membership-level form of the same exact equivalence. -/
theorem mem_plusMinusExactSpectrum_iff_setpartitionChoice
    (xs : List A) (n : ℕ) (y : A) :
    y ∈ plusMinusExactSpectrum xs n ↔
      Nonempty (PlusMinusSetpartitionChoice xs n y) := by
  rw [← plusMinusSetpartitionSpectrum_eq_plusMinusExactSpectrum xs n,
    mem_plusMinusSetpartitionSpectrum_iff]

end GaoLean

#print axioms GaoLean.plusMinusOccurrenceSetpartition_iteratedKneser
#print axioms GaoLean.hasPlusMinusSumOfCard_of_setpartitionChoice
#print axioms GaoLean.setpartitionChoice_of_hasPlusMinusSumOfCard
#print axioms GaoLean.plusMinusSetpartitionSpectrum_eq_layerSubsumSpectrum
#print axioms GaoLean.plusMinusSetpartitionSpectrum_eq_plusMinusExactSpectrum
#print axioms GaoLean.plusMinusExactSpectrum_eq_layerSubsumSpectrum
