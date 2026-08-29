import GaoLean.PGGeneralWeightedDefinitions
import GaoLean.PGGMOOrdinaryDGMSingleton
import GaoLean.PGGMOProvidersFromDGM

/-!
# General integer-weighted occurrence layers and DGM

This module identifies the exact occurrence-labelled `W`-weighted spectrum
with the exact-layer spectrum of the literal weighted occurrence
setpartition.  The weight set remains an arbitrary `Set ℤ`; finiteness of
each block comes from the finite ambient group, not from enumerating `W`.

The final theorem applies the already proved double-induction form of General
DGM.  Thus its only hypotheses are nonemptiness of `W` and the usual feasible
positive layer cardinality.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

@[simp]
theorem weightedOccurrenceSetpartition_nil (W : Set ℤ) :
    weightedOccurrenceSetpartition W ([] : List A) = [] := by
  classical
  simp [weightedOccurrenceSetpartition]

@[simp]
theorem weightedOccurrenceSetpartition_cons
    (W : Set ℤ) (x : A) (xs : List A) :
    weightedOccurrenceSetpartition W (x :: xs) =
      weightedValueBlock W x :: weightedOccurrenceSetpartition W xs := by
  classical
  simp [weightedOccurrenceSetpartition]

@[simp]
theorem weightedExactSpectrum_nil_succ (W : Set ℤ) (n : ℕ) :
    weightedExactSpectrum W ([] : List A) (n + 1) = ∅ := by
  classical
  ext y
  rw [mem_weightedExactSpectrum_iff]
  constructor
  · rintro ⟨h⟩
    have hselected : h.selected = ∅ := by
      ext i
      exact Fin.elim0 i
    have hzero : 0 = n + 1 := by
      simpa [hselected] using h.card_selected
    omega
  · simp

/-! The exact weighted spectrum has the same skip/take recursion as the
literal weighted occurrence layers.  All transports below act on occurrence
indices, so repeated source values are never collapsed. -/

theorem weightedExactSpectrum_cons_succ
    (W : Set ℤ) (x : A) (xs : List A) (n : ℕ) [DecidableEq A] :
    weightedExactSpectrum W (x :: xs) (n + 1) =
      weightedExactSpectrum W xs (n + 1) ∪
        (weightedValueBlock W x + weightedExactSpectrum W xs n) := by
  classical
  ext y
  simp only [mem_weightedExactSpectrum_iff, Finset.mem_union]
  constructor
  · rintro ⟨h⟩
    by_cases hzero : (0 : Occurrence (x :: xs)) ∈ h.selected
    · right
      let J := ordinaryTailSelection h.selected
      let weights : Occurrence xs → ℤ := fun j ↦ h.weights j.succ
      let z : A :=
        ∑ j ∈ J, weights j • occurrenceValue xs j
      have hJcard : J.card = n := by
        have hc := card_ordinaryTailSelection_of_mem_zero h.selected hzero
        change J.card + 1 = h.selected.card at hc
        rw [h.card_selected] at hc
        omega
      have hJweights : ∀ j ∈ J, weights j ∈ W := by
        intro j hj
        exact h.weights_mem j.succ
          ((mem_ordinaryTailSelection_iff h.selected j).1 hj)
      have htail : HasWeightedSumOfCard W xs n z := {
        selected := J
        weights := weights
        weights_mem := hJweights
        card_selected := hJcard
        weighted_sum := rfl
      }
      have hz : z ∈ weightedExactSpectrum W xs n :=
        (mem_weightedExactSpectrum_iff W xs n z).2 ⟨htail⟩
      have hhead : h.weights 0 • x ∈ weightedValueBlock W x := by
        apply (mem_weightedValueBlock_iff W x _).2
        exact ⟨h.weights 0, h.weights_mem 0 hzero, rfl⟩
      have hsumTail :
          z = ∑ i ∈ h.selected.erase 0,
            h.weights i • occurrenceValue (x :: xs) i := by
        dsimp only [z, J, weights]
        simpa [occurrenceValue] using
          (sum_ordinaryTailSelection h.selected
            (fun i ↦ h.weights i • occurrenceValue (x :: xs) i))
      have hy : h.weights 0 • x + z = y := by
        calc
          h.weights 0 • x + z =
              h.weights 0 • occurrenceValue (x :: xs) 0 +
                ∑ i ∈ h.selected.erase 0,
                  h.weights i • occurrenceValue (x :: xs) i := by
                    rw [hsumTail]
                    simp [occurrenceValue]
          _ = ∑ i ∈ h.selected,
                h.weights i • occurrenceValue (x :: xs) i := by
              rw [add_comm]
              exact h.selected.sum_erase_add
                (fun i ↦ h.weights i • occurrenceValue (x :: xs) i)
                hzero
          _ = y := h.weighted_sum
      exact Finset.mem_add.mpr
        ⟨h.weights 0 • x, hhead, z, hz, hy⟩
    · left
      let J := ordinaryTailSelection h.selected
      let weights : Occurrence xs → ℤ := fun j ↦ h.weights j.succ
      have hJcard : J.card = n + 1 := by
        rw [card_ordinaryTailSelection_of_not_mem_zero h.selected hzero]
        exact h.card_selected
      have hJweights : ∀ j ∈ J, weights j ∈ W := by
        intro j hj
        exact h.weights_mem j.succ
          ((mem_ordinaryTailSelection_iff h.selected j).1 hj)
      have hJsum :
          (∑ j ∈ J, weights j • occurrenceValue xs j) = y := by
        calc
          (∑ j ∈ J, weights j • occurrenceValue xs j) =
              ∑ i ∈ h.selected.erase 0,
                h.weights i • occurrenceValue (x :: xs) i := by
                  dsimp only [J, weights]
                  simpa [occurrenceValue] using
                    (sum_ordinaryTailSelection h.selected
                      (fun i ↦ h.weights i •
                        occurrenceValue (x :: xs) i))
          _ = ∑ i ∈ h.selected,
                h.weights i • occurrenceValue (x :: xs) i := by
                  rw [Finset.erase_eq_of_notMem hzero]
          _ = y := h.weighted_sum
      exact ⟨{
        selected := J
        weights := weights
        weights_mem := hJweights
        card_selected := hJcard
        weighted_sum := hJsum
      }⟩
  · rintro (htail | htake)
    · obtain ⟨h⟩ := htail
      let I := ordinaryLiftTailSelection (x := x) h.selected
      let weights : Occurrence (x :: xs) → ℤ :=
        Fin.cases 0 h.weights
      refine ⟨{
        selected := I
        weights := weights
        weights_mem := ?_
        card_selected := ?_
        weighted_sum := ?_
      }⟩
      · intro i hi
        induction i using Fin.cases with
        | zero =>
            exact (zero_not_mem_ordinaryLiftTailSelection
              (x := x) h.selected hi).elim
        | succ j =>
            have hj : j ∈ h.selected :=
              (mem_ordinaryLiftTailSelection_iff
                (x := x) h.selected j).1 hi
            simpa [weights] using h.weights_mem j hj
      · simpa [I] using h.card_selected
      · simpa [I, weights, ordinaryLiftTailSelection, occurrenceValue]
          using h.weighted_sum
    · rcases Finset.mem_add.mp htake with ⟨a, ha, z, hz, haz⟩
      rcases (mem_weightedValueBlock_iff W x a).1 ha with
        ⟨w, hw, hwa⟩
      obtain ⟨h⟩ := (mem_weightedExactSpectrum_iff W xs n z).1 hz
      let J := ordinaryLiftTailSelection (x := x) h.selected
      let I : Selection (x :: xs) :=
        Finset.cons 0 J
          (zero_not_mem_ordinaryLiftTailSelection (x := x) h.selected)
      let weights : Occurrence (x :: xs) → ℤ :=
        Fin.cases w h.weights
      refine ⟨{
        selected := I
        weights := weights
        weights_mem := ?_
        card_selected := ?_
        weighted_sum := ?_
      }⟩
      · intro i hi
        induction i using Fin.cases with
        | zero => exact hw
        | succ j =>
            have hj : j ∈ h.selected := by
              have hjsucc : j.succ ∈ J := by
                simpa [I] using hi
              exact (mem_ordinaryLiftTailSelection_iff
                (x := x) h.selected j).1 hjsucc
            simpa [weights] using h.weights_mem j hj
      · simp [I, J, h.card_selected]
      · calc
          (∑ i ∈ I, weights i • occurrenceValue (x :: xs) i) =
              w • x + ∑ j ∈ h.selected,
                h.weights j • occurrenceValue xs j := by
                  simp [I, J, weights, ordinaryLiftTailSelection,
                    occurrenceValue]
          _ = a + z := by rw [h.weighted_sum, hwa]
          _ = y := haz

/-- The exact occurrence-labelled weighted spectrum is literally the DGM
exact-layer spectrum of the weighted occurrence setpartition. -/
theorem weightedExactSpectrum_eq_layerSubsumSpectrum
    (W : Set ℤ) (xs : List A) (n : ℕ) [DecidableEq A] :
    weightedExactSpectrum W xs n =
      layerSubsumSpectrum (weightedOccurrenceSetpartition W xs) n := by
  classical
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero => simp
      | succ n => simp
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
          rw [weightedExactSpectrum_cons_succ,
            weightedOccurrenceSetpartition_cons,
            layerSubsumSpectrum_cons_succ,
            ih, ih]

/-- Membership-level form of the exact weighted spectrum bridge. -/
theorem mem_weightedExactSpectrum_iff_mem_layerSubsumSpectrum
    (W : Set ℤ) (xs : List A) (n : ℕ) (y : A) [DecidableEq A] :
    y ∈ weightedExactSpectrum W xs n ↔
      y ∈ layerSubsumSpectrum (weightedOccurrenceSetpartition W xs) n := by
  rw [weightedExactSpectrum_eq_layerSubsumSpectrum]

/-- Every weighted occurrence layer is nonempty whenever the arbitrary weight
set has at least one element. -/
theorem weightedOccurrenceSetpartition_isNonempty
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) :
    IsNonemptySetPartition (weightedOccurrenceSetpartition W xs) :=
  weightedOccurrenceSetpartition_cells_nonempty hW xs

/-- General DGM, already proved by double induction, applies unconditionally
to every feasible exact layer of an arbitrary nonempty integer weight set. -/
theorem weightedOccurrenceSetpartition_dgmBound_of_doubleInduction
    (W : Set ℤ) (hW : W.Nonempty) (xs : List A) (n : ℕ)
    [instDecEq : DecidableEq A]
    (hnpos : 1 ≤ n) (hn : n ≤ xs.length) :
    DGMSetpartitionBound (weightedOccurrenceSetpartition W xs) n := by
  classical
  have hdec : instDecEq = Classical.decEq A := Subsingleton.elim _ _
  cases hdec
  exact (finiteDGMSetpartitionInput_of_doubleInduction A)
    (weightedOccurrenceSetpartition W xs) n
    (weightedOccurrenceSetpartition_isNonempty hW xs)
    hnpos (by simpa using hn)

end GaoLean

#print axioms GaoLean.weightedExactSpectrum_cons_succ
#print axioms GaoLean.weightedExactSpectrum_eq_layerSubsumSpectrum
#print axioms GaoLean.mem_weightedExactSpectrum_iff_mem_layerSubsumSpectrum
#print axioms GaoLean.weightedOccurrenceSetpartition_isNonempty
#print axioms GaoLean.weightedOccurrenceSetpartition_dgmBound_of_doubleInduction
