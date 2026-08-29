import GaoLean.PGGeneralWeightedDefinitions
import GaoLean.GAOARDihedralBlocks

/-!
# Transport of general weighted sums along occurrence subsequences

The occurrence-subsequence construction remembers the exact source position
of every retained term.  This file records that an exact weighted selection
on such a subsequence lifts, without changing either its cardinality or its
weighted sum, to the original source list.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A]

/-- Extend weights from an occurrence subsequence to the original list.
Outside the image of the occurrence-source map the value is immaterial and is
set to zero. -/
noncomputable def liftOccurrenceSubsequenceWeights
    (xs : List A) (R : Selection xs)
    (weights : Occurrence (occurrenceSubsequence xs R) → ℤ) :
    Occurrence xs → ℤ := by
  classical
  intro i
  by_cases hi : ∃ j, occurrenceSubsequenceSource xs R j = i
  · exact weights (Classical.choose hi)
  · exact 0

theorem liftOccurrenceSubsequenceWeights_source
    (xs : List A) (R : Selection xs)
    (weights : Occurrence (occurrenceSubsequence xs R) → ℤ)
    (j : Occurrence (occurrenceSubsequence xs R)) :
    liftOccurrenceSubsequenceWeights xs R weights
        (occurrenceSubsequenceSource xs R j) = weights j := by
  classical
  have hj : ∃ k, occurrenceSubsequenceSource xs R k =
      occurrenceSubsequenceSource xs R j := ⟨j, rfl⟩
  simp only [liftOccurrenceSubsequenceWeights, dif_pos hj]
  congr 1
  exact occurrenceSubsequenceSource_injective xs R
    (Classical.choose_spec hj)

/-- The lifted selection lies in the retained source selection and has the
same cardinality.  This packages the two occurrence-level facts already
proved for `liftOccurrenceSubsequenceSelection`. -/
theorem liftOccurrenceSubsequenceSelection_subset_and_card
    (xs : List A) (R : Selection xs)
    (I : Selection (occurrenceSubsequence xs R)) :
    liftOccurrenceSubsequenceSelection xs R I ⊆ R ∧
      (liftOccurrenceSubsequenceSelection xs R I).card = I.card := by
  exact ⟨liftOccurrenceSubsequenceSelection_subset xs R I,
    card_liftOccurrenceSubsequenceSelection xs R I⟩

/-- Lifting a selected family preserves its integer-weighted sum. -/
theorem weightedSum_liftOccurrenceSubsequenceSelection
    (xs : List A) (R : Selection xs)
    (I : Selection (occurrenceSubsequence xs R))
    (weights : Occurrence (occurrenceSubsequence xs R) → ℤ) :
    (∑ i ∈ liftOccurrenceSubsequenceSelection xs R I,
        liftOccurrenceSubsequenceWeights xs R weights i •
          occurrenceValue xs i) =
      ∑ j ∈ I, weights j •
        occurrenceValue (occurrenceSubsequence xs R) j := by
  classical
  unfold liftOccurrenceSubsequenceSelection
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  change liftOccurrenceSubsequenceWeights xs R weights
      (occurrenceSubsequenceSource xs R j) •
        occurrenceValue xs (occurrenceSubsequenceSource xs R j) = _
  rw [liftOccurrenceSubsequenceWeights_source,
    occurrenceValue_occurrenceSubsequence]

/-- Every exact weighted sum on an occurrence subsequence is an exact
weighted sum of the same cardinality and value on the original list. -/
noncomputable def HasWeightedSumOfCard.liftOccurrenceSubsequence
    {W : Set ℤ} {xs : List A} {R : Selection xs} {n : ℕ} {y : A}
    (h : HasWeightedSumOfCard W (occurrenceSubsequence xs R) n y) :
    HasWeightedSumOfCard W xs n y where
  selected := liftOccurrenceSubsequenceSelection xs R h.selected
  weights := liftOccurrenceSubsequenceWeights xs R h.weights
  weights_mem := by
    classical
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    change liftOccurrenceSubsequenceWeights xs R h.weights
      (occurrenceSubsequenceSource xs R j) ∈ W
    rw [liftOccurrenceSubsequenceWeights_source]
    exact h.weights_mem j hj
  card_selected := by
    rw [card_liftOccurrenceSubsequenceSelection, h.card_selected]
  weighted_sum := by
    rw [weightedSum_liftOccurrenceSubsequenceSelection, h.weighted_sum]

section FiniteAmbient

variable [Fintype A]

/-- Passing to an occurrence subsequence can only shrink an exact weighted
spectrum. -/
theorem weightedExactSpectrum_occurrenceSubsequence_subset
    (W : Set ℤ) (xs : List A) (R : Selection xs) (n : ℕ) :
    weightedExactSpectrum W (occurrenceSubsequence xs R) n ⊆
      weightedExactSpectrum W xs n := by
  intro y hy
  rw [mem_weightedExactSpectrum_iff] at hy ⊢
  exact hy.map HasWeightedSumOfCard.liftOccurrenceSubsequence

end FiniteAmbient

end GaoLean

#print axioms GaoLean.liftOccurrenceSubsequenceWeights_source
#print axioms GaoLean.liftOccurrenceSubsequenceSelection_subset_and_card
#print axioms GaoLean.weightedSum_liftOccurrenceSubsequenceSelection
#print axioms GaoLean.HasWeightedSumOfCard.liftOccurrenceSubsequence
#print axioms GaoLean.weightedExactSpectrum_occurrenceSubsequence_subset
