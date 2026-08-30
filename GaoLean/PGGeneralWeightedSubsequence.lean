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

/-- The source-occurrence map is an equivalence from occurrences of the
subsequence to the subtype of original occurrences selected by `R`. -/
noncomputable def occurrenceSubsequenceEquivSelection
    (xs : List A) (R : Selection xs) :
    Occurrence (occurrenceSubsequence xs R) ≃
      {i : Occurrence xs // i ∈ R} := by
  classical
  let f : Occurrence (occurrenceSubsequence xs R) →
      {i : Occurrence xs // i ∈ R} := fun j ↦
    ⟨occurrenceSubsequenceSource xs R j,
      occurrenceSubsequenceSource_mem xs R j⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).2
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact occurrenceSubsequenceSource_injective xs R
      (congrArg Subtype.val hij)
  · simp [f, Occurrence, occurrenceSubsequence,
      Nat.card_eq_fintype_card]

@[simp]
theorem occurrenceSubsequenceEquivSelection_val
    (xs : List A) (R : Selection xs)
    (j : Occurrence (occurrenceSubsequence xs R)) :
    (occurrenceSubsequenceEquivSelection xs R j).1 =
      occurrenceSubsequenceSource xs R j :=
  rfl

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

/-- Restrict an ambient exact weighted-sum witness to an occurrence
subsequence when every selected source label lies in the retained selection.
This is the inverse transport to `liftOccurrenceSubsequence` on supported
witnesses; equal source values remain distinct because the equivalence is on
occurrence labels. -/
noncomputable def HasWeightedSumOfCard.restrictOccurrenceSubsequence
    {W : Set ℤ} {xs : List A} {R : Selection xs} {n : ℕ} {y : A}
    (h : HasWeightedSumOfCard W xs n y)
    (hsub : h.selected ⊆ R) :
    HasWeightedSumOfCard W (occurrenceSubsequence xs R) n y := by
  classical
  let e := occurrenceSubsequenceEquivSelection xs R
  let emb : {i : Occurrence xs // i ∈ h.selected} ↪
      Occurrence (occurrenceSubsequence xs R) := {
    toFun := fun i ↦ e.symm ⟨i.1, hsub i.2⟩
    inj' := by
      intro i j hij
      apply Subtype.ext
      have := congrArg e hij
      simpa using congrArg (fun q ↦ q.1) this
  }
  let selected : Selection (occurrenceSubsequence xs R) :=
    h.selected.attach.map emb
  let weights : Occurrence (occurrenceSubsequence xs R) → ℤ :=
    fun j ↦ h.weights (e j).1
  refine {
    selected := selected
    weights := weights
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro j hj
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hj
    change h.weights (e (e.symm ⟨i.1, hsub i.2⟩)).1 ∈ W
    rw [e.apply_symm_apply]
    exact h.weights_mem i.1 i.2
  · simp [selected, h.card_selected]
  · rw [show
        (∑ j ∈ selected,
          weights j • occurrenceValue (occurrenceSubsequence xs R) j) =
          ∑ i ∈ h.selected,
            h.weights i • occurrenceValue xs i by
      unfold selected
      rw [Finset.sum_map]
      rw [Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro i hi
      have he : e (e.symm ⟨i, hsub hi⟩) = ⟨i, hsub hi⟩ :=
        e.apply_symm_apply ⟨i, hsub hi⟩
      have hsrc : occurrenceSubsequenceSource xs R
          (e.symm ⟨i, hsub hi⟩) = i := by
        change (e (e.symm ⟨i, hsub hi⟩)).1 = i
        exact congrArg Subtype.val he
      simp [weights, emb, occurrenceValue_occurrenceSubsequence,
        he, hsrc]]
    exact h.weighted_sum

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
#print axioms GaoLean.occurrenceSubsequenceEquivSelection_val
#print axioms GaoLean.liftOccurrenceSubsequenceSelection_subset_and_card
#print axioms GaoLean.weightedSum_liftOccurrenceSubsequenceSelection
#print axioms GaoLean.HasWeightedSumOfCard.liftOccurrenceSubsequence
#print axioms GaoLean.HasWeightedSumOfCard.restrictOccurrenceSubsequence
#print axioms GaoLean.weightedExactSpectrum_occurrenceSubsequence_subset
