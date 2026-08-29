import GaoLean.PGGeneralWeightedDefinitions

/-!
# Occurrence-labelled convolution of general weighted selections

Two disjoint exact weighted selections on the same source can be joined
without losing occurrence identities.  The combined witness below records
the literal union of source positions and uses a piecewise weight function
which agrees with each original witness on its own selected positions.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A]

/-- Piecewise weight function for the union of two selections.  The left
weight is chosen on the left selection; outside it the right weight is used.
-/
def weightedSelectionUnionWeights
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (i : Occurrence xs) : ℤ :=
  if i ∈ h₁.selected then h₁.weights i else h₂.weights i

@[simp]
theorem weightedSelectionUnionWeights_eq_left_of_mem
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    {i : Occurrence xs} (hi : i ∈ h₁.selected) :
    weightedSelectionUnionWeights h₁ h₂ i = h₁.weights i := by
  simp [weightedSelectionUnionWeights, hi]

@[simp]
theorem weightedSelectionUnionWeights_eq_right_of_mem
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected)
    {i : Occurrence xs} (hi : i ∈ h₂.selected) :
    weightedSelectionUnionWeights h₁ h₂ i = h₂.weights i := by
  have hnot : i ∉ h₁.selected := by
    intro hi₁
    exact (Finset.disjoint_left.mp hdis) hi₁ hi
  simp [weightedSelectionUnionWeights, hnot]

/-- Occurrence-labelled convolution of two disjoint general weighted
selections.  No finiteness assumption on the weight set is used. -/
def HasWeightedSumOfCard.disjointUnion
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected) :
    HasWeightedSumOfCard W xs (n₁ + n₂) (y₁ + y₂) := by
  classical
  refine {
    selected := h₁.selected ∪ h₂.selected
    weights := weightedSelectionUnionWeights h₁ h₂
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro i hi
    rcases Finset.mem_union.mp hi with hi₁ | hi₂
    · rw [weightedSelectionUnionWeights_eq_left_of_mem h₁ h₂ hi₁]
      exact h₁.weights_mem i hi₁
    · rw [weightedSelectionUnionWeights_eq_right_of_mem h₁ h₂ hdis hi₂]
      exact h₂.weights_mem i hi₂
  · rw [Finset.card_union_of_disjoint hdis,
      h₁.card_selected, h₂.card_selected]
  · rw [Finset.sum_union hdis]
    have hleft :
        (∑ i ∈ h₁.selected,
            weightedSelectionUnionWeights h₁ h₂ i • occurrenceValue xs i) =
          ∑ i ∈ h₁.selected, h₁.weights i • occurrenceValue xs i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [weightedSelectionUnionWeights_eq_left_of_mem h₁ h₂ hi]
    have hright :
        (∑ i ∈ h₂.selected,
            weightedSelectionUnionWeights h₁ h₂ i • occurrenceValue xs i) =
          ∑ i ∈ h₂.selected, h₂.weights i • occurrenceValue xs i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [weightedSelectionUnionWeights_eq_right_of_mem h₁ h₂ hdis hi]
    rw [hleft, hright, h₁.weighted_sum, h₂.weighted_sum]

@[simp]
theorem HasWeightedSumOfCard.selected_disjointUnion
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected) :
    (h₁.disjointUnion h₂ hdis).selected = h₁.selected ∪ h₂.selected :=
  rfl

@[simp]
theorem HasWeightedSumOfCard.weights_disjointUnion_eq_left
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected)
    {i : Occurrence xs} (hi : i ∈ h₁.selected) :
    (h₁.disjointUnion h₂ hdis).weights i = h₁.weights i := by
  exact weightedSelectionUnionWeights_eq_left_of_mem h₁ h₂ hi

@[simp]
theorem HasWeightedSumOfCard.weights_disjointUnion_eq_right
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected)
    {i : Occurrence xs} (hi : i ∈ h₂.selected) :
    (h₁.disjointUnion h₂ hdis).weights i = h₂.weights i := by
  exact weightedSelectionUnionWeights_eq_right_of_mem h₁ h₂ hdis hi

theorem HasWeightedSumOfCard.weights_mem_disjointUnion
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected)
    {i : Occurrence xs} (hi : i ∈ (h₁.disjointUnion h₂ hdis).selected) :
    (h₁.disjointUnion h₂ hdis).weights i ∈ W :=
  (h₁.disjointUnion h₂ hdis).weights_mem i hi

@[simp]
theorem HasWeightedSumOfCard.card_selected_disjointUnion
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected) :
    (h₁.disjointUnion h₂ hdis).selected.card = n₁ + n₂ :=
  (h₁.disjointUnion h₂ hdis).card_selected

theorem HasWeightedSumOfCard.weighted_sum_disjointUnion
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (hdis : Disjoint h₁.selected h₂.selected) :
    (∑ i ∈ (h₁.disjointUnion h₂ hdis).selected,
      (h₁.disjointUnion h₂ hdis).weights i • occurrenceValue xs i) =
        y₁ + y₂ :=
  (h₁.disjointUnion h₂ hdis).weighted_sum

/-! ## Pool-preserving Step 1 interface -/

/-- Explicit output package for a convolution whose right selection was
drawn from a reserve pool.  It retains the literal union identity, both
weight restrictions, and the useful subset facts for later Step 1 assembly.
-/
structure WeightedSelectionPoolConvolutionOutput
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (reserve pool : Selection xs) where
  combined : HasWeightedSumOfCard W xs (n₁ + n₂) (y₁ + y₂)
  selected_eq_union : combined.selected = h₁.selected ∪ h₂.selected
  core_added_disjoint : Disjoint h₁.selected h₂.selected
  selected_subset_core_union_reserve :
    combined.selected ⊆ h₁.selected ∪ reserve
  selected_subset_core_union_pool : combined.selected ⊆ h₁.selected ∪ pool
  core_subset_selected : h₁.selected ⊆ combined.selected
  added_subset_selected : h₂.selected ⊆ combined.selected
  weights_eq_core : ∀ i ∈ h₁.selected, combined.weights i = h₁.weights i
  weights_eq_added : ∀ i ∈ h₂.selected, combined.weights i = h₂.weights i

/-- Step 1-facing constructor.  The right selection lies in `reserve`, the
reserve lies in `pool`, and the entire reserve is disjoint from the left
core.  Consequently the exact combined witness is supported in
`core ∪ pool`, with its selected set definitionally identified as the union.
-/
def HasWeightedSumOfCard.disjointUnionOfReserve
    {W : Set ℤ} {xs : List A} {n₁ n₂ : ℕ} {y₁ y₂ : A}
    (h₁ : HasWeightedSumOfCard W xs n₁ y₁)
    (h₂ : HasWeightedSumOfCard W xs n₂ y₂)
    (reserve pool : Selection xs)
    (h₂reserve : h₂.selected ⊆ reserve)
    (hreservePool : reserve ⊆ pool)
    (hcoreReserve : Disjoint h₁.selected reserve) :
    WeightedSelectionPoolConvolutionOutput h₁ h₂ reserve pool := by
  have hdis : Disjoint h₁.selected h₂.selected :=
    hcoreReserve.mono_right h₂reserve
  let combined := h₁.disjointUnion h₂ hdis
  refine {
    combined := combined
    selected_eq_union := rfl
    core_added_disjoint := hdis
    selected_subset_core_union_reserve := ?_
    selected_subset_core_union_pool := ?_
    core_subset_selected := ?_
    added_subset_selected := ?_
    weights_eq_core := ?_
    weights_eq_added := ?_
  }
  · rw [show combined.selected = h₁.selected ∪ h₂.selected by rfl]
    intro i hi
    rcases Finset.mem_union.mp hi with hiCore | hiAdded
    · exact Finset.mem_union_left reserve hiCore
    · exact Finset.mem_union_right h₁.selected
        (h₂reserve hiAdded)
  · rw [show combined.selected = h₁.selected ∪ h₂.selected by rfl]
    intro i hi
    rcases Finset.mem_union.mp hi with hiCore | hiAdded
    · exact Finset.mem_union_left pool hiCore
    · exact Finset.mem_union_right h₁.selected
        ((h₂reserve.trans hreservePool) hiAdded)
  · rw [show combined.selected = h₁.selected ∪ h₂.selected by rfl]
    exact Finset.subset_union_left
  · rw [show combined.selected = h₁.selected ∪ h₂.selected by rfl]
    exact Finset.subset_union_right
  · intro i hi
    exact h₁.weights_disjointUnion_eq_left h₂ hdis hi
  · intro i hi
    exact h₁.weights_disjointUnion_eq_right h₂ hdis hi

end GaoLean

#print axioms GaoLean.weightedSelectionUnionWeights_eq_left_of_mem
#print axioms GaoLean.weightedSelectionUnionWeights_eq_right_of_mem
#print axioms GaoLean.HasWeightedSumOfCard.disjointUnion
#print axioms GaoLean.HasWeightedSumOfCard.selected_disjointUnion
#print axioms GaoLean.HasWeightedSumOfCard.weights_disjointUnion_eq_left
#print axioms GaoLean.HasWeightedSumOfCard.weights_disjointUnion_eq_right
#print axioms GaoLean.HasWeightedSumOfCard.weights_mem_disjointUnion
#print axioms GaoLean.HasWeightedSumOfCard.card_selected_disjointUnion
#print axioms GaoLean.HasWeightedSumOfCard.weighted_sum_disjointUnion
#print axioms GaoLean.HasWeightedSumOfCard.disjointUnionOfReserve
