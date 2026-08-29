import GaoLean.PGGeneralWeightedCappedIncidence
import GaoLean.PGGeneralWeightedGcdTorsion

/-!
# Occurrence-faithful singleton weighted layers

The objects in this file retain labelled source positions.  Equal source
values at different positions are therefore counted separately.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

@[simp]
theorem map_attach_subtype_val {α : Type*} (l : List α) :
    l.attach.map (fun x => x.1) = l := by
  simp

/-- Literal source occurrences whose weighted value block has cardinality
one. -/
noncomputable def weightedSingletonOccurrences
    (W : Set ℤ) (xs : List A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i =>
    (weightedValueBlock W (occurrenceValue xs i)).card = 1

@[simp]
theorem mem_weightedSingletonOccurrences_iff
    (W : Set ℤ) (xs : List A) (i : Occurrence xs) :
    i ∈ weightedSingletonOccurrences W xs ↔
      (weightedValueBlock W (occurrenceValue xs i)).card = 1 := by
  classical
  simp [weightedSingletonOccurrences]

/-- Adding a source head changes the singleton-layer occurrence count by
one exactly when the head block is a singleton. -/
theorem card_weightedSingletonOccurrences_cons
    (W : Set ℤ) (x : A) (xs : List A) :
    (weightedSingletonOccurrences W (x :: xs)).card =
      (if (weightedValueBlock W x).card = 1 then 1 else 0) +
        (weightedSingletonOccurrences W xs).card := by
  classical
  let p : Fin (xs.length + 1) → Prop := fun i =>
    (weightedValueBlock W (occurrenceValue (x :: xs) i)).card = 1
  have hwhole : weightedSingletonOccurrences W (x :: xs) =
      Finset.univ.filter p := by
    ext i
    simp [weightedSingletonOccurrences, p]
  have htail : (Finset.univ.filter fun i : Fin xs.length => p i.succ) =
      weightedSingletonOccurrences W xs := by
    ext i
    simp [weightedSingletonOccurrences, p, occurrenceValue]
  rw [hwhole, Fin.card_filter_univ_succ', htail]
  by_cases hx : (weightedValueBlock W x).card = 1 <;>
    simp [occurrenceValue, hx]

/-- The selected finset cardinality is exactly the existing literal
singleton-layer count.  No support deduplication occurs. -/
theorem card_weightedSingletonOccurrences_eq_count
    (W : Set ℤ) (xs : List A) :
    (weightedSingletonOccurrences W xs).card =
      weightedSingletonOccurrenceCount W xs := by
  classical
  induction xs with
  | nil =>
      have hempty : weightedSingletonOccurrences W ([] : List A) = ∅ := by
        ext i
        exact Fin.elim0 i
      simp [hempty, weightedSingletonOccurrenceCount,
        weightedOccurrenceSetpartition]
  | cons x xs ih =>
      rw [card_weightedSingletonOccurrences_cons, ih]
      simp [weightedSingletonOccurrenceCount,
        weightedOccurrenceSetpartition]

/-- After choosing a base weight, a labelled occurrence is selected exactly
when its source value lies in the canonical difference kernel. -/
theorem mem_weightedSingletonOccurrences_iff_mem_weightedDifferenceKernel
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) (i : Occurrence xs) :
    i ∈ weightedSingletonOccurrences W xs ↔
      occurrenceValue xs i ∈ weightedDifferenceKernel W w₀ A := by
  rw [mem_weightedSingletonOccurrences_iff]
  exact (mem_weightedDifferenceKernel_iff_weightedValueBlock_card_eq_one
    hW hw₀ (occurrenceValue xs i)).symm

/-- The singleton-layer occurrences, now valued in the difference-kernel
subtype.  The list order is the canonical increasing source-index order of
the selected finset. -/
noncomputable def weightedSingletonKernelSubsequence
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) : List (weightedDifferenceKernel W w₀ A) := by
  classical
  let R := weightedSingletonOccurrences W xs
  let ys := occurrenceSubsequence xs R
  exact ys.attach.map fun y =>
    ⟨y.1, by
      rcases List.mem_map.mp y.2 with ⟨i, hi, hiy⟩
      rw [← hiy]
      apply (mem_weightedDifferenceKernel_iff_weightedValueBlock_card_eq_one
        hW hw₀ (occurrenceValue xs i)).2
      exact (mem_weightedSingletonOccurrences_iff W xs i).1
        (Finset.mem_toList.mp hi)⟩

@[simp]
theorem length_weightedSingletonKernelSubsequence
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) :
    (weightedSingletonKernelSubsequence hW hw₀ xs).length =
      weightedSingletonOccurrenceCount W xs := by
  classical
  simp only [weightedSingletonKernelSubsequence, List.length_map,
    List.length_attach, occurrenceSubsequence, Finset.length_toList]
  exact card_weightedSingletonOccurrences_eq_count W xs

/-- Forgetting the kernel proof recovers exactly the occurrence subsequence
of selected source positions. -/
theorem map_coe_weightedSingletonKernelSubsequence
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) :
    (weightedSingletonKernelSubsequence hW hw₀ xs).map
        (fun x : weightedDifferenceKernel W w₀ A => (x : A)) =
      occurrenceSubsequence xs (weightedSingletonOccurrences W xs) := by
  classical
  dsimp only [weightedSingletonKernelSubsequence]
  rw [List.map_map]
  calc
    List.map
        ((fun x : weightedDifferenceKernel W w₀ A => (x : A)) ∘
          fun y => ⟨y.1, by
            rcases List.mem_map.mp y.2 with ⟨i, hi, hiy⟩
            rw [← hiy]
            apply
              (mem_weightedDifferenceKernel_iff_weightedValueBlock_card_eq_one
                hW hw₀ (occurrenceValue xs i)).2
            exact (mem_weightedSingletonOccurrences_iff W xs i).1
              (Finset.mem_toList.mp hi)⟩)
        (occurrenceSubsequence xs
          (weightedSingletonOccurrences W xs)).attach =
        List.map (fun y => y.1)
          (occurrenceSubsequence xs
            (weightedSingletonOccurrences W xs)).attach := by
      apply List.map_congr_left
      intro y hy
      rfl
    _ = occurrenceSubsequence xs (weightedSingletonOccurrences W xs) :=
      map_attach_subtype_val _

/-- Send an occurrence of the kernel-valued singleton list back to its exact
source occurrence. -/
noncomputable def weightedSingletonKernelOccurrenceSource
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) :
    Occurrence (weightedSingletonKernelSubsequence hW hw₀ xs) →
      Occurrence xs := fun i =>
  (weightedSingletonOccurrences W xs).toList.get
    ⟨i.1, by
      simpa [weightedSingletonKernelSubsequence, occurrenceSubsequence] using i.2⟩

theorem weightedSingletonKernelOccurrenceSource_injective
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) :
    Function.Injective
      (weightedSingletonKernelOccurrenceSource hW hw₀ xs) := by
  intro i j hij
  apply Fin.ext
  have hget :
      (weightedSingletonOccurrences W xs).toList.get
          ⟨i.1, by
            simpa [weightedSingletonKernelSubsequence,
              occurrenceSubsequence] using i.2⟩ =
        (weightedSingletonOccurrences W xs).toList.get
          ⟨j.1, by
            simpa [weightedSingletonKernelSubsequence,
              occurrenceSubsequence] using j.2⟩ := hij
  have hidx := (weightedSingletonOccurrences W xs).nodup_toList.injective_get hget
  exact congrArg (fun k : Fin (weightedSingletonOccurrences W xs).toList.length => k.1) hidx

/-- The occurrence embedding preserves the underlying source value. -/
theorem weightedSingletonKernelOccurrenceSource_value
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A)
    (i : Occurrence (weightedSingletonKernelSubsequence hW hw₀ xs)) :
    ((occurrenceValue (weightedSingletonKernelSubsequence hW hw₀ xs) i :
        weightedDifferenceKernel W w₀ A) : A) =
      occurrenceValue xs
        (weightedSingletonKernelOccurrenceSource hW hw₀ xs i) := by
  classical
  let R := weightedSingletonOccurrences W xs
  let j : Occurrence (occurrenceSubsequence xs R) :=
    ⟨i.1, by
      simpa [weightedSingletonKernelSubsequence, R] using i.2⟩
  have hvalue := occurrenceValue_occurrenceSubsequence xs R j
  simpa [weightedSingletonKernelSubsequence,
    weightedSingletonKernelOccurrenceSource, occurrenceValue,
    occurrenceSubsequence, R, j, List.get_eq_getElem] using hvalue

end GaoLean

#print axioms GaoLean.mem_weightedSingletonOccurrences_iff
#print axioms GaoLean.card_weightedSingletonOccurrences_eq_count
#print axioms GaoLean.mem_weightedSingletonOccurrences_iff_mem_weightedDifferenceKernel
#print axioms GaoLean.length_weightedSingletonKernelSubsequence
#print axioms GaoLean.map_coe_weightedSingletonKernelSubsequence
#print axioms GaoLean.weightedSingletonKernelOccurrenceSource_injective
#print axioms GaoLean.weightedSingletonKernelOccurrenceSource_value
