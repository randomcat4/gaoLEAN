import GaoLean.PGGeneralWeightedDefinitions
import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic consequences of a primitive integer weight set

The arguments in this file are deliberately stated for an arbitrary
`Set ℤ`.  In particular, primitivity is used through additive-subgroup closure
induction rather than by extracting a finite list of weights.

There are three consequences needed by the general-weight GMO interface:

* if every weighted multiple `w • x` lies in a subgroup and `W` is primitive,
  then `x` itself lies in that subgroup;
* a common weighted coset for two source values forces the source values to
  lie in a common (unweighted) coset;
* consequently the `weightCoset` field of a concentration witness determines
  one source coset on every nonempty selected family.

The last section records the correct singleton locus of a general weighted
value block.  It is not in general the zero locus: on `ZMod 5`, the weights
`2` and `7` act identically, so every weighted value block is a singleton.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A]

/-! ## Primitive weights recover the unweighted source -/

/-- If the integer weights generate `ℤ` and all weighted multiples of `x`
belong to `K`, then `x` belongs to `K`.  Closure induction makes this valid
for an arbitrary, possibly infinite, set of weights. -/
theorem mem_addSubgroup_of_primitive_weights
    {W : Set ℤ} {K : AddSubgroup A} {x : A}
    (hprimitive : IsPrimitiveWeightSet W)
    (hweighted : ∀ w ∈ W, w • x ∈ K) :
    x ∈ K := by
  have hone : (1 : ℤ) ∈ AddSubgroup.closure W := by
    rw [hprimitive]
    exact AddSubgroup.mem_top 1
  have hall : ∀ z : ℤ, z ∈ AddSubgroup.closure W → z • x ∈ K := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem w hw => exact hweighted w hw
    | zero => simpa using K.zero_mem
    | add a b _ha _hb ha hb =>
        simpa [add_zsmul] using K.add_mem ha hb
    | neg a _ha ha =>
        simpa using K.neg_mem ha
  simpa using hall 1 hone

/-- If all `W`-multiples of `x` and `y` belong to the same affine `K`-coset,
then primitive weights force the unweighted difference `x - y` into `K`. -/
theorem sub_mem_addSubgroup_of_common_weightCoset
    {W : Set ℤ} {K : AddSubgroup A} {x y beta : A}
    (hprimitive : IsPrimitiveWeightSet W)
    (hx : ∀ w ∈ W, w • x - beta ∈ K)
    (hy : ∀ w ∈ W, w • y - beta ∈ K) :
    x - y ∈ K := by
  apply mem_addSubgroup_of_primitive_weights hprimitive
  intro w hw
  have hsub := K.sub_mem (hx w hw) (hy w hw)
  simpa [smul_sub] using hsub

/-! ## Consequences for a weighted GMO concentration witness -/

section FiniteAmbient

variable [Fintype A]

/-- The weighted-coset field alone forces any two selected source
occurrences into one unweighted `K`-coset. -/
theorem WeightedGMOConcentration.selected_sources_sub_mem
    {W : Set ℤ} {xs : List A}
    (C : WeightedGMOConcentration W xs)
    (hprimitive : IsPrimitiveWeightSet W)
    {i j : Occurrence xs} (hi : i ∈ C.selected) (hj : j ∈ C.selected) :
    occurrenceValue xs i - occurrenceValue xs j ∈ C.K := by
  exact sub_mem_addSubgroup_of_common_weightCoset hprimitive
    (C.weightCoset i hi) (C.weightCoset j hj)

/-- If the selected family is nonempty, one selected source occurrence can
be chosen as a center for the source coset, using only `weightCoset` and
primitivity. -/
theorem WeightedGMOConcentration.exists_selected_source_center
    {W : Set ℤ} {xs : List A}
    (C : WeightedGMOConcentration W xs)
    (hprimitive : IsPrimitiveWeightSet W)
    (hselected : C.selected.Nonempty) :
    ∃ i ∈ C.selected, ∀ j ∈ C.selected,
      occurrenceValue xs j - occurrenceValue xs i ∈ C.K := by
  obtain ⟨i, hi⟩ := hselected
  exact ⟨i, hi, fun j hj ↦ C.selected_sources_sub_mem hprimitive hj hi⟩

/-- A selected occurrence chosen as the source-coset center is compatible
with the `alpha` already stored in the concentration witness. -/
theorem WeightedGMOConcentration.selected_source_sub_alpha_mem
    {W : Set ℤ} {xs : List A}
    (C : WeightedGMOConcentration W xs)
    {i : Occurrence xs} (hi : i ∈ C.selected) :
    occurrenceValue xs i - C.alpha ∈ C.K :=
  C.sourceCoset i hi

/-- More generally, any center that contains all selected source values is
congruent modulo `K` to the stored center, provided a selected value exists.
-/
theorem WeightedGMOConcentration.source_center_sub_alpha_mem
    {W : Set ℤ} {xs : List A}
    (C : WeightedGMOConcentration W xs)
    (hselected : C.selected.Nonempty)
    {a : A}
    (ha : ∀ i ∈ C.selected, occurrenceValue xs i - a ∈ C.K) :
    a - C.alpha ∈ C.K := by
  obtain ⟨i, hi⟩ := hselected
  have hsub := C.K.sub_mem (C.sourceCoset i hi) (ha i hi)
  rw [show a - C.alpha =
    (occurrenceValue xs i - C.alpha) - (occurrenceValue xs i - a) by abel]
  exact hsub

/-- The source center constructed purely from `weightCoset` can be chosen
to be compatible with the witness's existing `alpha`. -/
theorem WeightedGMOConcentration.exists_compatible_selected_source_center
    {W : Set ℤ} {xs : List A}
    (C : WeightedGMOConcentration W xs)
    (hprimitive : IsPrimitiveWeightSet W)
    (hselected : C.selected.Nonempty) :
    ∃ a : A,
      (∀ j ∈ C.selected, occurrenceValue xs j - a ∈ C.K) ∧
      a - C.alpha ∈ C.K := by
  obtain ⟨i, hi⟩ := hselected
  refine ⟨occurrenceValue xs i, ?_, C.sourceCoset i hi⟩
  intro j hj
  exact C.selected_sources_sub_mem hprimitive hj hi

/-! ## The correct singleton locus for a general weight set -/

/-- The source values whose `W`-weighted value block is forced to one value:
all pairwise weight differences annihilate the source. -/
def weightedSingletonLocus (W : Set ℤ) : Set A :=
  {x | ∀ w₁ ∈ W, ∀ w₂ ∈ W, (w₁ - w₂) • x = 0}

@[simp]
theorem mem_weightedSingletonLocus_iff
    (W : Set ℤ) (x : A) :
    x ∈ weightedSingletonLocus W ↔
      ∀ w₁ ∈ W, ∀ w₂ ∈ W, (w₁ - w₂) • x = 0 :=
  Iff.rfl

/-- With a distinguished weight `w₀`, membership in the singleton locus is
equivalent to every weight acting on `x` exactly as `w₀` does. -/
theorem mem_weightedSingletonLocus_iff_smul_eq
    {W : Set ℤ} {w₀ : ℤ} (hw₀ : w₀ ∈ W) (x : A) :
    x ∈ weightedSingletonLocus W ↔
      ∀ w ∈ W, w • x = w₀ • x := by
  constructor
  · intro hx w hw
    have hdiff := hx w hw w₀ hw₀
    rw [sub_zsmul] at hdiff
    apply sub_eq_zero.mp
    simpa only [sub_eq_add_neg] using hdiff
  · intro hx w₁ hw₁ w₂ hw₂
    rw [sub_zsmul, hx w₁ hw₁, hx w₂ hw₂]
    exact add_neg_cancel _

/-- A general weighted value block is the singleton centered at `w₀ • x`
exactly on the weighted singleton locus. -/
theorem weightedValueBlock_eq_singleton_iff
    {W : Set ℤ} {w₀ : ℤ} (hw₀ : w₀ ∈ W) (x : A) :
    weightedValueBlock W x = {w₀ • x} ↔
      x ∈ weightedSingletonLocus W := by
  rw [mem_weightedSingletonLocus_iff_smul_eq hw₀]
  constructor
  · intro hblock w hw
    have hmem : w • x ∈ weightedValueBlock W x :=
      (mem_weightedValueBlock_iff W x (w • x)).2 ⟨w, hw, rfl⟩
    rw [hblock] at hmem
    exact Finset.mem_singleton.mp hmem
  · intro hall
    ext y
    rw [mem_weightedValueBlock_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hall w hw
    · rintro rfl
      exact ⟨w₀, hw₀, rfl⟩

/-- Cardinality-one form of the singleton-locus characterization. -/
theorem weightedValueBlock_card_eq_one_iff
    {W : Set ℤ} (hW : W.Nonempty) (x : A) :
    (weightedValueBlock W x).card = 1 ↔
      x ∈ weightedSingletonLocus W := by
  obtain ⟨w₀, hw₀⟩ := hW
  rw [← weightedValueBlock_eq_singleton_iff hw₀]
  constructor
  · intro hcard
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hwmem : w₀ • x ∈ weightedValueBlock W x :=
      (mem_weightedValueBlock_iff W x (w₀ • x)).2 ⟨w₀, hw₀, rfl⟩
    have hwa : w₀ • x = a := by
      rw [ha] at hwmem
      exact Finset.mem_singleton.mp hwmem
    rw [hwa]
    exact ha
  · intro hblock
    rw [hblock]
    simp

/-! ## Regression: singleton does not imply zero for arbitrary weights -/

/-- The regression weight set is itself primitive: `7 - 3 * 2 = 1`, so the
two weights generate all of `ℤ`.  This makes the example relevant even under
the manuscript's `gcd(W) = 1` structural hypothesis. -/
theorem two_seven_isPrimitiveWeightSet :
    IsPrimitiveWeightSet ({2, 7} : Set ℤ) := by
  let K : AddSubgroup ℤ := AddSubgroup.closure ({2, 7} : Set ℤ)
  have h2 : (2 : ℤ) ∈ K :=
    AddSubgroup.subset_closure (by simp)
  have h7 : (7 : ℤ) ∈ K :=
    AddSubgroup.subset_closure (by simp)
  have h6 : (6 : ℤ) ∈ K := by
    simpa using K.zsmul_mem h2 (3 : ℤ)
  have h1 : (1 : ℤ) ∈ K := by
    simpa using K.sub_mem h7 h6
  change K = ⊤
  apply top_unique
  intro z _hz
  simpa using K.zsmul_mem h1 z

/-- On `ZMod 5`, weights `2` and `7` have the same action.  Thus the weighted
block at the nonzero source `1` is the singleton `{2}`. -/
theorem zmod5_two_seven_weightedValueBlock_one :
    weightedValueBlock ({2, 7} : Set ℤ) (1 : ZMod 5) = {2} := by
  ext y
  rw [mem_weightedValueBlock_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with (rfl | rfl)
    · simp only [zsmul_one]
      decide
    · simp only [zsmul_one]
      decide
  · rintro rfl
    exact ⟨2, by simp, by norm_num⟩

/-- The preceding singleton block occurs at a genuinely nonzero source. -/
theorem zmod5_one_ne_zero : (1 : ZMod 5) ≠ 0 := by
  decide

end FiniteAmbient

end GaoLean

#print axioms GaoLean.mem_addSubgroup_of_primitive_weights
#print axioms GaoLean.sub_mem_addSubgroup_of_common_weightCoset
#print axioms GaoLean.WeightedGMOConcentration.selected_sources_sub_mem
#print axioms GaoLean.WeightedGMOConcentration.exists_selected_source_center
#print axioms GaoLean.WeightedGMOConcentration.source_center_sub_alpha_mem
#print axioms GaoLean.WeightedGMOConcentration.exists_compatible_selected_source_center
#print axioms GaoLean.weightedValueBlock_eq_singleton_iff
#print axioms GaoLean.weightedValueBlock_card_eq_one_iff
#print axioms GaoLean.two_seven_isPrimitiveWeightSet
#print axioms GaoLean.zmod5_two_seven_weightedValueBlock_one
#print axioms GaoLean.zmod5_one_ne_zero
