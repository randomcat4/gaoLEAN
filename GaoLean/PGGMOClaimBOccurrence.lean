import GaoLean.PGGMOClaimBCore
import GaoLean.PGGMOPGroupInvariant

/-!
# Occurrence-faithful substrate for ordinary GMO Claim B

This module records the labelled-occurrence objects used in Section 5 of
Grynkiewicz--Marchan--Ordaz.  In particular, `x = |S| - |S'|` is counted in
the complement of the *actual replacement-partition support*.  None of the
statements below replaces occurrence counts by cardinalities of value sets.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-! `insideCoreCell`, `coreValueCell`, their exact elementwise occurrence
correspondence, and the equality of their cardinalities are imported from
`PGGMOClaimBCore`.  Keeping that layer shared prevents duplicate classical
finset implementations from becoming definitionally inconsistent. -/

/-- One labelled occurrence retained from every original cell, with all
chosen values in one fixed additive coset.  The choice remains tied to its
source cell and hence cannot identify repeated values in different cells. -/
structure Theorem21SetPartition.CellCosetOccurrenceChoice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) where
  occurrence : Fin n → Occurrence xs
  mem_cell : ∀ c, occurrence c ∈ P.cells c
  value_mem_coset : ∀ c,
    occurrenceValue xs (occurrence c) ∈ addCosetFinset H g

/-- Construct the cellwise labelled choice from the literal per-cell
existence hypotheses. -/
noncomputable def Theorem21SetPartition.cellCosetOccurrenceChoice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A)
    (h : ∀ c : Fin n, ∃ i : Occurrence xs,
      i ∈ P.cells c ∧ occurrenceValue xs i ∈ addCosetFinset H g) :
    P.CellCosetOccurrenceChoice H g where
  occurrence c := Classical.choose (h c)
  mem_cell c := (Classical.choose_spec (h c)).1
  value_mem_coset c := (Classical.choose_spec (h c)).2

/-- The choice interface is equivalent to retaining a genuine labelled
occurrence in the required coset from every original layer. -/
theorem Theorem21SetPartition.nonempty_cellCosetOccurrenceChoice_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) :
    Nonempty (P.CellCosetOccurrenceChoice H g) ↔
      ∀ c : Fin n, ∃ i : Occurrence xs,
        i ∈ P.cells c ∧ occurrenceValue xs i ∈ addCosetFinset H g := by
  constructor
  · rintro ⟨choice⟩ c
    exact ⟨choice.occurrence c, choice.mem_cell c,
      choice.value_mem_coset c⟩
  · intro h
    exact ⟨P.cellCosetOccurrenceChoice H g h⟩

/-- Membership of `g` in the common thickened core produces, in every
original cell, a genuine labelled occurrence whose value lies in `g+H`.
This is the occurrence-level passage used when Section 5 chooses one term
from each `Aᵢ` above the common quotient class. -/
theorem Theorem21SetPartition.exists_cellOccurrence_mem_addCoset_of_mem_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H)
    (c : Fin n) :
    ∃ i : Occurrence xs,
      i ∈ P.cells c ∧ occurrenceValue xs i ∈ addCosetFinset H g := by
  classical
  have hthick := (P.mem_commonCore_iff H g).1 hg c
  unfold Theorem21SetPartition.thickenedCell at hthick
  obtain ⟨a, ha, h, hh, rfl⟩ := Finset.mem_add.mp hthick
  unfold Theorem21SetPartition.valueCell at ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  refine ⟨i, hi, ?_⟩
  apply (mem_addCosetFinset_iff H
    (occurrenceValue xs i + h) (occurrenceValue xs i)).2
  have hhH : h ∈ H := (mem_subgroupFinset H h).1 hh
  have hneg := H.neg_mem hhH
  convert hneg using 1 <;> abel

/-- Canonical cell-indexed labelled representatives supplied by one common
core element. -/
noncomputable def Theorem21SetPartition.cellCosetOccurrenceChoice_of_mem_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H) :
    P.CellCosetOccurrenceChoice H g :=
  P.cellCosetOccurrenceChoice H g fun c ↦
    P.exists_cellOccurrence_mem_addCoset_of_mem_commonCore H g hg c

omit [Fintype A] in
/-- The replacement support and its literal unused-occurrence complement
partition the whole source occurrence set. -/
theorem Theorem21SetPartition.support_union_unused
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.support ∪ ((Finset.univ : Selection xs) \ P.support) = Finset.univ := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.subset_univ P.support)

omit [Fintype A] in
/-- The two parts in `support_union_unused` are occurrence-disjoint. -/
theorem Theorem21SetPartition.support_disjoint_unused
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    Disjoint P.support
      ((Finset.univ : Selection xs) \ P.support) := by
  classical
  exact Finset.disjoint_sdiff

omit [Fintype A] in
/-- Exact number of labelled source occurrences outside an `m`-occurrence
replacement partition. -/
theorem Theorem21SetPartition.card_unused
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    ((Finset.univ : Selection xs) \ P.support).card = xs.length - m := by
  classical
  rw [Finset.card_sdiff]
  simp [P.card_support_eq]

/-- Unused labelled occurrences whose values lie in the fixed coset
`g + H`. -/
noncomputable def Theorem21SetPartition.unusedInAddCoset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) : Selection xs := by
  classical
  exact ((Finset.univ : Selection xs) \ P.support).filter fun i ↦
    occurrenceValue xs i ∈ addCosetFinset H g

@[simp]
theorem Theorem21SetPartition.mem_unusedInAddCoset_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (i : Occurrence xs) :
    i ∈ P.unusedInAddCoset H g ↔
      i ∉ P.support ∧ occurrenceValue xs i ∈ addCosetFinset H g := by
  classical
  simp [Theorem21SetPartition.unusedInAddCoset]

/-- If every unused source occurrence lies in the coset, filtering by that
coset loses no occurrence. -/
theorem Theorem21SetPartition.unusedInAddCoset_eq_unused
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A)
    (hall : ∀ i : Occurrence xs, i ∉ P.support →
      occurrenceValue xs i ∈ addCosetFinset H g) :
    P.unusedInAddCoset H g =
      (Finset.univ : Selection xs) \ P.support := by
  classical
  unfold Theorem21SetPartition.unusedInAddCoset
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact hall i (Finset.mem_sdiff.mp hi).2

/-- Source-faithful form of `x = |S| - |S'|`: when the replacement support
has the seed cardinality and all unused terms lie in `g+H`, the exact number
of unused occurrences in that coset is `xs.length - seed.card`. -/
theorem Theorem21SetPartition.card_unusedInAddCoset_eq_length_sub_seed
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P : Theorem21SetPartition xs n seed.card)
    (H : AddSubgroup A) (g : A)
    (hall : ∀ i : Occurrence xs, i ∉ P.support →
      occurrenceValue xs i ∈ addCosetFinset H g) :
    (P.unusedInAddCoset H g).card = xs.length - seed.card := by
  rw [P.unusedInAddCoset_eq_unused H g hall, P.card_unused]

/-- The exact Claim-B payload retained by the odd-prime ordinary GMO
induction.  `partition.support` is the genuine labelled subsequence `T`;
`support_in_coset` constrains every occurrence of `T`; `saturation` is the
source equation for the first `d*(K)` cells; and `remaining_in_coset` counts
the labelled occurrences of `T⁻¹S` in the same coset. -/
structure OrdinaryGMOClaimBOutput
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  K : AddSubgroup A
  nontrivial : K ≠ ⊥
  g : A
  supportCard : ℕ
  partition : Theorem21SetPartition xs (pGroupDStar K) supportCard
  support_in_coset : ∀ i : Occurrence xs, i ∈ partition.support →
    occurrenceValue xs i ∈ addCosetFinset K g
  saturation :
    partition.sumset = addCosetFinset K ((pGroupDStar K) • g)
  remaining_in_coset :
    n - pGroupDStar K + (xs.length - seed.card) ≤
      (partition.unusedInAddCoset K g).card

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.mem_coreValueCell_iff_exists_insideCoreCell
#print axioms GaoLean.Theorem21SetPartition.card_unused
#print axioms GaoLean.Theorem21SetPartition.card_unusedInAddCoset_eq_length_sub_seed
