import GaoLean.PGGMOOrdinarySeed

/-!
# Canonical capped and excess occurrence ledger

This module records exactly which labelled occurrences are omitted by the
canonical capped selection.  Everything here is source-level bookkeeping:
no Claim-B, concentration, or target-spectrum conclusion is asserted.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The labelled occurrences of value `a` left after taking its canonical
first `min r multiplicity` occurrences. -/
noncomputable def excessOccurrenceFiber
    (xs : List A) (a : A) (r : ℕ) : Selection xs := by
  classical
  exact occurrenceFiber xs a \ cappedOccurrenceFiber xs a r

/-- All labelled occurrences omitted by the canonical capped selection. -/
noncomputable def cappedOmittedOccurrenceSelection
    (xs : List A) (r : ℕ) : Selection xs := by
  classical
  exact (Finset.univ : Selection xs) \ cappedOccurrenceSelection xs r

theorem excessOccurrenceFiber_subset_occurrenceFiber
    (xs : List A) (a : A) (r : ℕ) :
    excessOccurrenceFiber xs a r ⊆ occurrenceFiber xs a := by
  classical
  exact Finset.sdiff_subset

@[simp]
theorem card_excessOccurrenceFiber
    (xs : List A) (a : A) (r : ℕ) :
    (excessOccurrenceFiber xs a r).card =
      (occurrenceFiber xs a).card - r := by
  classical
  rw [excessOccurrenceFiber,
    Finset.card_sdiff_of_subset
      (cappedOccurrenceFiber_subset_occurrenceFiber xs a r),
    card_cappedOccurrenceFiber]
  omega

theorem cappedOccurrenceFiber_union_excessOccurrenceFiber
    (xs : List A) (a : A) (r : ℕ) :
    cappedOccurrenceFiber xs a r ∪ excessOccurrenceFiber xs a r =
      occurrenceFiber xs a := by
  classical
  exact Finset.union_sdiff_of_subset
    (cappedOccurrenceFiber_subset_occurrenceFiber xs a r)

theorem cappedOccurrenceFiber_disjoint_excessOccurrenceFiber
    (xs : List A) (a : A) (r : ℕ) :
    Disjoint (cappedOccurrenceFiber xs a r)
      (excessOccurrenceFiber xs a r) := by
  classical
  exact Finset.disjoint_sdiff

theorem excessOccurrenceFiber_disjoint_of_ne
    (xs : List A) {a b : A} (r : ℕ) (hab : a ≠ b) :
    Disjoint (excessOccurrenceFiber xs a r)
      (excessOccurrenceFiber xs b r) := by
  classical
  exact (occurrenceFiber_disjoint_of_ne xs hab).mono
    (excessOccurrenceFiber_subset_occurrenceFiber xs a r)
    (excessOccurrenceFiber_subset_occurrenceFiber xs b r)

theorem cappedOccurrenceSelection_union_omitted
    (xs : List A) (r : ℕ) :
    cappedOccurrenceSelection xs r ∪
        cappedOmittedOccurrenceSelection xs r =
      (Finset.univ : Selection xs) := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

theorem cappedOccurrenceSelection_disjoint_omitted
    (xs : List A) (r : ℕ) :
    Disjoint (cappedOccurrenceSelection xs r)
      (cappedOmittedOccurrenceSelection xs r) := by
  classical
  exact Finset.disjoint_sdiff

/-- The omitted occurrences are precisely the disjoint union of the excess
parts of all value fibers. -/
theorem biUnion_excessOccurrenceFiber_eq_omitted
    (xs : List A) (r : ℕ) :
    (Finset.univ : Finset A).biUnion
        (fun a ↦ excessOccurrenceFiber xs a r) =
      cappedOmittedOccurrenceSelection xs r := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨a, _ha, hia⟩ := Finset.mem_biUnion.mp hi
    have hia' := Finset.mem_sdiff.mp hia
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hicap
    simp only [cappedOccurrenceSelection, Finset.mem_biUnion] at hicap
    obtain ⟨b, _hb, hib⟩ := hicap
    have hiaFiber : i ∈ occurrenceFiber xs a := hia'.1
    have hibFiber : i ∈ occurrenceFiber xs b :=
      cappedOccurrenceFiber_subset_occurrenceFiber xs b r hib
    have ha : occurrenceValue xs i = a := by
      simpa [occurrenceFiber] using hiaFiber
    have hb : occurrenceValue xs i = b := by
      simpa [occurrenceFiber] using hibFiber
    have hab : a = b := ha.symm.trans hb
    exact hia'.2 (by simpa [hab] using hib)
  · intro hi
    have hi' := Finset.mem_sdiff.mp hi
    apply Finset.mem_biUnion.mpr
    refine ⟨occurrenceValue xs i, Finset.mem_univ _, ?_⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [occurrenceFiber]
    · intro hicap
      apply hi'.2
      simp only [cappedOccurrenceSelection, Finset.mem_biUnion]
      exact ⟨occurrenceValue xs i, Finset.mem_univ _, hicap⟩

@[simp]
theorem card_cappedOmittedOccurrenceSelection
    (xs : List A) (r : ℕ) :
    (cappedOmittedOccurrenceSelection xs r).card =
      xs.length - cappedFiberMass xs r := by
  classical
  rw [cappedOmittedOccurrenceSelection,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    card_cappedOccurrenceSelection]
  simp

/-- If a value fiber is at most the cap, its canonical capped part is the
whole fiber. -/
theorem cappedOccurrenceFiber_eq_occurrenceFiber_of_card_le
    (xs : List A) (a : A) (r : ℕ)
    (hle : (occurrenceFiber xs a).card ≤ r) :
    cappedOccurrenceFiber xs a r = occurrenceFiber xs a := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (cappedOccurrenceFiber_subset_occurrenceFiber xs a r)
  rw [card_cappedOccurrenceFiber]
  simp [Nat.min_eq_right hle]

/-- Every omitted labelled occurrence belongs to a fiber strictly larger
than the cap. -/
theorem occurrenceFiber_card_gt_of_mem_cappedOmittedOccurrenceSelection
    (xs : List A) (r : ℕ) {i : Occurrence xs}
    (hi : i ∈ cappedOmittedOccurrenceSelection xs r) :
    r < (occurrenceFiber xs (occurrenceValue xs i)).card := by
  classical
  by_contra hnot
  have hle :
      (occurrenceFiber xs (occurrenceValue xs i)).card ≤ r :=
    Nat.le_of_not_gt hnot
  have heq := cappedOccurrenceFiber_eq_occurrenceFiber_of_card_le
    xs (occurrenceValue xs i) r hle
  have hiFiber :
      i ∈ occurrenceFiber xs (occurrenceValue xs i) := by
    simp [occurrenceFiber]
  have hiCapFiber :
      i ∈ cappedOccurrenceFiber xs (occurrenceValue xs i) r := by
    rw [heq]
    exact hiFiber
  have hi' := Finset.mem_sdiff.mp hi
  apply hi'.2
  simp only [cappedOccurrenceSelection, Finset.mem_biUnion]
  exact ⟨occurrenceValue xs i, Finset.mem_univ _, hiCapFiber⟩

/-- Exact per-value excess mass identity. -/
theorem sum_card_excessOccurrenceFiber
    (xs : List A) (r : ℕ) :
    (∑ a : A, (excessOccurrenceFiber xs a r).card) =
      xs.length - cappedFiberMass xs r := by
  classical
  have hpair : ((Finset.univ : Finset A) : Set A).PairwiseDisjoint
      (fun a ↦ excessOccurrenceFiber xs a r) := by
    intro a _ha b _hb hab
    exact excessOccurrenceFiber_disjoint_of_ne xs r hab
  rw [← Finset.card_biUnion hpair,
    biUnion_excessOccurrenceFiber_eq_omitted,
    card_cappedOmittedOccurrenceSelection]

/-- The same excess ledger written only in terms of source multiplicities. -/
theorem sum_occurrenceFiber_card_sub_cap
    (xs : List A) (r : ℕ) :
    (∑ a : A, ((occurrenceFiber xs a).card - r)) =
      xs.length - cappedFiberMass xs r := by
  classical
  simpa only [card_excessOccurrenceFiber] using
    sum_card_excessOccurrenceFiber xs r

/-- Exact global selected/omitted mass decomposition. -/
theorem cappedFiberMass_add_omitted_card
    (xs : List A) (r : ℕ) :
    cappedFiberMass xs r +
        (cappedOmittedOccurrenceSelection xs r).card = xs.length := by
  classical
  rw [card_cappedOmittedOccurrenceSelection]
  have hmass : cappedFiberMass xs r ≤ xs.length := by
    rw [← card_cappedOccurrenceSelection]
    simpa using Finset.card_le_card
      (Finset.subset_univ (cappedOccurrenceSelection xs r))
  omega

/-- If the capped mass misses a requested size `m`, then the canonical
omitted pool contains at least the source deficit `xs.length - m` plus one
additional labelled occurrence. -/
theorem deficit_add_one_le_card_cappedOmittedOccurrenceSelection
    (xs : List A) (r m : ℕ)
    (hsmall : cappedFiberMass xs r < m)
    (hm : m ≤ xs.length) :
    xs.length - m + 1 ≤
      (cappedOmittedOccurrenceSelection xs r).card := by
  rw [card_cappedOmittedOccurrenceSelection]
  omega

end GaoLean

#print axioms GaoLean.card_excessOccurrenceFiber
#print axioms GaoLean.biUnion_excessOccurrenceFiber_eq_omitted
#print axioms GaoLean.card_cappedOmittedOccurrenceSelection
#print axioms GaoLean.occurrenceFiber_card_gt_of_mem_cappedOmittedOccurrenceSelection
#print axioms GaoLean.sum_card_excessOccurrenceFiber
#print axioms GaoLean.deficit_add_one_le_card_cappedOmittedOccurrenceSelection
