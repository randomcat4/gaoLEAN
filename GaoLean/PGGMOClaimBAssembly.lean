import GaoLean.PGGMOClaimBOccurrence
import GaoLean.PGGMOClaimBAlgebra

/-!
# Labelled subpartition assembly for ordinary GMO Claim B

This module constructs the Claim-B subsequence from selected cells of the
actual Theorem-E replacement partition.  Selected layers are filtered at the
labelled-occurrence level; omitted layers contribute one retained labelled
occurrence each; and occurrences outside the replacement support contribute
the exact source deficit `|S| - |S'|`.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Canonical embedding of the first `r` cells when `r ≤ n`. -/
def initialCellEmbedding {r n : ℕ} (hr : r ≤ n) : Fin r ↪ Fin n where
  toFun j := ⟨j, lt_of_lt_of_le j.isLt hr⟩
  inj' := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun x : Fin n ↦ x.val) h

/-- The original cell indices selected by an embedding `Fin r ↪ Fin n`. -/
noncomputable def selectedCellIndices {r n : ℕ} (e : Fin r ↪ Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.image e

/-- The original cell indices not used by the embedded `r`-cell
subpartition. -/
noncomputable def unselectedCellIndices {r n : ℕ} (e : Fin r ↪ Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ \ selectedCellIndices e

@[simp]
theorem mem_selectedCellIndices_iff {r n : ℕ} (e : Fin r ↪ Fin n)
    (c : Fin n) :
    c ∈ selectedCellIndices e ↔ ∃ j : Fin r, e j = c := by
  classical
  simp [selectedCellIndices]

@[simp]
theorem mem_unselectedCellIndices_iff {r n : ℕ} (e : Fin r ↪ Fin n)
    (c : Fin n) :
    c ∈ unselectedCellIndices e ↔ ∀ j : Fin r, e j ≠ c := by
  classical
  simp [unselectedCellIndices, mem_selectedCellIndices_iff]

theorem card_unselectedCellIndices {r n : ℕ} (e : Fin r ↪ Fin n) :
    (unselectedCellIndices e).card = n - r := by
  classical
  unfold unselectedCellIndices selectedCellIndices
  rw [Finset.card_sdiff]
  simp [Finset.card_image_of_injective, e.injective]

/-- The genuine labelled support obtained by taking the common-core part of
the embedded original cells. -/
noncomputable def Theorem21SetPartition.insideCoreEmbeddedSupport
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) : Selection xs := by
  classical
  exact Finset.univ.biUnion fun j ↦ P.insideCoreCell H (e j)

/-- Its literal occurrence cardinality. -/
noncomputable def Theorem21SetPartition.insideCoreEmbeddedSupportCard
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) : ℕ :=
  (P.insideCoreEmbeddedSupport H e).card

/-- The actual `r`-setpartition formed from the common-core occurrence
filters of the embedded original cells. -/
noncomputable def Theorem21SetPartition.insideCoreEmbeddedPartition
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hne : ∀ j : Fin r, (P.insideCoreCell H (e j)).Nonempty) :
    Theorem21SetPartition xs r (P.insideCoreEmbeddedSupportCard H e) := by
  classical
  refine {
    cells := fun j ↦ P.insideCoreCell H (e j)
    cells_nonempty := hne
    cells_pairwise_disjoint := ?_
    value_injective := ?_
    card_support := rfl
  }
  · intro j k hjk
    have hek : e j ≠ e k := fun h ↦ hjk (e.injective h)
    exact (P.cells_pairwise_disjoint hek).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  · intro j
    exact (P.value_injective (e j)).mono (by
      intro i hi
      exact (P.mem_insideCoreCell_iff H (e j) i).1 hi |>.1)

/-- First-`r` specialization of the genuine embedded construction. -/
noncomputable def Theorem21SetPartition.insideCoreInitialPartition
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (hr : r ≤ n)
    (hne : ∀ j : Fin r,
      (P.insideCoreCell H (initialCellEmbedding hr j)).Nonempty) :
    Theorem21SetPartition xs r
      (P.insideCoreEmbeddedSupportCard H (initialCellEmbedding hr)) :=
  P.insideCoreEmbeddedPartition H (initialCellEmbedding hr) hne

@[simp]
theorem Theorem21SetPartition.support_insideCoreEmbeddedPartition
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hne : ∀ j : Fin r, (P.insideCoreCell H (e j)).Nonempty) :
    (P.insideCoreEmbeddedPartition H e hne).support =
      P.insideCoreEmbeddedSupport H e := by
  rfl

/-- The constructed support is a literal labelled subsequence of the
Theorem-E replacement support. -/
theorem Theorem21SetPartition.insideCoreEmbeddedSupport_subset_support
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) :
    P.insideCoreEmbeddedSupport H e ⊆ P.support := by
  classical
  intro i hi
  obtain ⟨j, -, hij⟩ := Finset.mem_biUnion.mp hi
  have hiCell := (P.mem_insideCoreCell_iff H (e j) i).1 hij |>.1
  apply Finset.mem_biUnion.mpr
  exact ⟨e j, Finset.mem_univ _, hiCell⟩

/-- Every new value cell is exactly the already verified core value cell of
its embedded original layer. -/
theorem Theorem21SetPartition.valueCell_insideCoreEmbeddedPartition
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hne : ∀ j : Fin r, (P.insideCoreCell H (e j)).Nonempty)
    (j : Fin r) :
    (P.insideCoreEmbeddedPartition H e hne).valueCell j =
      P.coreValueCell H (e j) := by
  classical
  ext x
  rw [P.mem_coreValueCell_iff_exists_insideCoreCell H (e j) x]
  simp [Theorem21SetPartition.valueCell,
    Theorem21SetPartition.insideCoreEmbeddedPartition]

/-- Exact ordered value-cell ledger for the constructed subpartition. -/
theorem Theorem21SetPartition.valueCells_insideCoreEmbeddedPartition
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hne : ∀ j : Fin r, (P.insideCoreCell H (e j)).Nonempty) :
    (P.insideCoreEmbeddedPartition H e hne).valueCells =
      List.ofFn fun j : Fin r ↦ P.coreValueCell H (e j) := by
  classical
  simp [Theorem21SetPartition.valueCells,
    P.valueCell_insideCoreEmbeddedPartition H e hne]

/-- The literal iterated sum of the embedded core value cells, with the
classical finite-set implementation hidden behind one shared definition. -/
noncomputable def Theorem21SetPartition.insideCoreEmbeddedIteratedSum
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) : Finset A := by
  classical
  exact iteratedFinsetSum
    (List.ofFn fun j : Fin r ↦ P.coreValueCell H (e j))

/-- The constructed Claim-B sumset is the literal iterated sum of the
selected core value cells. -/
theorem Theorem21SetPartition.sumset_insideCoreEmbeddedPartition
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hne : ∀ j : Fin r, (P.insideCoreCell H (e j)).Nonempty) :
    (P.insideCoreEmbeddedPartition H e hne).sumset =
      P.insideCoreEmbeddedIteratedSum H e := by
  classical
  unfold Theorem21SetPartition.insideCoreEmbeddedIteratedSum
  rw [Theorem21SetPartition.sumset,
    fullLayerSumSpectrum_eq_iteratedFinsetSum,
    P.valueCells_insideCoreEmbeddedPartition H e hne]

/-- Cellwise coset representatives are injective because distinct original
cells are occurrence-disjoint. -/
theorem Theorem21SetPartition.CellCosetOccurrenceChoice.occurrence_injective
    {xs : List A} {n m : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g) :
    Function.Injective choice.occurrence := by
  intro c d hcd
  by_contra hne
  have hdisj := P.cells_pairwise_disjoint hne
  rw [Finset.disjoint_left] at hdisj
  exact hdisj (choice.mem_cell c) (hcd ▸ choice.mem_cell d)

/-- One genuine labelled coset occurrence retained from every omitted
original layer. -/
noncomputable def Theorem21SetPartition.retainedUnselectedOccurrences
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n) : Selection xs := by
  classical
  exact (unselectedCellIndices e).image choice.occurrence

theorem Theorem21SetPartition.card_retainedUnselectedOccurrences
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n) :
    (P.retainedUnselectedOccurrences choice e).card = n - r := by
  classical
  unfold Theorem21SetPartition.retainedUnselectedOccurrences
  rw [Finset.card_image_of_injective (unselectedCellIndices e)
      choice.occurrence_injective,
    card_unselectedCellIndices]

/-- Retained omitted-layer occurrences belong to the old replacement
support. -/
theorem Theorem21SetPartition.retainedUnselectedOccurrences_subset_support
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n) :
    P.retainedUnselectedOccurrences choice e ⊆ P.support := by
  classical
  intro i hi
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.mem_biUnion.mpr
  exact ⟨c, Finset.mem_univ _, choice.mem_cell c⟩

/-- Every retained omitted-layer occurrence still has value in the chosen
coset. -/
theorem Theorem21SetPartition.retainedUnselectedOccurrences_value_mem_coset
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n) {i : Occurrence xs}
    (hi : i ∈ P.retainedUnselectedOccurrences choice e) :
    occurrenceValue xs i ∈ addCosetFinset H g := by
  classical
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hi
  exact choice.value_mem_coset c

/-- Omitted-layer representatives are disjoint from the selected
common-core subpartition support. -/
theorem Theorem21SetPartition.retainedUnselectedOccurrences_disjoint_insideCoreEmbeddedSupport
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {K : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice K g)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) :
    Disjoint (P.retainedUnselectedOccurrences choice e)
      (P.insideCoreEmbeddedSupport H e) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiRet hiSelected
  obtain ⟨c, hcUnselected, rfl⟩ := Finset.mem_image.mp hiRet
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hiSelected
  have hce : c ≠ e j := by
    exact ((mem_unselectedCellIndices_iff e c).1 hcUnselected j).symm
  have hdisj := P.cells_pairwise_disjoint hce
  rw [Finset.disjoint_left] at hdisj
  exact hdisj (choice.mem_cell c)
    ((P.mem_insideCoreCell_iff H (e j) (choice.occurrence c)).1 hj |>.1)

/-- The complete labelled reserve: one term from every omitted replacement
cell, plus every occurrence outside the replacement support. -/
noncomputable def Theorem21SetPartition.claimBReserve
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n) : Selection xs := by
  classical
  exact P.retainedUnselectedOccurrences choice e ∪
    ((Finset.univ : Selection xs) \ P.support)

/-- Exact reserve count `(n-r) + (|S|-m)` at the occurrence level. -/
theorem Theorem21SetPartition.card_claimBReserve
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n) :
    (P.claimBReserve choice e).card = (n - r) + (xs.length - m) := by
  classical
  unfold Theorem21SetPartition.claimBReserve
  have hdisj : Disjoint (P.retainedUnselectedOccurrences choice e)
      ((Finset.univ : Selection xs) \ P.support) :=
    (P.support_disjoint_unused).mono
      (P.retainedUnselectedOccurrences_subset_support choice e) (by rfl)
  rw [Finset.card_union_of_disjoint hdisj,
    P.card_retainedUnselectedOccurrences choice e, P.card_unused]

/-- The full reserve is disjoint from the constructed Claim-B support. -/
theorem Theorem21SetPartition.claimBReserve_disjoint_insideCoreEmbeddedSupport
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {K : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice K g)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) :
    Disjoint (P.claimBReserve choice e)
      (P.insideCoreEmbeddedSupport H e) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiReserve hiSelected
  rcases Finset.mem_union.mp hiReserve with hiRet | hiOutside
  · exact (Finset.disjoint_left.mp
      (P.retainedUnselectedOccurrences_disjoint_insideCoreEmbeddedSupport
        choice H e)) hiRet hiSelected
  · have hiP : i ∉ P.support := (Finset.mem_sdiff.mp hiOutside).2
    exact hiP (P.insideCoreEmbeddedSupport_subset_support H e hiSelected)

/-- If the original unused occurrences also lie in `g+H`, every labelled
reserve occurrence lies there. -/
theorem Theorem21SetPartition.claimBReserve_value_mem_coset
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {H : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice H g)
    (e : Fin r ↪ Fin n)
    (hallUnused : ∀ i : Occurrence xs, i ∉ P.support →
      occurrenceValue xs i ∈ addCosetFinset H g)
    {i : Occurrence xs} (hi : i ∈ P.claimBReserve choice e) :
    occurrenceValue xs i ∈ addCosetFinset H g := by
  classical
  rcases Finset.mem_union.mp hi with hiRet | hiOutside
  · exact P.retainedUnselectedOccurrences_value_mem_coset choice e hiRet
  · exact hallUnused i (Finset.mem_sdiff.mp hiOutside).2

/-- The reserve embeds in the unused-in-coset selection of the constructed
subpartition.  Thus the later Claim-B `remaining_in_coset` inequality is a
cardinality consequence, not an assumed output field. -/
theorem Theorem21SetPartition.claimBReserve_subset_unusedInAddCoset
    {xs : List A} {n m r : ℕ} {P : Theorem21SetPartition xs n m}
    {K : AddSubgroup A} {g : A} (choice : P.CellCosetOccurrenceChoice K g)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hne : ∀ j : Fin r, (P.insideCoreCell H (e j)).Nonempty)
    (hallUnused : ∀ i : Occurrence xs, i ∉ P.support →
      occurrenceValue xs i ∈ addCosetFinset K g) :
    P.claimBReserve choice e ⊆
      (P.insideCoreEmbeddedPartition H e hne).unusedInAddCoset K g := by
  intro i hi
  apply ((P.insideCoreEmbeddedPartition H e hne).mem_unusedInAddCoset_iff
    K g i).2
  constructor
  · intro hiSupport
    have hiSelected : i ∈ P.insideCoreEmbeddedSupport H e := by
      simpa using hiSupport
    exact (Finset.disjoint_left.mp
      (P.claimBReserve_disjoint_insideCoreEmbeddedSupport choice H e))
      hi hiSelected
  · exact P.claimBReserve_value_mem_coset choice e hallUnused hi

/-- Mechanical assembly of the genuine Claim-B payload.  The saturation
input is the algebraic equality for the explicit iterated list of core value
cells; `saturation` for the constructed partition is then obtained by the
proved sumset ledger.  The `remaining_in_coset` field is *not* assumed: it
follows from the disjoint labelled reserve of the omitted cells and the
exact `|S|-|S'|` complement. -/
noncomputable def ordinaryGMOClaimBOutput_of_insideCoreEmbeddedPartition
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P : Theorem21SetPartition xs n seed.card)
    (H K : AddSubgroup A) (hK : K ≠ ⊥) (g : A)
    (e : Fin (pGroupDStar K) ↪ Fin n)
    (hne : ∀ j : Fin (pGroupDStar K),
      (P.insideCoreCell H (e j)).Nonempty)
    (choice : P.CellCosetOccurrenceChoice K g)
    (hselected : ∀ (j : Fin (pGroupDStar K)) (i : Occurrence xs),
      i ∈ P.insideCoreCell H (e j) →
        occurrenceValue xs i ∈ addCosetFinset K g)
    (hallUnused : ∀ i : Occurrence xs, i ∉ P.support →
      occurrenceValue xs i ∈ addCosetFinset K g)
    (hsaturation :
      P.insideCoreEmbeddedIteratedSum H e =
        addCosetFinset K ((pGroupDStar K) • g)) :
    OrdinaryGMOClaimBOutput xs seed n := by
  classical
  let Q := P.insideCoreEmbeddedPartition H e hne
  refine {
    K := K
    nontrivial := hK
    g := g
    supportCard := P.insideCoreEmbeddedSupportCard H e
    partition := Q
    support_in_coset := ?_
    saturation := ?_
    remaining_in_coset := ?_
  }
  · intro i hi
    have hi' : i ∈ P.insideCoreEmbeddedSupport H e := by
      simpa [Q] using hi
    obtain ⟨j, -, hij⟩ := Finset.mem_biUnion.mp hi'
    exact hselected j i hij
  · simpa [Q] using
      (P.sumset_insideCoreEmbeddedPartition H e hne).trans hsaturation
  · have hsub := P.claimBReserve_subset_unusedInAddCoset
      choice H e hne hallUnused
    have hcard := Finset.card_le_card hsub
    rw [P.card_claimBReserve choice e] at hcard
    exact hcard

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.insideCoreEmbeddedSupport_subset_support
#print axioms GaoLean.Theorem21SetPartition.sumset_insideCoreEmbeddedPartition
#print axioms GaoLean.Theorem21SetPartition.card_claimBReserve
#print axioms GaoLean.Theorem21SetPartition.claimBReserve_subset_unusedInAddCoset
#print axioms GaoLean.ordinaryGMOClaimBOutput_of_insideCoreEmbeddedPartition
