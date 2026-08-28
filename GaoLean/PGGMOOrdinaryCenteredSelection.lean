import GaoLean.PGGMOOrdinaryStep1

/-!
# Occurrence-faithful centering of a selected coset subsequence

A selected family of labelled source occurrences lying in one affine coset is
reindexed, in the fixed order of its attached finset, as a genuine list in the
subgroup.  Every later selection is transported back through one explicit
embedding of occurrences.  Thus repetitions of source values remain distinct,
and all cardinality and sum statements refer to the original labels.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The selected source occurrences, centered at `alpha`, as a genuine list
in `K`.  The order is exactly `C.attach.toList`. -/
noncomputable def cosetCenteredSelectionList
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K) : List K := by
  classical
  exact C.attach.toList.map fun i ↦
    ⟨occurrenceValue xs i.1 - alpha, hC i.1 i.2⟩

@[simp]
theorem length_cosetCenteredSelectionList
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K) :
    (cosetCenteredSelectionList xs K alpha C hC).length = C.card := by
  classical
  simp [cosetCenteredSelectionList]

/-- The occurrence of the original source represented by one occurrence of
the centered list.  Injectivity is the nodup property of `C.attach.toList`. -/
noncomputable def cosetCenteredOccurrenceEmbedding
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K) :
    Occurrence (cosetCenteredSelectionList xs K alpha C hC) ↪
      Occurrence xs := by
  classical
  let index :
      Occurrence (cosetCenteredSelectionList xs K alpha C hC) →
        Fin C.attach.toList.length := fun i ↦
    ⟨i.1, by
      simpa [cosetCenteredSelectionList] using i.2⟩
  refine {
    toFun := fun i ↦ (C.attach.toList.get (index i)).1
    inj' := ?_
  }
  intro i j hij
  have hget :
      C.attach.toList.get (index i) =
        C.attach.toList.get (index j) := by
    apply Subtype.ext
    exact hij
  have hindex : index i = index j :=
    C.attach.nodup_toList.injective_get hget
  apply Fin.ext
  exact congrArg
    (fun q : Fin C.attach.toList.length => q.val) hindex

theorem cosetCenteredOccurrenceEmbedding_mem
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (j : Occurrence (cosetCenteredSelectionList xs K alpha C hC)) :
    cosetCenteredOccurrenceEmbedding xs K alpha C hC j ∈ C := by
  classical
  unfold cosetCenteredOccurrenceEmbedding
  dsimp only
  exact (C.attach.toList.get _).2

/-- The centered value at a reindexed occurrence is literally the displacement
of its original source value from `alpha`. -/
theorem coe_occurrenceValue_cosetCenteredSelectionList
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (j : Occurrence (cosetCenteredSelectionList xs K alpha C hC)) :
    ((occurrenceValue
        (cosetCenteredSelectionList xs K alpha C hC) j : K) : A) =
      occurrenceValue xs
        (cosetCenteredOccurrenceEmbedding xs K alpha C hC j) - alpha := by
  classical
  simp [cosetCenteredSelectionList, cosetCenteredOccurrenceEmbedding,
    occurrenceValue, List.get_eq_getElem]
  congr

/-- Equivalently, restoring the affine center recovers the original value. -/
theorem occurrenceValue_cosetCenteredOccurrenceEmbedding
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (j : Occurrence (cosetCenteredSelectionList xs K alpha C hC)) :
    occurrenceValue xs
        (cosetCenteredOccurrenceEmbedding xs K alpha C hC j) =
      alpha +
        ((occurrenceValue
          (cosetCenteredSelectionList xs K alpha C hC) j : K) : A) := by
  have hcentered :=
    coe_occurrenceValue_cosetCenteredSelectionList xs K alpha C hC j
  rw [hcentered]
  abel

/-- Push a selection of centered-list positions back to the original labelled
source. -/
noncomputable def mapCosetCenteredSelection
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (J : Selection (cosetCenteredSelectionList xs K alpha C hC)) :
    Selection xs :=
  J.map (cosetCenteredOccurrenceEmbedding xs K alpha C hC)

theorem mapCosetCenteredSelection_subset
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (J : Selection (cosetCenteredSelectionList xs K alpha C hC)) :
    mapCosetCenteredSelection xs K alpha C hC J ⊆ C := by
  classical
  intro i hi
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
  exact cosetCenteredOccurrenceEmbedding_mem xs K alpha C hC j

@[simp]
theorem card_mapCosetCenteredSelection
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (J : Selection (cosetCenteredSelectionList xs K alpha C hC)) :
    (mapCosetCenteredSelection xs K alpha C hC J).card = J.card := by
  classical
  simp [mapCosetCenteredSelection]

/-- Exact affine sum transport for every finite selection of centered
occurrences. -/
theorem sum_mapCosetCenteredSelection
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (J : Selection (cosetCenteredSelectionList xs K alpha C hC)) :
    (∑ i ∈ mapCosetCenteredSelection xs K alpha C hC J,
        occurrenceValue xs i) =
      J.card • alpha +
        (((∑ j ∈ J,
          occurrenceValue
            (cosetCenteredSelectionList xs K alpha C hC) j) : K) : A) := by
  classical
  rw [mapCosetCenteredSelection, Finset.sum_map]
  calc
    (∑ j ∈ J,
        occurrenceValue xs
          (cosetCenteredOccurrenceEmbedding xs K alpha C hC j)) =
        ∑ j ∈ J, (alpha +
          ((occurrenceValue
            (cosetCenteredSelectionList xs K alpha C hC) j : K) : A)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact occurrenceValue_cosetCenteredOccurrenceEmbedding
        xs K alpha C hC j
    _ = J.card • alpha +
        ∑ j ∈ J,
          ((occurrenceValue
            (cosetCenteredSelectionList xs K alpha C hC) j : K) : A) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = J.card • alpha +
        (((∑ j ∈ J,
          occurrenceValue
            (cosetCenteredSelectionList xs K alpha C hC) j) : K) : A) := by
      simpa using
        (map_sum K.subtype (fun j => occurrenceValue
          (cosetCenteredSelectionList xs K alpha C hC) j) J).symm

/-- A full centered `k`-spectrum gives, for every literal subgroup element,
an occurrence-faithful `k`-selection inside the one fixed carrier `C`. -/
theorem exists_selection_subset_of_cosetCentered_spectrumFull
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (k : ℕ)
    (hfull :
      OrdinarySpectrumFull
        (cosetCenteredSelectionList xs K alpha C hC) k)
    (h : A) (hh : h ∈ K) :
    ∃ I : Selection xs,
      I ⊆ C ∧ I.card = k ∧
        (∑ i ∈ I, occurrenceValue xs i) = k • alpha + h := by
  obtain ⟨J, hJcard, hJsum⟩ := hfull ⟨h, hh⟩
  let I := mapCosetCenteredSelection xs K alpha C hC J
  refine ⟨I, mapCosetCenteredSelection_subset xs K alpha C hC J,
    ?_, ?_⟩
  · simpa only [I, card_mapCosetCenteredSelection] using hJcard
  · have hsum :=
      sum_mapCosetCenteredSelection xs K alpha C hC J
    have hJsumCoe :
        (((∑ j ∈ J,
          occurrenceValue
            (cosetCenteredSelectionList xs K alpha C hC) j) : K) : A) = h :=
      congrArg Subtype.val hJsum
    rw [hJcard, hJsumCoe] at hsum
    exact hsum

/-- Field-level adapter to the existing Step-1 core.  The fixed centered
carrier `C` supplies the core, while an independently supplied outer
container retains the ambient `d*(A)` reserve budget. -/
noncomputable def ordinaryGMOStep1Core_of_cosetCentered_spectrumFull
    (xs : List A) (K : AddSubgroup A) (alpha : A)
    (C outerContainer : Selection xs)
    (hC : ∀ i ∈ C, occurrenceValue xs i - alpha ∈ K)
    (hCouter : C ⊆ outerContainer)
    (houterCoset : ∀ i ∈ outerContainer,
      occurrenceValue xs i ∈ addCosetFinset K alpha)
    (houterBudget :
      Nat.card K + pGroupDStar A ≤ outerContainer.card)
    (hCcard : C.card = Nat.card K + pGroupDStar K)
    (hfull :
      OrdinarySpectrumFull
        (cosetCenteredSelectionList xs K alpha C hC) (Nat.card K)) :
    OrdinaryGMOStep1Core xs where
  H := K
  beta := alpha
  container := outerContainer
  core := C
  core_subset_container := hCouter
  container_in_coset := houterCoset
  container_card_lower := houterBudget
  core_card := hCcard
  core_full := by
    intro h hh
    exact exists_selection_subset_of_cosetCentered_spectrumFull
      xs K alpha C hC (Nat.card K) hfull h hh

end GaoLean

#print axioms GaoLean.length_cosetCenteredSelectionList
#print axioms GaoLean.cosetCenteredOccurrenceEmbedding_mem
#print axioms GaoLean.coe_occurrenceValue_cosetCenteredSelectionList
#print axioms GaoLean.occurrenceValue_cosetCenteredOccurrenceEmbedding
#print axioms GaoLean.mapCosetCenteredSelection_subset
#print axioms GaoLean.card_mapCosetCenteredSelection
#print axioms GaoLean.sum_mapCosetCenteredSelection
#print axioms GaoLean.exists_selection_subset_of_cosetCentered_spectrumFull
#print axioms GaoLean.ordinaryGMOStep1Core_of_cosetCentered_spectrumFull
