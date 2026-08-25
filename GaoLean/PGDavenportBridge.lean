import GaoLean.PGSynthesis
import GaoLean.PGReflectionExtraction

/-!
# Ordinary Davenport lower witness in the generalized-dihedral group

This module constructs the lower-bound group witness from the frozen ordinary
Davenport hypothesis: take an occurrence-labelled zero-sum-free rotation word
of length `D-1` and append one reflection.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A]

/-- Selected reflection count is bounded by the total number of reflection
occurrences in the source. -/
theorem selectedReflectionCount_le_reflectionOccurrences_card
    (s : List (Group A)) (I : Selection s) :
    selectedReflectionCount s I ≤ (reflectionOccurrences s).card := by
  classical
  simp only [selectedReflectionCount, selectedMultiset,
    reflectionOccurrences, Multiset.countP_map]
  change (I.filter fun i => ¬IsRotation (occurrenceValue s i)).card ≤
    ((Finset.univ : Selection s).filter fun i =>
      ¬IsRotation (occurrenceValue s i)).card
  exact Finset.card_le_card (by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'.2⟩)

/-- Embed an additive word as rotations and append one distinguished
reflection. -/
def davenportLiftWord (w : List A) : List (Group A) :=
  w.map (data A).rot ++ [(data A).refl 0]

/-- The lifted word has at most one reflection occurrence. -/
theorem card_reflectionOccurrences_davenportLiftWord_le_one
    (w : List A) :
    (reflectionOccurrences (davenportLiftWord w)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply Fin.ext
  have index_of_reflection :
      ∀ k : Occurrence (davenportLiftWord w),
        k ∈ reflectionOccurrences (davenportLiftWord w) →
        k.1 = w.length := by
    intro k hk
    have hkRef : ¬IsRotation
        (occurrenceValue (davenportLiftWord w) k) := by
      simpa [reflectionOccurrences] using hk
    by_contra hkIndex
    have hklt : k.1 < w.length := by
      have hkBound := k.2
      simp only [davenportLiftWord, List.length_append, List.length_map,
        List.length_singleton] at hkBound
      omega
    let kw : Occurrence w := ⟨k.1, hklt⟩
    have hvalue :
        occurrenceValue (davenportLiftWord w) k =
          (data A).rot (occurrenceValue w kw) := by
      simp [davenportLiftWord, occurrenceValue, kw,
        List.get_eq_getElem, List.getElem_append_left, hklt]
    apply hkRef
    rw [hvalue]
    simp [IsRotation, GaoLean.GDihedralData.rot, data, rotation]
  exact index_of_reflection i hi |>.trans (index_of_reflection j hj).symm

/-- Zero selected reflection count means that every selected occurrence is a
rotation. -/
theorem allRotation_of_selectedReflectionCount_eq_zero
    (s : List (Group A)) (I : Selection s)
    (hzero : selectedReflectionCount s I = 0) :
    ∀ i ∈ I, IsRotation (occurrenceValue s i) := by
  classical
  intro i hi
  by_contra href
  have hzero' :
      (Multiset.filter (fun j =>
        ¬IsRotation (occurrenceValue s j)) I.1).card = 0 := by
    simpa [selectedReflectionCount, selectedMultiset,
      Multiset.countP_map] using hzero
  have hempty : Multiset.filter (fun j =>
      ¬IsRotation (occurrenceValue s j)) I.1 = 0 :=
    Multiset.card_eq_zero.mp hzero'
  have hmem : i ∈ Multiset.filter (fun j =>
      ¬IsRotation (occurrenceValue s j)) I.1 :=
    Multiset.mem_filter.mpr ⟨by simpa using hi, href⟩
  rw [hempty] at hmem
  simp at hmem

/-- A product-one selection has even selected reflection count. -/
theorem even_selectedReflectionCount_of_productOneSelection
    [Fintype A] (s : List (Group A)) (I : Selection s)
    (hprod : IsProductOneSelection s I) :
    Even (selectedReflectionCount s I) := by
  rcases hprod with ⟨word, hword, hprodWord⟩
  have heven := even_reflectionCount_of_word_prod_one word hprodWord
  simpa [selectedReflectionCount, reflectionMultiplicity, hword] using heven

/-- In a source with at most one reflection, every product-one selection is
all-rotation. -/
theorem allRotation_of_productOneSelection_of_reflection_card_le_one
    [Fintype A] (s : List (Group A)) (I : Selection s)
    (hsource : (reflectionOccurrences s).card ≤ 1)
    (hprod : IsProductOneSelection s I) :
    ∀ i ∈ I, IsRotation (occurrenceValue s i) := by
  have hle : selectedReflectionCount s I ≤ 1 :=
    (selectedReflectionCount_le_reflectionOccurrences_card s I).trans hsource
  rcases even_selectedReflectionCount_of_productOneSelection s I hprod with
    ⟨k, hk⟩
  have hzero : selectedReflectionCount s I = 0 := by omega
  exact allRotation_of_selectedReflectionCount_eq_zero s I hzero

/-- Canonical occurrence equivalence induced by mapping a list. -/
def mapOccurrenceEquiv {X B : Type*} (f : X → B) (s : List X) :
    Occurrence s ≃ Occurrence (s.map f) where
  toFun i := ⟨i.1, by rw [List.length_map]; exact i.2⟩
  invFun i := ⟨i.1, by simpa only [List.length_map] using i.2⟩
  left_inv i := by rfl
  right_inv i := by rfl

@[simp]
theorem mapOccurrenceEquiv_val {X B : Type*} (f : X → B) (s : List X)
    (i : Occurrence s) :
    (mapOccurrenceEquiv f s i).1 = i.1 := by
  rfl

@[simp]
theorem mapOccurrenceEquiv_symm_val {X B : Type*}
    (f : X → B) (s : List X) (i : Occurrence (s.map f)) :
    ((mapOccurrenceEquiv f s).symm i).1 = i.1 := by
  rfl

@[simp]
theorem occurrenceValue_mapOccurrenceEquiv {X B : Type*}
    (f : X → B) (s : List X) (i : Occurrence s) :
    occurrenceValue (s.map f) (mapOccurrenceEquiv f s i) =
      f (occurrenceValue s i) := by
  simp [occurrenceValue, mapOccurrenceEquiv, List.get_eq_getElem]

theorem occurrenceValue_mapOccurrenceEquiv_symm {X B : Type*}
    (f : X → B) (s : List X) (i : Occurrence (s.map f)) :
    f (occurrenceValue s ((mapOccurrenceEquiv f s).symm i)) =
      occurrenceValue (s.map f) i := by
  rw [← occurrenceValue_mapOccurrenceEquiv f s
    ((mapOccurrenceEquiv f s).symm i)]
  simp

/-- Pull an occurrence selection on a mapped list back to the original list. -/
noncomputable def pullbackMapSelection {X B : Type*}
    (f : X → B) (s : List X) (I : Selection (s.map f)) : Selection s := by
  classical
  exact I.map (mapOccurrenceEquiv f s).symm.toEmbedding

theorem selectedMultiset_pullbackMapSelection {X B : Type*}
    (f : X → B) (s : List X) (I : Selection (s.map f)) :
    (selectedMultiset s (pullbackMapSelection f s I)).map f =
      selectedMultiset (s.map f) I := by
  classical
  simp [selectedMultiset, pullbackMapSelection,
    occurrenceValue_mapOccurrenceEquiv_symm]

/-- A product-one selection from the lifted word would pull back to a
nonempty zero-sum selection of the original additive word. -/
theorem hasNonemptyZeroSum_of_productOneSelection_davenportLiftWord
    [Fintype A] (w : List A)
    (I : Selection (davenportLiftWord w)) (hIne : I.Nonempty)
    (hprod : IsProductOneSelection (davenportLiftWord w) I) :
    HasNonemptyZeroSum w := by
  classical
  change Selection
    (w.map (data A).rot ++ [(data A).refl 0]) at I
  change I.Nonempty at hIne
  change IsProductOneSelection
    (w.map (data A).rot ++ [(data A).refl 0]) I at hprod
  let rotations := w.map (data A).rot
  let reflection : Group A := (data A).refl 0
  have hall :=
    allRotation_of_productOneSelection_of_reflection_card_le_one
      (rotations ++ [reflection]) I
      (by simpa [rotations, reflection, davenportLiftWord] using
        card_reflectionOccurrences_davenportLiftWord_le_one w) hprod
  have hprefix : I ⊆ prefixOccurrences rotations [reflection] := by
    intro i hi
    have hrot := hall i hi
    have hibound := i.2
    have hibound' : i.1 < rotations.length + 1 := by
      simpa [rotations] using hibound
    have hlt : i.1 < rotations.length := by
      by_contra hnot
      have hieq : i.1 = rotations.length := by omega
      have hvalue : occurrenceValue (rotations ++ [reflection]) i = reflection := by
        simp [occurrenceValue, List.get_eq_getElem, hieq,
          List.getElem_append_right]
      rw [hvalue] at hrot
      simp [reflection, IsRotation] at hrot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
  have hinter : I ∩ prefixOccurrences rotations [reflection] = I :=
    Finset.inter_eq_left.mpr hprefix
  let Jrot := prefixSelection rotations [reflection] I
  have hmapJrot : Jrot.map
        (appendLeftOccurrenceEmbedding rotations [reflection]) = I := by
    have h := map_prefixSelection_eq_inter rotations [reflection] I
    rw [hinter] at h
    simpa [Jrot] using h
  have hJrotNe : Jrot.Nonempty := by
    rcases hIne with ⟨i, hi⟩
    have hiMap : i ∈ Jrot.map
        (appendLeftOccurrenceEmbedding rotations [reflection]) := by
      simpa [hmapJrot] using hi
    rcases Finset.mem_map.mp hiMap with ⟨j, hj, _⟩
    exact ⟨j, hj⟩
  have hselectedJrot : selectedMultiset rotations Jrot =
      selectedMultiset (rotations ++ [reflection]) I := by
    have h := selectedMultiset_prefixSelection rotations [reflection] I
    rw [hinter] at h
    simpa [Jrot] using h
  rcases hprod with ⟨word, hword, hprodWord⟩
  have hword' : Multiset.ofList word =
      selectedMultiset (rotations ++ [reflection]) I := by
    simpa [rotations, reflection] using hword
  have hallWord : ∀ g ∈ word, IsRotation g := by
    intro g hg
    have hgSelected : g ∈ selectedMultiset (rotations ++ [reflection]) I := by
      rw [← hword']
      simpa using hg
    rw [selectedMultiset] at hgSelected
    rcases Multiset.mem_map.mp hgSelected with ⟨i, hi, rfl⟩
    exact hall i hi
  have hwordSum :=
    sum_coordinate_eq_zero_of_prod_one word hallWord hprodWord
  have hselectedSum :
      ((selectedMultiset (rotations ++ [reflection]) I).map coordinate).sum = 0 := by
    rw [← hword']
    simpa using hwordSum
  have hJrotSum :
      ((selectedMultiset rotations Jrot).map coordinate).sum = 0 := by
    rw [hselectedJrot]
    exact hselectedSum
  let J := pullbackMapSelection (data A).rot w Jrot
  have hJNe : J.Nonempty := by
    rcases hJrotNe with ⟨j, hj⟩
    refine ⟨(mapOccurrenceEquiv (data A).rot w).symm j, ?_⟩
    exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
  have hpull :
      (selectedMultiset w J).map (data A).rot =
        selectedMultiset rotations Jrot := by
    simpa [J, rotations] using
      selectedMultiset_pullbackMapSelection (data A).rot w Jrot
  have hJSum : (selectedMultiset w J).sum = 0 := by
    rw [← hpull] at hJrotSum
    simpa [coordinate, GaoLean.GDihedralData.rot, data, rotation] using
      hJrotSum
  refine ⟨J, hJNe, ?_⟩
  simpa [selectedMultiset] using hJSum

/-- A zero-sum-free additive word lifts to a product-one-free group word after
one reflection is appended. -/
theorem isProductOneFreeSelection_davenportLiftWord
    [Fintype A] (w : List A) (hfree : ¬HasNonemptyZeroSum w) :
    IsProductOneFreeSelection (davenportLiftWord w) Finset.univ := by
  intro I _ hIne hprod
  exact hfree
    (hasNonemptyZeroSum_of_productOneSelection_davenportLiftWord
      w I hIne hprod)

/-- The frozen ordinary Davenport hypothesis internally supplies the exact
length-`D` group witness needed by the PG-GAO lower construction. -/
theorem smallDavenportWitness_of_isOrdinaryDavenportConstant
    [Fintype A] (D : ℕ) (hD : IsOrdinaryDavenportConstant A D) :
    SmallDavenportWitness (Group A) D := by
  have hDpos : 0 < D := by
    by_contra hnot
    have hDzero : D = 0 := Nat.eq_zero_of_not_pos hnot
    have hempty := hD.1 ([] : List A) (by simp [hDzero])
    rcases hempty with ⟨I, hIne, _⟩
    rcases hIne with ⟨i, _⟩
    exact Fin.elim0 i
  have hpred : D - 1 < D := by omega
  rcases hD.2 (D - 1) hpred with ⟨w, hwlen, hwfree⟩
  refine ⟨davenportLiftWord w, ?_, ?_⟩
  · simp [davenportLiftWord, hwlen]
    omega
  · exact isProductOneFreeSelection_davenportLiftWord w hwfree

/-- The conditional PG-GAO theorem no longer needs a separate lower witness:
the frozen ordinary Davenport hypothesis constructs it internally. -/
theorem pgGaoV1_of_upperInputs_and_isOrdinaryDavenportConstant
    [Fintype A] (D : ℕ) (hDQ : D ≤ Nat.card A)
    (hAodd : Odd (Nat.card A)) (hupper : PGGaoUpperInputs A D)
    (hD : IsOrdinaryDavenportConstant A D) :
    PGGaoV1 A D := by
  exact pgGaoV1_of_upperInputs_and_smallDavenportWitness
    D hDQ hAodd hupper
      (smallDavenportWitness_of_isOrdinaryDavenportConstant D hD)

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.selectedReflectionCount_le_reflectionOccurrences_card
#print axioms GaoLean.ConcreteGDihedral.card_reflectionOccurrences_davenportLiftWord_le_one
#print axioms GaoLean.ConcreteGDihedral.allRotation_of_productOneSelection_of_reflection_card_le_one
#print axioms GaoLean.ConcreteGDihedral.hasNonemptyZeroSum_of_productOneSelection_davenportLiftWord
#print axioms GaoLean.ConcreteGDihedral.isProductOneFreeSelection_davenportLiftWord
#print axioms GaoLean.ConcreteGDihedral.smallDavenportWitness_of_isOrdinaryDavenportConstant
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_upperInputs_and_isOrdinaryDavenportConstant
