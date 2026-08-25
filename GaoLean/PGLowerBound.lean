import GaoLean.PGBase

/-!
# Occurrence-faithful PG lower bound

This module formalizes the elementary lower-bound construction in A-R6,
Section 2.  A product-one-free sequence of length `D` is padded by fewer than
`k` labelled identities.  Any selected `k` occurrences must contain a
nonempty part of the original sequence; deleting only the padded identity
occurrences preserves a product-one ordering and contradicts freeness.

Equal group values are never used to distinguish the original and padded
positions.  The split is performed on occurrence indices.
-/

namespace GaoLean

section GenericIdentityDeletion

variable {G : Type*} [Group G] [DecidableEq G]

/-- Filtering a labelled selection by a value predicate commutes with
forgetting its labels. -/
theorem selectedMultiset_filter_value
    (s : List G) (I : Selection s) (p : G → Prop) [DecidablePred p] :
    selectedMultiset s (I.filter fun i => p (occurrenceValue s i)) =
      (selectedMultiset s I).filter p := by
  classical
  simp [selectedMultiset, Multiset.filter_map]

/-- Removing all selected nonidentity occurrences from a product-one
selection leaves the exact filtered product-one certificate. -/
theorem IsProductOneSelection.filter_ne_one
    {s : List G} {I : Selection s} (hI : IsProductOneSelection s I) :
    IsProductOneSelection s
      (I.filter fun i => occurrenceValue s i ≠ 1) := by
  classical
  have hfiltered := hasProductOneOrdering_filter_ne_one hI
  rw [← selectedMultiset_filter_value s I (fun g => g ≠ 1)] at hfiltered
  exact hfiltered

/-- Deleting an occurrence subset consisting only of identities preserves a
product-one selection.  The deleted occurrences are identified by labels,
not by their values. -/
theorem IsProductOneSelection.sdiff_of_all_one
    {s : List G} {I J : Selection s}
    (hI : IsProductOneSelection s I) (hJI : J ⊆ I)
    (hone : ∀ i ∈ I \ J, occurrenceValue s i = 1) :
    IsProductOneSelection s J := by
  classical
  let N : Selection s := I.filter fun i => occurrenceValue s i ≠ 1
  have hNprod : IsProductOneSelection s N := by
    exact hI.filter_ne_one
  have hNJ : N ⊆ J := by
    intro i hiN
    have hiI : i ∈ I := (Finset.mem_filter.mp hiN).1
    by_contra hiJ
    have honeI : occurrenceValue s i = 1 :=
      hone i (Finset.mem_sdiff.mpr ⟨hiI, hiJ⟩)
    exact (Finset.mem_filter.mp hiN).2 honeI
  let E : Selection s := J \ N
  have hEone : ∀ i ∈ E, occurrenceValue s i = 1 := by
    intro i hiE
    have hiJ : i ∈ J := (Finset.mem_sdiff.mp hiE).1
    have hiI : i ∈ I := hJI hiJ
    have hiNotN : i ∉ N := (Finset.mem_sdiff.mp hiE).2
    by_contra hne
    exact hiNotN (Finset.mem_filter.mpr ⟨hiI, hne⟩)
  have hEprod : IsProductOneSelection s E :=
    isProductOneSelection_of_all_one s E hEone
  have hdis : Disjoint N E := by
    exact Finset.disjoint_sdiff
  have hunion : N ∪ E = J := by
    exact Finset.union_sdiff_of_subset hNJ
  rw [← hunion]
  exact hNprod.union hdis hEprod

end GenericIdentityDeletion

section PrefixOccurrences

variable {G : Type*}

/-- Embed an occurrence of the left list into the corresponding occurrence
of an append. -/
def appendLeftOccurrenceEmbedding (left right : List G) :
    Occurrence left ↪ Occurrence (left ++ right) where
  toFun i := ⟨i.1, by simp; omega⟩
  inj' := by
    intro i j hij
    exact Fin.ext (by
      simpa using congrArg (fun x => x.val) hij)

@[simp]
theorem occurrenceValue_appendLeftOccurrenceEmbedding
    (left right : List G) (i : Occurrence left) :
    occurrenceValue (left ++ right)
        (appendLeftOccurrenceEmbedding left right i) =
      occurrenceValue left i := by
  simp [occurrenceValue, appendLeftOccurrenceEmbedding,
    List.get_eq_getElem, List.getElem_append_left]

/-- The labelled prefix carrier inside an appended source list. -/
noncomputable def prefixOccurrences (left right : List G) :
    Selection (left ++ right) := by
  classical
  exact Finset.univ.filter fun i => i.1 < left.length

/-- Pull a selected part of the prefix back to the original left list. -/
noncomputable def prefixSelection (left right : List G)
    (I : Selection (left ++ right)) : Selection left := by
  classical
  exact Finset.univ.filter fun i =>
    appendLeftOccurrenceEmbedding left right i ∈ I

theorem map_prefixSelection_eq_inter
    (left right : List G) (I : Selection (left ++ right)) :
    (prefixSelection left right I).map
        (appendLeftOccurrenceEmbedding left right) =
      I ∩ prefixOccurrences left right := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    have hjI : appendLeftOccurrenceEmbedding left right j ∈ I :=
      (Finset.mem_filter.mp hj).2
    refine Finset.mem_inter.mpr ⟨hjI, ?_⟩
    simp [prefixOccurrences, appendLeftOccurrenceEmbedding]
  · intro hi
    have hiI : i ∈ I := (Finset.mem_inter.mp hi).1
    have hlt : i.1 < left.length := by
      simpa [prefixOccurrences] using (Finset.mem_inter.mp hi).2
    let j : Occurrence left := ⟨i.1, hlt⟩
    have hji : appendLeftOccurrenceEmbedding left right j = i := by
      apply Fin.ext
      rfl
    apply Finset.mem_map.mpr
    refine ⟨j, ?_, hji⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hji] using hiI⟩

theorem selectedMultiset_prefixSelection
    (left right : List G) (I : Selection (left ++ right)) :
    selectedMultiset left (prefixSelection left right I) =
      selectedMultiset (left ++ right) (I ∩ prefixOccurrences left right) := by
  classical
  rw [← map_prefixSelection_eq_inter left right I]
  simp [selectedMultiset, occurrenceValue_appendLeftOccurrenceEmbedding]

theorem card_prefixOccurrences (left right : List G) :
    (prefixOccurrences left right).card = left.length := by
  classical
  have hmap := map_prefixSelection_eq_inter left right
    (Finset.univ : Selection (left ++ right))
  have hpull : prefixSelection left right
      (Finset.univ : Selection (left ++ right)) = Finset.univ := by
    ext i
    simp [prefixSelection]
  have hcarrier :
      (Finset.univ : Selection left).map
          (appendLeftOccurrenceEmbedding left right) =
        prefixOccurrences left right := by
    simpa [hpull] using hmap
  rw [← hcarrier, Finset.card_map]
  simp

theorem occurrenceValue_eq_one_of_mem_compl_prefixOccurrences
    [One G] (left : List G) (t : ℕ)
    (i : Occurrence (left ++ List.replicate t (1 : G)))
    (hi : i ∈ (Finset.univ : Selection
      (left ++ List.replicate t (1 : G))) \ prefixOccurrences left
        (List.replicate t (1 : G))) :
    occurrenceValue (left ++ List.replicate t (1 : G)) i = 1 := by
  classical
  have hge : left.length ≤ i.1 := by
    have hnot := (Finset.mem_sdiff.mp hi).2
    simpa [prefixOccurrences, not_lt] using hnot
  simp only [occurrenceValue, List.get_eq_getElem]
  rw [List.getElem_append_right hge]
  simp

end PrefixOccurrences

section PaddedCounterexample

variable {G : Type*} [Group G]

/-- Exact external lower-bound input corresponding to `d(G) ≥ D`: a
labelled product-one-free sequence of length `D`. -/
def SmallDavenportWitness (G : Type*) [Group G] (D : ℕ) : Prop :=
  ∃ w : List G, w.length = D ∧
    IsProductOneFreeSelection w Finset.univ

/-- Padding a product-one-free sequence with fewer than `k` identities cannot
create a `k`-occurrence product-one block. -/
theorem noProductOneBlock_of_identityPadding
    (w : List G) (k t : ℕ)
    (hfree : IsProductOneFreeSelection w Finset.univ) (ht : t < k) :
    ¬HasProductOneSubsequenceOfCard
      (w ++ List.replicate t (1 : G)) k := by
  classical
  intro hblock
  rcases hblock with ⟨I, hIcard, hIprod⟩
  let P : Selection (w ++ List.replicate t (1 : G)) :=
    prefixOccurrences w (List.replicate t (1 : G))
  let J : Selection (w ++ List.replicate t (1 : G)) := I ∩ P
  have hJI : J ⊆ I := Finset.inter_subset_left
  have hcompCard :
      ((Finset.univ : Selection (w ++ List.replicate t (1 : G))) \ P).card =
        t := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P)]
    simp [P, card_prefixOccurrences]
  have hJne : J.Nonempty := by
    by_contra hJempty
    have hJempty' : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJempty
    have hIcomp : I ⊆
        (Finset.univ : Selection (w ++ List.replicate t (1 : G))) \ P := by
      intro i hiI
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, ?_⟩
      intro hiP
      have hiJ : i ∈ J := Finset.mem_inter.mpr ⟨hiI, hiP⟩
      simpa [hJempty'] using hiJ
    have hcardLe := Finset.card_le_card hIcomp
    rw [hcompCard, hIcard] at hcardLe
    omega
  have hdeletedOne : ∀ i ∈ I \ J,
      occurrenceValue (w ++ List.replicate t (1 : G)) i = 1 := by
    intro i hi
    have hiI : i ∈ I := (Finset.mem_sdiff.mp hi).1
    have hiNotJ : i ∉ J := (Finset.mem_sdiff.mp hi).2
    have hiNotP : i ∉ P := by
      intro hiP
      exact hiNotJ (Finset.mem_inter.mpr ⟨hiI, hiP⟩)
    exact occurrenceValue_eq_one_of_mem_compl_prefixOccurrences w t i
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiNotP⟩)
  have hJprod : IsProductOneSelection
      (w ++ List.replicate t (1 : G)) J :=
    hIprod.sdiff_of_all_one hJI hdeletedOne
  let K : Selection w :=
    prefixSelection w (List.replicate t (1 : G)) I
  have hmap : K.map (appendLeftOccurrenceEmbedding w
      (List.replicate t (1 : G))) = J := by
    exact map_prefixSelection_eq_inter w (List.replicate t (1 : G)) I
  have hKne : K.Nonempty := by
    by_contra hKempty
    have hKempty' : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hKempty
    have : J = ∅ := by simpa [hKempty'] using hmap.symm
    rcases hJne with ⟨j, hj⟩
    rw [this] at hj
    simpa using hj
  have hKprod : IsProductOneSelection w K := by
    have hselected : selectedMultiset w K =
        selectedMultiset (w ++ List.replicate t (1 : G)) J := by
      simpa [K, J, P] using selectedMultiset_prefixSelection w
        (List.replicate t (1 : G)) I
    change HasProductOneOrdering (selectedMultiset w K)
    rw [hselected]
    exact hJprod
  exact hfree K (Finset.subset_univ K) hKne hKprod

end PaddedCounterexample

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Explicit lower-threshold family in the frozen `PGGaoV1` statement. -/
def PGGaoThresholdCounterexamples (A : Type*) [AddCommGroup A] [Fintype A]
    (D : ℕ) : Prop :=
  ∀ n : ℕ, n < 2 * Nat.card A + D →
    ∃ s : List (Group A), s.length = n ∧
      ¬HasProductOneSubsequenceOfCard s (2 * Nat.card A)

/-- The A-R6 identity-padding construction supplies every counterexample
below the proposed threshold from a single exact small-Davenport witness. -/
theorem pgGaoThresholdCounterexamples_of_smallDavenportWitness
    (D : ℕ) (hDQ : D ≤ Nat.card A)
    (hwitness : SmallDavenportWitness (Group A) D) :
    PGGaoThresholdCounterexamples A D := by
  intro n hn
  by_cases hnsmall : n < 2 * Nat.card A
  · refine ⟨List.replicate n (1 : Group A), by simp, ?_⟩
    intro hblock
    rcases hblock with ⟨I, hIcard, _⟩
    have hcardLe : I.card ≤ n := by
      calc
        I.card ≤ (Finset.univ : Selection
            (List.replicate n (1 : Group A))).card :=
          Finset.card_le_card (Finset.subset_univ I)
        _ = n := by simp
    omega
  · have hnlarge : 2 * Nat.card A ≤ n := Nat.le_of_not_gt hnsmall
    have hDn : D ≤ n := by omega
    obtain ⟨w, hwlen, hfree⟩ := hwitness
    refine ⟨w ++ List.replicate (n - D) (1 : Group A), ?_, ?_⟩
    · simp [hwlen]
      omega
    · apply noProductOneBlock_of_identityPadding w
        (2 * Nat.card A) (n - D) hfree
      omega

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.selectedMultiset_filter_value
#print axioms GaoLean.IsProductOneSelection.filter_ne_one
#print axioms GaoLean.IsProductOneSelection.sdiff_of_all_one
#print axioms GaoLean.map_prefixSelection_eq_inter
#print axioms GaoLean.selectedMultiset_prefixSelection
#print axioms GaoLean.card_prefixOccurrences
#print axioms GaoLean.noProductOneBlock_of_identityPadding
#print axioms GaoLean.ConcreteGDihedral.pgGaoThresholdCounterexamples_of_smallDavenportWitness
