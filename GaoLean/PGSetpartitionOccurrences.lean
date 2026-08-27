import GaoLean.PGDGMCore

/-!
# Occurrence-faithful finite setpartitions

The classical setpartition criterion says that a sequence admits an
`n`-setpartition exactly when its maximum value multiplicity is at most `n`
and `n` is at most the sequence length.  This file proves the existence
direction directly for labelled occurrences.

The proof first colors equal-valued occurrences differently using their rank
inside the value fiber.  Such a proper coloring can have empty colors.  Among
all proper colorings, choose one with maximal image.  If a color were missing,
the length bound would force two occurrences to share another color; moving
one of them to the missing color preserves properness and enlarges the image,
a contradiction.  Fibers of the resulting surjective coloring are the cells.
-/

namespace GaoLean

variable {A : Type*}

/-- All labelled occurrences of `xs` carrying the value `a`. -/
noncomputable def occurrenceFiber (xs : List A) (a : A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i ↦ occurrenceValue xs i = a

/-- Occurrences in the same value fiber that precede `i` in the source list. -/
noncomputable def occurrencesBeforeInFiber
    (xs : List A) (i : Occurrence xs) : Selection xs := by
  classical
  exact Finset.univ.filter fun j ↦
    occurrenceValue xs j = occurrenceValue xs i ∧ j.1 < i.1

/-- Occurrence multiplicity is bounded by `n`, with repetitions counted by
source position. -/
def OccurrenceMultiplicityAtMost (xs : List A) (n : ℕ) : Prop :=
  ∀ a : A, (occurrenceFiber xs a).card ≤ n

theorem occurrencesBeforeInFiber_ssubset_occurrenceFiber
    (xs : List A) (i : Occurrence xs) :
    occurrencesBeforeInFiber xs i ⊂
      occurrenceFiber xs (occurrenceValue xs i) := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro j hj
    simp only [occurrencesBeforeInFiber, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    simp only [occurrenceFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj.1
  · intro heq
    have hiFiber : i ∈ occurrenceFiber xs (occurrenceValue xs i) := by
      simp [occurrenceFiber]
    have hiBefore : i ∉ occurrencesBeforeInFiber xs i := by
      simp [occurrencesBeforeInFiber]
    apply hiBefore
    rw [heq]
    exact hiFiber

theorem card_occurrencesBeforeInFiber_lt_multiplicity
    (xs : List A) (i : Occurrence xs) :
    (occurrencesBeforeInFiber xs i).card <
      (occurrenceFiber xs (occurrenceValue xs i)).card :=
  Finset.card_lt_card
    (occurrencesBeforeInFiber_ssubset_occurrenceFiber xs i)

theorem occurrencesBeforeInFiber_ssubset_of_sameValue_of_lt
    (xs : List A) (i j : Occurrence xs)
    (hvalue : occurrenceValue xs i = occurrenceValue xs j)
    (hij : i.1 < j.1) :
    occurrencesBeforeInFiber xs i ⊂ occurrencesBeforeInFiber xs j := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro k hk
    simp only [occurrencesBeforeInFiber, Finset.mem_filter,
      Finset.mem_univ, true_and] at hk ⊢
    exact ⟨hk.1.trans hvalue, hk.2.trans hij⟩
  · intro heq
    have hii : i ∉ occurrencesBeforeInFiber xs i := by
      simp [occurrencesBeforeInFiber]
    have hijmem : i ∈ occurrencesBeforeInFiber xs j := by
      simp only [occurrencesBeforeInFiber, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨hvalue, ?_⟩
      exact hij
    apply hii
    rw [heq]
    exact hijmem

/-- Ranks inside one value fiber distinguish its labelled occurrences. -/
theorem card_occurrencesBeforeInFiber_injective_on_value
    (xs : List A) (i j : Occurrence xs)
    (hvalue : occurrenceValue xs i = occurrenceValue xs j)
    (hrank : (occurrencesBeforeInFiber xs i).card =
      (occurrencesBeforeInFiber xs j).card) :
    i = j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hlt := Finset.card_lt_card
      (occurrencesBeforeInFiber_ssubset_of_sameValue_of_lt
        xs i j hvalue hij)
    omega
  · have hlt := Finset.card_lt_card
      (occurrencesBeforeInFiber_ssubset_of_sameValue_of_lt
        xs j i hvalue.symm hji)
    omega

/-- The rank of an occurrence in its value fiber, viewed as a color in
`Fin n`.  The multiplicity cap proves that the color is in range. -/
noncomputable def occurrenceRankColor
    (xs : List A) (n : ℕ) (hcap : OccurrenceMultiplicityAtMost xs n) :
    Occurrence xs → Fin n := fun i ↦
  ⟨(occurrencesBeforeInFiber xs i).card,
    (card_occurrencesBeforeInFiber_lt_multiplicity xs i).trans_le
      (hcap (occurrenceValue xs i))⟩

/-- A coloring is proper when equal-valued occurrences receive distinct
colors. -/
def OccurrenceColoringProper
    (xs : List A) (n : ℕ) (f : Occurrence xs → Fin n) : Prop :=
  ∀ i j, occurrenceValue xs i = occurrenceValue xs j →
    f i = f j → i = j

theorem occurrenceRankColor_proper
    (xs : List A) (n : ℕ) (hcap : OccurrenceMultiplicityAtMost xs n) :
    OccurrenceColoringProper xs n (occurrenceRankColor xs n hcap) := by
  intro i j hvalue hcolor
  apply card_occurrencesBeforeInFiber_injective_on_value xs i j hvalue
  exact congrArg Fin.val hcolor

/-- A proper occurrence coloring can be made surjective whenever there are at
least as many occurrences as colors.  Maximal-image recoloring is used so the
argument does not assume any ordering on the value type. -/
theorem exists_surjective_proper_occurrenceColoring
    (xs : List A) (n : ℕ)
    (hcap : OccurrenceMultiplicityAtMost xs n)
    (hlen : n ≤ xs.length) :
    ∃ f : Occurrence xs → Fin n,
      Function.Surjective f ∧ OccurrenceColoringProper xs n f := by
  classical
  let f₀ : Occurrence xs → Fin n := occurrenceRankColor xs n hcap
  let good : Finset (Occurrence xs → Fin n) :=
    Finset.univ.filter fun f ↦ OccurrenceColoringProper xs n f
  have hf₀ : f₀ ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact occurrenceRankColor_proper xs n hcap
  obtain ⟨f, hfGood, hmax⟩ := Finset.exists_max_image good
    (fun f ↦ (Finset.univ.image f).card) ⟨f₀, hf₀⟩
  have hfProper : OccurrenceColoringProper xs n f := by
    exact (Finset.mem_filter.mp hfGood).2
  refine ⟨f, ?_, hfProper⟩
  by_contra hnotSurj
  obtain ⟨c, hc⟩ : ∃ c : Fin n, ∀ i : Occurrence xs, f i ≠ c := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnotSurj
  have hnotInj : ¬ Function.Injective f := by
    intro hinj
    have hlt := Fintype.card_lt_of_injective_not_surjective f hinj hnotSurj
    simp only [Fintype.card_fin] at hlt
    omega
  obtain ⟨i, j, hfij, hij⟩ := Function.not_injective_iff.mp hnotInj
  let g : Occurrence xs → Fin n := Function.update f i c
  have hgProper : OccurrenceColoringProper xs n g := by
    intro a b hvalue hgab
    by_cases hai : a = i
    · subst a
      by_cases hbi : b = i
      · exact hbi.symm
      · exfalso
        have hcb : c = f b := by
          simpa [g, hbi] using hgab
        exact hc b hcb.symm
    · by_cases hbi : b = i
      · subst b
        exfalso
        have hac : f a = c := by
          simpa [g, hai] using hgab
        exact hc a hac
      · apply hfProper a b hvalue
        simpa [g, hai, hbi] using hgab
  have hgGood : g ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hgProper
  have hrangeSubset : Finset.univ.image f ⊆ Finset.univ.image g := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, -, rfl⟩
    by_cases hxi : x = i
    · subst x
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      simp [g, hij.symm, hfij]
    · refine Finset.mem_image.mpr ⟨x, Finset.mem_univ _, ?_⟩
      simp [g, hxi]
  have hcRangeG : c ∈ Finset.univ.image g := by
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    simp [g]
  have hcRangeF : c ∉ Finset.univ.image f := by
    intro hcF
    rcases Finset.mem_image.mp hcF with ⟨x, -, hfx⟩
    exact hc x hfx
  have hrangeStrict : Finset.univ.image f ⊂ Finset.univ.image g := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hrangeSubset, ?_⟩
    intro heq
    exact hcRangeF (heq ▸ hcRangeG)
  have hcardLt : (Finset.univ.image f).card <
      (Finset.univ.image g).card := Finset.card_lt_card hrangeStrict
  have hcardMax := hmax g hgGood
  omega

/-- An indexed occurrence setpartition.  `unique_cell` simultaneously records
coverage and pairwise disjointness.  The last field says equal values never
occur twice in one cell. -/
structure OccurrenceSetPartition (xs : List A) (n : ℕ) where
  cells : Fin n → Selection xs
  cells_nonempty : ∀ c, (cells c).Nonempty
  unique_cell : ∀ i : Occurrence xs, ∃! c, i ∈ cells c
  value_injective : ∀ c,
    Set.InjOn (occurrenceValue xs) (cells c : Set (Occurrence xs))

/-- The full occurrence-faithful `n`-setpartition existence criterion. -/
theorem exists_occurrenceSetPartition
    (xs : List A) (n : ℕ)
    (hcap : OccurrenceMultiplicityAtMost xs n)
    (hlen : n ≤ xs.length) :
    Nonempty (OccurrenceSetPartition xs n) := by
  classical
  obtain ⟨f, hsurj, hproper⟩ :=
    exists_surjective_proper_occurrenceColoring xs n hcap hlen
  let cells : Fin n → Selection xs := fun c ↦
    Finset.univ.filter fun i ↦ f i = c
  refine ⟨{
    cells := cells
    cells_nonempty := ?_
    unique_cell := ?_
    value_injective := ?_
  }⟩
  · intro c
    obtain ⟨i, hi⟩ := hsurj c
    exact ⟨i, by simp [cells, hi]⟩
  · intro i
    refine ⟨f i, by simp [cells], ?_⟩
    intro c hc
    exact (show f i = c from by simpa [cells] using hc).symm
  · intro c i hi j hj hvalue
    apply hproper i j hvalue
    simpa [cells] using (show f i = c from by simpa [cells] using hi).trans
      (show f j = c from by simpa [cells] using hj).symm

theorem OccurrenceSetPartition.cells_pairwise_disjoint
    (P : OccurrenceSetPartition xs n) {c d : Fin n} (hcd : c ≠ d) :
    Disjoint (P.cells c) (P.cells d) := by
  classical
  rw [Finset.disjoint_left]
  intro i hic hid
  obtain ⟨e, -, he⟩ := P.unique_cell i
  exact hcd ((he c hic).trans (he d hid).symm)

theorem OccurrenceSetPartition.biUnion_cells
    (P : OccurrenceSetPartition xs n) :
    Finset.univ.biUnion P.cells = (Finset.univ : Selection xs) := by
  classical
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  obtain ⟨c, hc, -⟩ := P.unique_cell i
  exact ⟨c, hc⟩

/-- The value image of one cell. -/
def OccurrenceSetPartition.valueCell
    [DecidableEq A] {xs : List A} {n : ℕ}
    (P : OccurrenceSetPartition xs n) (c : Fin n) : Finset A :=
  (P.cells c).image (occurrenceValue xs : Occurrence xs → A)

/-- No cardinality is lost when a cell is converted from labelled
occurrences to its finite value set. -/
theorem OccurrenceSetPartition.card_valueCell
    [DecidableEq A] {xs : List A} {n : ℕ}
    (P : OccurrenceSetPartition xs n) (c : Fin n) :
    (P.valueCell c).card = (P.cells c).card := by
  classical
  exact Finset.card_image_iff.mpr (P.value_injective c)

section AdditiveBridge

variable [AddCommGroup A] [DecidableEq A]

/-- Arrange the value images of the indexed occurrence cells as the literal
list of finite layers consumed by `PGDGMCore`. -/
noncomputable def OccurrenceSetPartition.valueCells
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n) :
    List (Finset A) := by
  classical
  exact List.ofFn fun c : Fin n ↦ P.valueCell c

omit [AddCommGroup A] in
@[simp]
theorem OccurrenceSetPartition.length_valueCells
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n) :
    P.valueCells.length = n := by
  classical
  simp [OccurrenceSetPartition.valueCells]

omit [AddCommGroup A] in
theorem OccurrenceSetPartition.valueCells_nonempty
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n) :
    IsNonemptySetPartition P.valueCells := by
  classical
  intro B hB
  simp only [OccurrenceSetPartition.valueCells, List.mem_ofFn] at hB
  obtain ⟨c, rfl⟩ := hB
  obtain ⟨i, hi⟩ := P.cells_nonempty c
  refine ⟨occurrenceValue xs i, ?_⟩
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Membership in a full-layer sumset is equivalent to choosing one value
from every indexed layer.  This exposes the individual choices needed to
recover labelled source occurrences. -/
theorem mem_fullLayerSumSpectrum_iff_exists_choice
    (L : List (Finset A)) (y : A) :
    y ∈ fullLayerSumSpectrum L ↔
      ∃ a : Fin L.length → A,
        (∀ i, a i ∈ L.get i) ∧ (∑ i, a i) = y := by
  classical
  induction L generalizing y with
  | nil =>
      simp only [fullLayerSumSpectrum_nil, Finset.mem_singleton,
        List.length_nil]
      constructor
      · intro hy
        subst y
        refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · simp
      · rintro ⟨a, -, hsum⟩
        simpa using hsum.symm
  | cons B L ih =>
      rw [fullLayerSumSpectrum_cons, Finset.mem_add]
      constructor
      · rintro ⟨b, hb, z, hz, hsum⟩
        obtain ⟨a, ha, haz⟩ := (ih z).1 hz
        refine ⟨Fin.cons b a, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simpa using hb
          · simpa using ha j
        · calc
            (∑ i, Fin.cons b a i) = b + ∑ i, a i := by
              simp [Fin.sum_univ_succ]
            _ = y := by simpa [haz] using hsum
      · rintro ⟨a, ha, hay⟩
        let tail : Fin L.length → A := fun i ↦ a i.succ
        have htail : ∀ i, tail i ∈ L.get i := by
          intro i
          simpa [tail] using ha i.succ
        have hz : (∑ i, tail i) ∈ fullLayerSumSpectrum L :=
          (ih _).2 ⟨tail, htail, rfl⟩
        refine ⟨a 0, ?_, ∑ i, tail i, hz, ?_⟩
        · simpa using ha 0
        · rw [← hay]
          simpa [tail] using (Fin.sum_univ_succ a).symm

/-- Every choice of one value from each value-cell lifts to one *distinct
labelled occurrence* from each original cell.  Consequently the DGM
full-layer spectrum is contained in the exact occurrence spectrum of the
source list. -/
theorem OccurrenceSetPartition.fullLayerSumSpectrum_valueCells_subset
    [Fintype A] {xs : List A} {n : ℕ}
    (P : OccurrenceSetPartition xs n) :
    fullLayerSumSpectrum P.valueCells ⊆ ordinaryExactSpectrum xs n := by
  classical
  intro y hy
  rw [mem_fullLayerSumSpectrum_iff_exists_choice] at hy
  obtain ⟨a, ha, hsum⟩ := hy
  let e : Fin n ≃ Fin P.valueCells.length :=
    finCongr P.length_valueCells.symm
  let a' : Fin n → A := fun c ↦ a (e c)
  have ha' : ∀ c : Fin n, a' c ∈ P.valueCell c := by
    intro c
    have hc := ha (e c)
    simp only [OccurrenceSetPartition.valueCells, List.get_ofFn] at hc
    dsimp only [a']
    convert hc using 1
    · congr 1
    · rfl
  have hsum' : (∑ c, a' c) = y := by
    exact (e.sum_comp a).trans hsum
  have hpick : ∀ c : Fin n, ∃ i : Occurrence xs,
      i ∈ P.cells c ∧ occurrenceValue xs i = a' c := by
    intro c
    simpa [OccurrenceSetPartition.valueCell] using ha' c
  let pick : Fin n → Occurrence xs := fun c ↦ Classical.choose (hpick c)
  have pick_mem (c : Fin n) : pick c ∈ P.cells c :=
    (Classical.choose_spec (hpick c)).1
  have pick_value (c : Fin n) : occurrenceValue xs (pick c) = a' c :=
    (Classical.choose_spec (hpick c)).2
  have pick_injective : Function.Injective pick := by
    intro c d hcd
    obtain ⟨e, -, he⟩ := P.unique_cell (pick c)
    have hmemd : pick c ∈ P.cells d := by
      rw [hcd]
      exact pick_mem d
    exact (he c (pick_mem c)).trans (he d hmemd).symm
  let I : Selection xs := Finset.univ.image pick
  apply (mem_ordinaryExactSpectrum_iff xs n y).2
  refine ⟨I, ?_, ?_⟩
  · simp [I, Finset.card_image_of_injective, pick_injective]
  · unfold I
    rw [Finset.sum_image]
    · simp only [pick_value]
      simpa using hsum'
    · intro c _ d _ hcd
      exact pick_injective hcd

section QuotientIncidence

variable [Fintype A]

/-- Occurrences from one cell lying in one quotient coset. -/
noncomputable def OccurrenceSetPartition.cellQuotientOccurrenceCount
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n)
    (K : AddSubgroup A) [Fintype (A ⧸ K)] (c : Fin n) (q : A ⧸ K) : ℕ := by
  classical
  exact ((P.cells c).filter fun i ↦
    QuotientAddGroup.mk' K (occurrenceValue xs i) = q).card

omit [DecidableEq A] in
/-- Summing occurrence incidences in a fixed quotient coset over all cells
recovers the source occurrence multiplicity of that coset.  This counts
labelled occurrences, unlike `quotientLayerMultiplicity`, which counts a
layer at most once. -/
theorem OccurrenceSetPartition.sum_cell_quotientOccurrenceCount
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n)
    (K : AddSubgroup A) [Fintype (A ⧸ K)] (q : A ⧸ K) :
    (∑ c : Fin n, P.cellQuotientOccurrenceCount K c q) =
      occurrenceQuotientMultiplicity xs K q := by
  classical
  let C : Fin n → Selection xs := fun c ↦
    (P.cells c).filter fun i ↦
      QuotientAddGroup.mk' K (occurrenceValue xs i) = q
  change (∑ c : Fin n, (C c).card) =
    occurrenceQuotientMultiplicity xs K q
  have hdisjoint : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint C := by
    intro c _ d _ hcd
    exact (P.cells_pairwise_disjoint hcd).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hunion : Finset.univ.biUnion C =
      (Finset.univ : Selection xs).filter (fun i ↦
        QuotientAddGroup.mk' K (occurrenceValue xs i) = q) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨c, -, hic⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hic).2⟩
    · intro hi
      obtain ⟨c, hic, -⟩ := P.unique_cell i
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hic, (Finset.mem_filter.mp hi).2⟩⟩
  rw [← Finset.card_biUnion hdisjoint, hunion]
  rfl

/-- Representative form of the same identity, aligned with the canonical
coset selection used by the ordinary GMO concentration interface. -/
theorem OccurrenceSetPartition.sum_cell_cosetCount_eq_occurrencesInAddCoset
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n)
    (K : AddSubgroup A) [Fintype (A ⧸ K)] (alpha : A) :
    (∑ c : Fin n, P.cellQuotientOccurrenceCount K c
        (QuotientAddGroup.mk' K alpha)) =
      (occurrencesInAddCoset xs K alpha).card := by
  rw [P.sum_cell_quotientOccurrenceCount K (QuotientAddGroup.mk' K alpha),
    occurrenceQuotientMultiplicity_mk_eq_card_occurrencesInAddCoset]

end QuotientIncidence
end AdditiveBridge

end GaoLean

#print axioms GaoLean.exists_surjective_proper_occurrenceColoring
#print axioms GaoLean.exists_occurrenceSetPartition
#print axioms GaoLean.OccurrenceSetPartition.cells_pairwise_disjoint
#print axioms GaoLean.OccurrenceSetPartition.biUnion_cells
#print axioms GaoLean.OccurrenceSetPartition.card_valueCell
#print axioms GaoLean.mem_fullLayerSumSpectrum_iff_exists_choice
#print axioms GaoLean.OccurrenceSetPartition.fullLayerSumSpectrum_valueCells_subset
#print axioms GaoLean.OccurrenceSetPartition.sum_cell_quotientOccurrenceCount
