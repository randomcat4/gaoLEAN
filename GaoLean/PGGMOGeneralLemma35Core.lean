import GaoLean.PGDGMCore
import GaoLean.PGCapacity

/-!
# General labelled setpartition core for GMO Lemma 3.5

This file contains the weight-independent bookkeeping used before the
special form of the cells is exploited in GMO Lemma 3.5.  The finite type
`ι` labels occurrences.  Consequently two equal cells at different labels
are never identified.

For a selected labelled carrier `s`, we record its full selected-cell
sumset, its stabilizer, the quotient excess of every cell, and the labels
whose cells become singletons modulo a subgroup.  The main result is the
complete labelled form of GMO Lemma 3.5.  Its proof combines the exact
DGM/Kneser inequality, a deletion-minimal greedy full-cardinality leaf, and
strong induction on the order of the source subgroup.  The proper branch
translates the retained cells independently and transports the recursive
certificate back without identifying equal cell occurrences.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {A : Type u} [AddCommGroup A] [Fintype A]
variable {ι : Type v} [Fintype ι]

noncomputable local instance generalLemma35DecidableEq {α : Type*} :
    DecidableEq α := Classical.decEq α

noncomputable local instance generalLemma35PropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

/-! ## Labelled cells and selected-cell sumsets -/

/-- The list of cells on a literal finite set of occurrence labels.  The
arbitrary `Finset.toList` order does not merge equal cells. -/
noncomputable def indexedCellsOn
    (cells : ι → Finset A) (s : Finset ι) : List (Finset A) := by
  classical
  exact s.toList.map cells

@[simp]
theorem length_indexedCellsOn
    (cells : ι → Finset A) (s : Finset ι) :
    (indexedCellsOn cells s).length = s.card := by
  classical
  simp [indexedCellsOn]

theorem indexedCellsOn_nonempty
    (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty) :
    IsNonemptySetPartition (indexedCellsOn cells s) := by
  classical
  intro B hB
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
  exact hcells i (Finset.mem_toList.mp hi)

/-- The full sumset obtained by choosing one element from every cell whose
label lies in `s`. -/
noncomputable def selectedCellSumset
    (cells : ι → Finset A) (s : Finset ι) : Finset A :=
  fullLayerSumSpectrum (indexedCellsOn cells s)

theorem selectedCellSumset_nonempty
    (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty) :
    (selectedCellSumset cells s).Nonempty := by
  unfold selectedCellSumset
  exact layerSubsumSpectrum_nonempty
    (indexedCellsOn cells s)
    (indexedCellsOn_nonempty cells s hcells)
    (indexedCellsOn cells s).length le_rfl

/-- The canonical stabilizer of the selected-cell sumset. -/
noncomputable def selectedCellStabilizer
    (cells : ι → Finset A) (s : Finset ι) : AddSubgroup A :=
  AddAction.stabilizer A (selectedCellSumset cells s : Set A)

/-! ## Quotient excess and retained singleton labels -/

/-- The excess number of quotient classes contributed by one cell, beyond
the one class forced by nonemptiness. -/
noncomputable def cellQuotientExcess
    (H : AddSubgroup A) (cells : ι → Finset A) (i : ι) : ℕ :=
  (quotientLayer H (cells i)).card - 1

/-- Total quotient excess on a literal selected carrier. -/
noncomputable def quotientExcessOn
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) : ℕ :=
  ∑ i ∈ s, cellQuotientExcess H cells i

/-- Selected labels whose cells lie in a single coset of `H`. -/
noncomputable def singletonModIndicesOn
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) : Finset ι := by
  classical
  exact s.filter fun i ↦ (quotientLayer H (cells i)).card = 1

/-- Selected labels omitted because their cells meet at least two `H`-cosets.
-/
noncomputable def nonsingletonModIndicesOn
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) : Finset ι :=
  s \ singletonModIndicesOn H cells s

@[simp]
theorem mem_singletonModIndicesOn_iff
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) (i : ι) :
    i ∈ singletonModIndicesOn H cells s ↔
      i ∈ s ∧ (quotientLayer H (cells i)).card = 1 := by
  classical
  simp [singletonModIndicesOn]

@[simp]
theorem mem_nonsingletonModIndicesOn_iff
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) (i : ι) :
    i ∈ nonsingletonModIndicesOn H cells s ↔
      i ∈ s ∧ (quotientLayer H (cells i)).card ≠ 1 := by
  classical
  constructor
  · intro hi
    have hdiff := Finset.mem_sdiff.mp hi
    refine ⟨hdiff.1, ?_⟩
    intro hcard
    exact hdiff.2 ((mem_singletonModIndicesOn_iff H cells s i).2
      ⟨hdiff.1, hcard⟩)
  · rintro ⟨his, hcard⟩
    exact Finset.mem_sdiff.mpr ⟨his, fun hret ↦
      hcard ((mem_singletonModIndicesOn_iff H cells s i).1 hret).2⟩

theorem singletonModIndicesOn_disjoint_nonsingleton
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) :
    Disjoint (singletonModIndicesOn H cells s)
      (nonsingletonModIndicesOn H cells s) := by
  classical
  exact Finset.disjoint_sdiff

theorem singletonModIndicesOn_union_nonsingleton
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) :
    singletonModIndicesOn H cells s ∪
        nonsingletonModIndicesOn H cells s = s := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

theorem card_singletonModIndicesOn_add_nonsingleton
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) :
    (singletonModIndicesOn H cells s).card +
        (nonsingletonModIndicesOn H cells s).card = s.card := by
  classical
  have h := Finset.card_union_of_disjoint
    (singletonModIndicesOn_disjoint_nonsingleton H cells s)
  rw [singletonModIndicesOn_union_nonsingleton H cells s] at h
  exact h.symm

/-- A nonempty cell omitted from the singleton-mod-`H` carrier contributes
at least one unit of quotient excess. -/
theorem one_le_cellQuotientExcess_of_nonsingleton
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty)
    {i : ι} (hi : i ∈ nonsingletonModIndicesOn H cells s) :
    1 ≤ cellQuotientExcess H cells i := by
  have his : i ∈ s := (mem_nonsingletonModIndicesOn_iff H cells s i).1 hi |>.1
  have hne : (quotientLayer H (cells i)).card ≠ 1 :=
    (mem_nonsingletonModIndicesOn_iff H cells s i).1 hi |>.2
  have hpos : 0 < (quotientLayer H (cells i)).card :=
    Finset.card_pos.mpr (quotientLayer_nonempty H (cells i) (hcells i his))
  unfold cellQuotientExcess
  omega

/-- The number of selected labels which fail to be singleton modulo `H` is
bounded by the total quotient excess.  This is the omission ledger used in
Lemma 3.5 and counts labels, not distinct cell values. -/
theorem card_nonsingletonModIndicesOn_le_quotientExcessOn
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty) :
    (nonsingletonModIndicesOn H cells s).card ≤
      quotientExcessOn H cells s := by
  classical
  rw [Finset.card_eq_sum_ones]
  unfold quotientExcessOn
  calc
    (∑ _i ∈ nonsingletonModIndicesOn H cells s, 1) ≤
        ∑ i ∈ nonsingletonModIndicesOn H cells s,
          cellQuotientExcess H cells i := by
            apply Finset.sum_le_sum
            intro i hi
            exact one_le_cellQuotientExcess_of_nonsingleton
              H cells s hcells hi
    _ ≤ ∑ i ∈ s, cellQuotientExcess H cells i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (show nonsingletonModIndicesOn H cells s ⊆ s from
          Finset.sdiff_subset)
      intro i _hi _hnot
      exact Nat.zero_le _

/-! ## Singleton quotient fibers are honest subgroup cosets -/

/-- A nonempty cell has singleton quotient image exactly in the direction
needed later: one chosen element is a center and every element of the cell
differs from it by an element of `H`. -/
theorem exists_cell_center_of_quotientLayer_card_eq_one
    (H : AddSubgroup A) (B : Finset A) (hB : B.Nonempty)
    (hcard : (quotientLayer H B).card = 1) :
    ∃ a ∈ B, ∀ x ∈ B, x - a ∈ H := by
  obtain ⟨a, ha⟩ := hB
  refine ⟨a, ha, ?_⟩
  intro x hx
  have hqa : (a : A ⧸ H) ∈ quotientLayer H B :=
    (mem_quotientLayer_iff H B _).2 ⟨a, ha, rfl⟩
  have hqx : (x : A ⧸ H) ∈ quotientLayer H B :=
    (mem_quotientLayer_iff H B _).2 ⟨x, hx, rfl⟩
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  rw [hq] at hqa hqx
  have hqa' : (a : A ⧸ H) = q := Finset.mem_singleton.mp hqa
  have hqx' : (x : A ⧸ H) = q := Finset.mem_singleton.mp hqx
  have hxa : (x : A ⧸ H) = (a : A ⧸ H) := hqx'.trans hqa'.symm
  exact QuotientAddGroup.eq_iff_sub_mem.mp hxa

theorem exists_cell_center_of_mem_singletonModIndicesOn
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty)
    {i : ι} (hi : i ∈ singletonModIndicesOn H cells s) :
    ∃ a ∈ cells i, ∀ x ∈ cells i, x - a ∈ H := by
  have h := (mem_singletonModIndicesOn_iff H cells s i).1 hi
  exact exists_cell_center_of_quotientLayer_card_eq_one
    H (cells i) (hcells i h.1) h.2

/-! ## Exact incidence and DGM/Kneser glue -/

omit [AddCommGroup A] [Fintype A] in
theorem sum_map_finset_toList_nat_general
    (s : Finset ι) (f : ι → ℕ) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem sum_card_quotientLayer_indexedCellsOn
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι) :
    ((indexedCellsOn cells s).map fun B ↦ (quotientLayer H B).card).sum =
      ∑ i ∈ s, (quotientLayer H (cells i)).card := by
  classical
  unfold indexedCellsOn
  simp only [List.map_map]
  exact sum_map_finset_toList_nat_general s fun i ↦
    (quotientLayer H (cells i)).card

/-- The specialized stabilizer projection is definitionally the ordinary
quotient-layer projection by the stabilizer of the same finite set. -/
theorem stabilizerQuotientLayer_eq_quotientLayer
    (T B : Finset A) :
    stabilizerQuotientLayer T B =
      quotientLayer (AddAction.stabilizer A (T : Set A)) B := by
  classical
  ext q
  simp [stabilizerQuotientLayer, quotientLayer]

/-- Exact quotient incidence identity.  It is stated with addition to avoid
truncated-subtraction ambiguity. -/
theorem sum_card_quotientLayer_eq_card_add_excess
    (H : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty) :
    (∑ i ∈ s, (quotientLayer H (cells i)).card) =
      s.card + quotientExcessOn H cells s := by
  classical
  unfold quotientExcessOn cellQuotientExcess
  calc
    (∑ i ∈ s, (quotientLayer H (cells i)).card) =
        ∑ i ∈ s, (1 + ((quotientLayer H (cells i)).card - 1)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hpos : 0 < (quotientLayer H (cells i)).card :=
            Finset.card_pos.mpr
              (quotientLayer_nonempty H (cells i) (hcells i hi))
          omega
    _ = (∑ _i ∈ s, 1) +
          ∑ i ∈ s, ((quotientLayer H (cells i)).card - 1) := by
            rw [Finset.sum_add_distrib]
    _ = s.card + ∑ i ∈ s,
          ((quotientLayer H (cells i)).card - 1) := by simp

/-- The full-layer DGM/Kneser theorem rewritten as a quotient-excess bound
for labelled selected cells and their canonical stabilizer. -/
theorem selectedCellSumset_dgm_excess_bound
    (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty) :
    (quotientExcessOn (selectedCellStabilizer cells s) cells s + 1) *
        (selectedCellSumset cells s).addStab.card ≤
      (selectedCellSumset cells s).card := by
  classical
  unfold selectedCellStabilizer selectedCellSumset
  have hdgm := fullLayer_dgm_lower_bound (indexedCellsOn cells s)
    (indexedCellsOn_nonempty cells s hcells)
  have hincidence :
      ((indexedCellsOn cells s).map fun B ↦
          (stabilizerQuotientLayer
            (fullLayerSumSpectrum (indexedCellsOn cells s)) B).card).sum =
        s.card + quotientExcessOn
          (AddAction.stabilizer A
            (fullLayerSumSpectrum (indexedCellsOn cells s) : Set A)) cells s := by
    rw [show (fun B : Finset A ↦
        (stabilizerQuotientLayer
          (fullLayerSumSpectrum (indexedCellsOn cells s)) B).card) =
        (fun B : Finset A ↦
          (quotientLayer (AddAction.stabilizer A
            (fullLayerSumSpectrum (indexedCellsOn cells s) : Set A)) B).card) by
      funext B
      exact congrArg Finset.card
        (stabilizerQuotientLayer_eq_quotientLayer
          (fullLayerSumSpectrum (indexedCellsOn cells s)) B)]
    rw [sum_card_quotientLayer_indexedCellsOn]
    exact sum_card_quotientLayer_eq_card_add_excess
      (AddAction.stabilizer A
        (fullLayerSumSpectrum (indexedCellsOn cells s) : Set A)) cells s hcells
  rw [length_indexedCellsOn] at hdgm
  rw [hincidence] at hdgm
  simpa using hdgm

/-! ## Commutative carrier sumsets and the general greedy leaf -/

/-- The same labelled full sumset expressed as a commutative `Finset` sum.
This presentation is convenient for carrier insertion, deletion, and union.
-/
noncomputable def commutativeCellSumset
    (cells : ι → Finset A) (s : Finset ι) : Finset A :=
  selectedCellSumset cells s

theorem selectedCellSumset_eq_commutativeCellSumset
    (cells : ι → Finset A) (s : Finset ι) :
    selectedCellSumset cells s = commutativeCellSumset cells s := by
  rfl

theorem iteratedFinsetSum_eq_of_perm_general
    [DecidableEq A] {P Q : List (Finset A)} (hPQ : P.Perm Q) :
    iteratedFinsetSum P = iteratedFinsetSum Q := by
  induction hPQ with
  | nil => rfl
  | cons B _h ih => simp [iteratedFinsetSum, ih]
  | swap B C P => simp [iteratedFinsetSum, add_assoc, add_comm, add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem singleton_zero_add_finset_general
    [DecidableEq A] (S : Finset A) :
    ({0} : Finset A) + S = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, y, hy, hzy⟩ := Finset.mem_add.mp hx
    have hz0 : z = 0 := by simpa using hz
    subst z
    have hyx : y = x := by simpa using hzy
    simpa [hyx] using hy
  · intro hx
    exact Finset.mem_add.mpr ⟨0, by simp, x, hx, by simp⟩

theorem iteratedFinsetSum_append_general
    [DecidableEq A] (P Q : List (Finset A)) :
    iteratedFinsetSum (P ++ Q) =
      iteratedFinsetSum P + iteratedFinsetSum Q := by
  induction P with
  | nil => exact (singleton_zero_add_finset_general _).symm
  | cons B P ih =>
      simp [iteratedFinsetSum, ih, add_assoc]

@[simp]
theorem commutativeCellSumset_empty (cells : ι → Finset A) :
    commutativeCellSumset cells ∅ = {0} := by
  classical
  simpa [← selectedCellSumset_eq_commutativeCellSumset,
    selectedCellSumset, indexedCellsOn]

theorem commutativeCellSumset_insert
    (cells : ι → Finset A) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    commutativeCellSumset cells (insert i s) =
      cells i + commutativeCellSumset cells s := by
  classical
  unfold commutativeCellSumset selectedCellSumset indexedCellsOn
  rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
    fullLayerSumSpectrum_eq_iteratedFinsetSum]
  calc
    iteratedFinsetSum (List.map cells (insert i s).toList) =
        iteratedFinsetSum (cells i :: List.map cells s.toList) :=
      iteratedFinsetSum_eq_of_perm_general ((Finset.toList_insert hi).map cells)
    _ = cells i + iteratedFinsetSum (List.map cells s.toList) := rfl

theorem commutativeCellSumset_union_of_disjoint
    (cells : ι → Finset A) {s t : Finset ι} (hst : Disjoint s t) :
    commutativeCellSumset cells (s ∪ t) =
      commutativeCellSumset cells s + commutativeCellSumset cells t := by
  classical
  have hperm : (s ∪ t).toList.Perm (s.toList ++ t.toList) := by
    have hlistDisjoint : List.Disjoint s.toList t.toList := by
      simp only [List.disjoint_left]
      intro i his hit
      exact (Finset.disjoint_left.mp hst)
        (Finset.mem_toList.mp his) (Finset.mem_toList.mp hit)
    have hnodup : (s.toList ++ t.toList).Nodup :=
      (Finset.nodup_toList _).append (Finset.nodup_toList _) hlistDisjoint
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hnodup).2
    intro i
    simp
  unfold commutativeCellSumset selectedCellSumset indexedCellsOn
  rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
    fullLayerSumSpectrum_eq_iteratedFinsetSum,
    fullLayerSumSpectrum_eq_iteratedFinsetSum]
  rw [iteratedFinsetSum_eq_of_perm_general (hperm.map cells),
    List.map_append, iteratedFinsetSum_append_general]

theorem zero_mem_commutativeCellSumset
    (cells : ι → Finset A) (s : Finset ι)
    (hzero : ∀ i ∈ s, 0 ∈ cells i) :
    0 ∈ commutativeCellSumset cells s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [commutativeCellSumset, selectedCellSumset, indexedCellsOn]
  | @insert i s hi ih =>
      rw [commutativeCellSumset_insert cells s i hi]
      exact Finset.mem_add.mpr ⟨0, hzero i (by simp), 0,
        ih (fun j hj ↦ hzero j (by simp [hj])), by simp⟩

/-- If every added cell contains zero, enlarging the labelled carrier
enlarges its full sumset. -/
theorem commutativeCellSumset_mono_of_zero
    (cells : ι → Finset A) {s t : Finset ι} (hst : s ⊆ t)
    (hzero : ∀ i ∈ t, 0 ∈ cells i) :
    commutativeCellSumset cells s ⊆ commutativeCellSumset cells t := by
  classical
  let u := t \ s
  have hdis : Disjoint s u := Finset.disjoint_sdiff
  have hunion : s ∪ u = t := Finset.union_sdiff_of_subset hst
  have hzeroU : ∀ i ∈ u, 0 ∈ cells i := by
    intro i hi
    exact hzero i (Finset.sdiff_subset hi)
  have h0 : 0 ∈ commutativeCellSumset cells u :=
    zero_mem_commutativeCellSumset cells u hzeroU
  intro x hx
  rw [← hunion, commutativeCellSumset_union_of_disjoint cells hdis]
  exact Finset.mem_add.mpr ⟨x, hx, 0, h0, by simp⟩

/-- Redundancy of a zero-containing cell at one prefix propagates through
every disjoint tail. -/
theorem commutativeCellSumset_erase_eq_of_insert_eq
    (cells : ι → Finset A) {M s : Finset ι} {i : ι}
    (hiM : i ∈ M) (hsM : s ⊆ M.erase i)
    (heq : commutativeCellSumset cells (insert i s) =
      commutativeCellSumset cells s) :
    commutativeCellSumset cells (M.erase i) =
      commutativeCellSumset cells M := by
  classical
  let t := M \ insert i s
  have hinsM : insert i s ⊆ M :=
    Finset.insert_subset hiM (hsM.trans (Finset.erase_subset i M))
  have hdisInsert : Disjoint (insert i s) t := by
    exact Finset.disjoint_sdiff
  have hdisS : Disjoint s t :=
    hdisInsert.mono_left (Finset.subset_insert i s)
  have hMpartition : insert i s ∪ t = M :=
    Finset.union_sdiff_of_subset hinsM
  have herasePartition : s ∪ t = M.erase i := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hjs | hjt
      · exact hsM hjs
      · have hjdiff := Finset.mem_sdiff.mp hjt
        exact Finset.mem_erase.mpr
          ⟨fun hji ↦ hjdiff.2 (by subst j; simp), hjdiff.1⟩
    · intro hj
      have hjErase := Finset.mem_erase.mp hj
      by_cases hjs : j ∈ s
      · exact Finset.mem_union_left t hjs
      · apply Finset.mem_union_right s
        exact Finset.mem_sdiff.mpr
          ⟨hjErase.2, by simpa [hjErase.1, hjs]⟩
  calc
    commutativeCellSumset cells (M.erase i) =
        commutativeCellSumset cells (s ∪ t) := by rw [herasePartition]
    _ = commutativeCellSumset cells s +
        commutativeCellSumset cells t :=
      commutativeCellSumset_union_of_disjoint cells hdisS
    _ = commutativeCellSumset cells (insert i s) +
        commutativeCellSumset cells t := by rw [heq]
    _ = commutativeCellSumset cells (insert i s ∪ t) :=
      (commutativeCellSumset_union_of_disjoint cells hdisInsert).symm
    _ = commutativeCellSumset cells M := by rw [hMpartition]

/-- A deletion-minimal zero-containing labelled carrier has at most one
fewer labels than values in its full sumset. -/
theorem card_add_one_le_commutativeCellSumset_card_of_erase_minimal
    (cells : ι → Finset A) (M : Finset ι)
    (hzero : ∀ i ∈ M, 0 ∈ cells i)
    (hminimal : ∀ i ∈ M,
      commutativeCellSumset cells (M.erase i) ≠
        commutativeCellSumset cells M) :
    M.card + 1 ≤ (commutativeCellSumset cells M).card := by
  classical
  have aux : ∀ s : Finset ι, s ⊆ M →
      s.card + 1 ≤ (commutativeCellSumset cells s).card := by
    intro s hsM
    induction s using Finset.induction_on with
    | empty => simp [commutativeCellSumset_empty]
    | @insert i s hi ih =>
        have hiM : i ∈ M := hsM (Finset.mem_insert_self i s)
        have hsM' : s ⊆ M.erase i := by
          intro j hjs
          exact Finset.mem_erase.mpr
            ⟨fun hji ↦ hi (hji ▸ hjs), hsM (Finset.mem_insert_of_mem hjs)⟩
        have hne : commutativeCellSumset cells s ≠
            commutativeCellSumset cells (insert i s) := by
          intro heq
          exact hminimal i hiM
            (commutativeCellSumset_erase_eq_of_insert_eq
              cells hiM hsM' heq.symm)
        have hstrict : commutativeCellSumset cells s ⊂
            commutativeCellSumset cells (insert i s) := by
          rw [Finset.ssubset_iff_subset_ne]
          exact ⟨commutativeCellSumset_mono_of_zero cells
            (Finset.subset_insert i s)
            (fun j hj ↦ hzero j (hsM hj)), hne⟩
        have hcardStrict := Finset.card_lt_card hstrict
        have ih' := ih (hsM'.trans (Finset.erase_subset i M))
        rw [Finset.card_insert_of_notMem hi]
        omega
  exact aux M Finset.Subset.rfl

/-- General greedy leaf.  If zero belongs to every cell and the full
labelled sumset has ambient cardinality, then exactly `|A|-1` labelled cells
still have ambient-cardinality sumset. -/
theorem exists_selectedCellSumset_core_card_eq_card_sub_one
    [Nontrivial A] (cells : ι → Finset A)
    (hzero : ∀ i, 0 ∈ cells i)
    (hlength : Nat.card A - 1 ≤ Nat.card ι)
    (hfull : (selectedCellSumset cells (Finset.univ : Finset ι)).card =
      Nat.card A) :
    ∃ core : Finset ι,
      core.card = Nat.card A - 1 ∧
        (selectedCellSumset cells core).card = Nat.card A := by
  classical
  let candidates := (Finset.univ : Finset ι).powerset.filter fun s ↦
    (commutativeCellSumset cells s).card = Nat.card A
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, ?_⟩⟩
    simpa [← selectedCellSumset_eq_commutativeCellSumset] using hfull
  obtain ⟨M, hMcandidate, hMmin⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hMsub : M ⊆ (Finset.univ : Finset ι) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMcandidate).1
  have hMfull : (commutativeCellSumset cells M).card = Nat.card A :=
    (Finset.mem_filter.mp hMcandidate).2
  have hMeraseMinimal : ∀ i ∈ M,
      commutativeCellSumset cells (M.erase i) ≠
        commutativeCellSumset cells M := by
    intro i hiM heq
    have heraseFull :
        (commutativeCellSumset cells (M.erase i)).card = Nat.card A := by
      rw [heq]
      exact hMfull
    have heraseCandidate : M.erase i ∈ candidates :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr
          ((Finset.erase_subset i M).trans hMsub), heraseFull⟩
    have hle := hMmin (M.erase i) heraseCandidate
    have hcardErase := Finset.card_erase_of_mem hiM
    have hMpos : 0 < M.card := Finset.card_pos.mpr ⟨i, hiM⟩
    omega
  have hMcardGrowth :=
    card_add_one_le_commutativeCellSumset_card_of_erase_minimal
      cells M (fun i hi ↦ hzero i) hMeraseMinimal
  have hMcard : M.card ≤ Nat.card A - 1 := by omega
  have htargetLe : Nat.card A - 1 ≤ (Finset.univ : Finset ι).card := by
    simpa [Nat.card_eq_fintype_card] using hlength
  obtain ⟨core, hMcore, _hcoreUniv, hcoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hMsub hMcard htargetLe
  refine ⟨core, hcoreCard, ?_⟩
  have hmono := commutativeCellSumset_mono_of_zero cells hMcore
    (fun i hi ↦ hzero i)
  have hlower := Finset.card_le_card hmono
  have hupper : (commutativeCellSumset cells core).card ≤ Nat.card A := by
    simpa [Nat.card_eq_fintype_card] using
      Finset.card_le_card (Finset.subset_univ
        (commutativeCellSumset cells core))
  rw [selectedCellSumset_eq_commutativeCellSumset]
  omega

/-- Cellwise translation by chosen representatives.  This is the normalization
used in both branches of the subgroup-cardinality induction: the translated
cell contains zero, while all selected full sumsets change only by one global
translation. -/
noncomputable def generalTranslatedCells
    (cells : ι → Finset A) (center : ι → A) : ι → Finset A :=
  fun i ↦ cells i + {-center i}

@[simp]
theorem card_generalTranslatedCells
    (cells : ι → Finset A) (center : ι → A) (i : ι) :
    (generalTranslatedCells cells center i).card = (cells i).card := by
  classical
  simp [generalTranslatedCells]

theorem zero_mem_generalTranslatedCells
    (cells : ι → Finset A) (center : ι → A) (i : ι)
    (hcenter : center i ∈ cells i) :
    0 ∈ generalTranslatedCells cells center i := by
  classical
  exact Finset.mem_add.mpr
    ⟨center i, hcenter, -center i, by simp, by simp⟩

/-- Exact full-sumset transport under independent translations of the
labelled cells. -/
theorem selectedCellSumset_generalTranslatedCells
    (cells : ι → Finset A) (center : ι → A) (s : Finset ι) :
    selectedCellSumset (generalTranslatedCells cells center) s =
      selectedCellSumset cells s + {-∑ i ∈ s, center i} := by
  classical
  rw [selectedCellSumset_eq_commutativeCellSumset,
    selectedCellSumset_eq_commutativeCellSumset]
  induction s using Finset.induction_on with
  | empty => simp [commutativeCellSumset_empty]
  | @insert i s hi ih =>
      rw [commutativeCellSumset_insert _ s i hi,
        commutativeCellSumset_insert _ s i hi, ih,
        Finset.sum_insert hi]
      simp [generalTranslatedCells, add_assoc, add_comm, add_left_comm]

theorem card_selectedCellSumset_generalTranslatedCells
    (cells : ι → Finset A) (center : ι → A) (s : Finset ι) :
    (selectedCellSumset (generalTranslatedCells cells center) s).card =
      (selectedCellSumset cells s).card := by
  classical
  rw [selectedCellSumset_generalTranslatedCells]
  simp

/-- Translating a finite cell translates its quotient layer. -/
theorem quotientLayer_add_singleton_general
    (H : AddSubgroup A) (B : Finset A) (a : A) :
    quotientLayer H (B + {a}) = quotientLayer H B + {(a : A ⧸ H)} := by
  classical
  ext q
  simp only [mem_quotientLayer_iff, Finset.mem_add, Finset.mem_singleton]
  constructor
  · rintro ⟨x, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    subst c
    exact ⟨(b : A ⧸ H), ⟨b, hb, rfl⟩, (a : A ⧸ H), rfl, by simp⟩
  · rintro ⟨qb, ⟨b, hb, rfl⟩, qa, hqa, rfl⟩
    subst qa
    exact ⟨b + a, ⟨b, hb, a, rfl, rfl⟩, by simp⟩

@[simp]
theorem card_quotientLayer_generalTranslatedCells
    (H : AddSubgroup A) (cells : ι → Finset A) (center : ι → A) (i : ι) :
    (quotientLayer H (generalTranslatedCells cells center i)).card =
      (quotientLayer H (cells i)).card := by
  classical
  rw [generalTranslatedCells, quotientLayer_add_singleton_general]
  simp

/-- Target-cardinality version of the greedy leaf.  Unlike the ambient-card
specialization above, this is suitable for a full `K`-coset sumset sitting in
a larger ambient group. -/
theorem exists_selectedCellSumset_core_card_eq_target_sub_one
    (cells : ι → Finset A) (N : ℕ)
    (hzero : ∀ i, 0 ∈ cells i)
    (hlength : N - 1 ≤ Nat.card ι)
    (hfull : (selectedCellSumset cells (Finset.univ : Finset ι)).card = N) :
    ∃ core : Finset ι,
      core.card = N - 1 ∧ (selectedCellSumset cells core).card = N := by
  classical
  let candidates := (Finset.univ : Finset ι).powerset.filter fun s ↦
    (commutativeCellSumset cells s).card = N
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, ?_⟩⟩
    simpa [← selectedCellSumset_eq_commutativeCellSumset] using hfull
  obtain ⟨M, hMcandidate, hMmin⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hMsub : M ⊆ (Finset.univ : Finset ι) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMcandidate).1
  have hMfull : (commutativeCellSumset cells M).card = N :=
    (Finset.mem_filter.mp hMcandidate).2
  have hMeraseMinimal : ∀ i ∈ M,
      commutativeCellSumset cells (M.erase i) ≠
        commutativeCellSumset cells M := by
    intro i hiM heq
    have heraseFull :
        (commutativeCellSumset cells (M.erase i)).card = N := by
      rw [heq]
      exact hMfull
    have heraseCandidate : M.erase i ∈ candidates :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr
          ((Finset.erase_subset i M).trans hMsub), heraseFull⟩
    have hle := hMmin (M.erase i) heraseCandidate
    have hcardErase := Finset.card_erase_of_mem hiM
    have hMpos : 0 < M.card := Finset.card_pos.mpr ⟨i, hiM⟩
    omega
  have hMcardGrowth :=
    card_add_one_le_commutativeCellSumset_card_of_erase_minimal
      cells M (fun i hi ↦ hzero i) hMeraseMinimal
  have hMcard : M.card ≤ N - 1 := by omega
  have htargetLe : N - 1 ≤ (Finset.univ : Finset ι).card := by
    simpa [Nat.card_eq_fintype_card] using hlength
  obtain ⟨core, hMcore, hcoreUniv, hcoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hMsub hMcard htargetLe
  refine ⟨core, hcoreCard, ?_⟩
  have hlower := Finset.card_le_card
    (commutativeCellSumset_mono_of_zero cells hMcore
      (fun i hi ↦ hzero i))
  have hupper := Finset.card_le_card
    (commutativeCellSumset_mono_of_zero cells hcoreUniv
      (fun i hi ↦ hzero i))
  rw [selectedCellSumset_eq_commutativeCellSumset]
  have huniv : (commutativeCellSumset cells
      (Finset.univ : Finset ι)).card = N := by
    simpa [← selectedCellSumset_eq_commutativeCellSumset] using hfull
  omega

/-! ## The exact source conclusion and the canonical proper branch -/

/-- Exact labelled form of the conclusion of source Lemma 3.5.  The source
asserts `|sigma(A'')| = |H|`; it does not assert that the sumset is literally
the subgroup `H` without a preceding translation. -/
structure GeneralLemma35Certificate
    (K : AddSubgroup A) (cells : ι → Finset A) where
  H : AddSubgroup A
  H_le_K : H ≤ K
  H_ne_bot : H ≠ ⊥
  retained : Finset ι
  core : Finset ι
  core_subset_retained : core ⊆ retained
  retained_card_lower :
    min (Nat.card ι) (Nat.card ι - Nat.card (K ⧸ H.addSubgroupOf K) + 2) ≤
      retained.card
  core_card : core.card = Nat.card H - 1
  core_sumset_card : (selectedCellSumset cells core).card = Nat.card H
  retained_singleton_mod :
    ∀ i ∈ retained, (quotientLayer H (cells i)).card = 1

/-- Quotienting by the trivial subgroup does not identify two elements of a
finite cell. -/
@[simp]
theorem card_quotientLayer_bot_general (B : Finset A) :
    (quotientLayer (⊥ : AddSubgroup A) B).card = B.card := by
  classical
  unfold quotientLayer
  apply Finset.card_image_iff.mpr
  intro x _hx y _hy hxy
  have hsub : x - y ∈ (⊥ : AddSubgroup A) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  exact sub_eq_zero.mp hsub

/-- A list of singleton finite sets has a singleton full-layer sumset. -/
theorem fullLayerSumSpectrum_card_eq_one_of_cells_card_eq_one
    [DecidableEq A] (P : List (Finset A))
    (hP : ∀ B ∈ P, B.card = 1) :
    (fullLayerSumSpectrum P).card = 1 := by
  classical
  induction P with
  | nil => simp
  | cons B P ih =>
      have hB : B.card = 1 := hP B (by simp)
      have htail : ∀ C ∈ P, C.card = 1 := by
        intro C hC
        exact hP C (by simp [hC])
      obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (ih htail)
      rw [fullLayerSumSpectrum_cons, ht]
      simp

/-- If every selected cell lies in one `K`-coset, then their full sumset also
lies in one `K`-coset.  This is the quotient-fiber input to the stabilizer
step in the proof of Lemma 3.5. -/
theorem quotientLayer_selectedCellSumset_card_eq_one
    (K : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι)
    (hsingle : ∀ i ∈ s, (quotientLayer K (cells i)).card = 1) :
    (quotientLayer K (selectedCellSumset cells s)).card = 1 := by
  classical
  letI : DecidablePred (fun x : A ↦ x ∈ K) := Classical.decPred _
  letI : DecidableEq (A ⧸ K) :=
    QuotientAddGroup.instDecidableEqQuotientAddSubgroupOfDecidablePredMem K
  let P := indexedCellsOn cells s
  let q : A →+ A ⧸ K := QuotientAddGroup.mk' K
  have himage := image_layerSubsumSpectrum q P P.length
  have heq : quotientLayer K (selectedCellSumset cells s) =
      layerSubsumSpectrum
        (P.map fun C ↦ quotientLayer K C) P.length := by
    simpa [P, q, quotientLayer, selectedCellSumset,
      fullLayerSumSpectrum] using himage
  have hcellsImage :
      ∀ B ∈ P.map (fun C ↦ quotientLayer K C), B.card = 1 := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
    exact hsingle i (Finset.mem_toList.mp hi)
  have hone := fullLayerSumSpectrum_card_eq_one_of_cells_card_eq_one
    (P.map fun C ↦ quotientLayer K C) hcellsImage
  rw [heq]
  simpa [fullLayerSumSpectrum] using hone

/-- The stabilizer of the selected full sumset lies in every subgroup modulo
which all selected cells are singletons. -/
theorem selectedCellStabilizer_le
    (K : AddSubgroup A) (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty)
    (hsingle : ∀ i ∈ s, (quotientLayer K (cells i)).card = 1) :
    selectedCellStabilizer cells s ≤ K := by
  let T := selectedCellSumset cells s
  have hT : T.Nonempty := selectedCellSumset_nonempty cells s hcells
  have hcard : (quotientLayer K T).card = 1 := by
    simpa [T] using quotientLayer_selectedCellSumset_card_eq_one
      K cells s hsingle
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  apply stabilizer_le_of_nonempty_subset_quotientFiber K T hT q
  intro x hx
  have hxq : (x : A ⧸ K) ∈ quotientLayer K T :=
    (mem_quotientLayer_iff K T _).2 ⟨x, hx, rfl⟩
  rw [hq] at hxq
  exact Finset.mem_singleton.mp hxq

/-- A nonempty finite set contained in one `K`-coset has at most `|K|`
elements. -/
theorem card_le_natCard_of_quotientLayer_card_eq_one
    (K : AddSubgroup A) (T : Finset A) (hT : T.Nonempty)
    (hcard : (quotientLayer K T).card = 1) :
    T.card ≤ Nat.card K := by
  obtain ⟨a, ha, hcenter⟩ :=
    exists_cell_center_of_quotientLayer_card_eq_one K T hT hcard
  have hsubset : T ⊆ dgmCosetFiber K a := by
    intro x hx
    apply (mem_dgmCosetFiber_iff K a x).2
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact hcenter x hx
  exact (Finset.card_le_card hsubset).trans_eq (card_dgmCosetFiber K a)

/-- In the strict-cardinality branch of Lemma 3.5, the canonical sumset
stabilizer is nontrivial.  This is the key DGM/Kneser gate: if the stabilizer
were trivial, every cell of size at least two would contribute one unit of
excess, forcing the sumset to have at least `|K|` elements. -/
theorem selectedCellStabilizer_ne_bot_of_card_lt
    (K : AddSubgroup A) (cells : ι → Finset A)
    (hcells : ∀ i, (cells i).Nonempty)
    (hcardTwo : ∀ i, 2 ≤ (cells i).card)
    (hsingleK : ∀ i, (quotientLayer K (cells i)).card = 1)
    (hlength : Nat.card K - 1 ≤ Nat.card ι)
    (hsmall : (selectedCellSumset cells Finset.univ).card < Nat.card K) :
    selectedCellStabilizer cells Finset.univ ≠ ⊥ := by
  classical
  intro hbot
  have hexcessTerm :
      ∀ i : ι, 1 ≤ cellQuotientExcess
        (selectedCellStabilizer cells Finset.univ) cells i := by
    intro i
    rw [hbot]
    unfold cellQuotientExcess
    rw [card_quotientLayer_bot_general]
    have hi := hcardTwo i
    omega
  have hexcess :
      Nat.card ι ≤ quotientExcessOn
        (selectedCellStabilizer cells Finset.univ) cells Finset.univ := by
    calc
      Nat.card ι = ∑ i : ι, 1 := by
        simp [Nat.card_eq_fintype_card]
      _ ≤ ∑ i : ι, cellQuotientExcess
          (selectedCellStabilizer cells Finset.univ) cells i := by
        exact Finset.sum_le_sum fun i _hi ↦ hexcessTerm i
      _ = quotientExcessOn
          (selectedCellStabilizer cells Finset.univ) cells Finset.univ := by
        simp [quotientExcessOn]
  have hdgm := selectedCellSumset_dgm_excess_bound
    cells (Finset.univ : Finset ι) (by simpa using hcells)
  have hstabCard :
      (selectedCellSumset cells Finset.univ).addStab.card = 1 := by
    have hT := selectedCellSumset_nonempty cells (Finset.univ : Finset ι)
      (by simpa using hcells)
    rw [card_addStab_eq_natCard_stabilizer _ hT]
    change Nat.card (selectedCellStabilizer cells Finset.univ) = 1
    rw [hbot]
    simp
  rw [hstabCard, mul_one] at hdgm
  have hTpos : 0 < (selectedCellSumset cells Finset.univ).card :=
    Finset.card_pos.mpr (selectedCellSumset_nonempty cells
      (Finset.univ : Finset ι) (by simpa using hcells))
  have : Nat.card K ≤ (selectedCellSumset cells Finset.univ).card := by
    omega
  exact (Nat.not_le_of_lt hsmall) this

/-- The source hypotheses also place the canonical strict-branch stabilizer
inside `K`. -/
theorem selectedCellStabilizer_lt_K_of_card_lt
    (K : AddSubgroup A) (cells : ι → Finset A)
    (hcells : ∀ i, (cells i).Nonempty)
    (hsingleK : ∀ i, (quotientLayer K (cells i)).card = 1)
    (hsmall : (selectedCellSumset cells Finset.univ).card < Nat.card K) :
    selectedCellStabilizer cells Finset.univ < K := by
  have hle : selectedCellStabilizer cells Finset.univ ≤ K :=
    selectedCellStabilizer_le K cells Finset.univ
      (by simpa using hcells) (by simpa using hsingleK)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hT := selectedCellSumset_nonempty cells (Finset.univ : Finset ι)
    (by simpa using hcells)
  have hperiod :
      Nat.card K ≤ (selectedCellSumset cells Finset.univ).card := by
    obtain ⟨y, hy⟩ := hT
    have hfiber : dgmCosetFiber K y ⊆
        selectedCellSumset cells Finset.univ := by
      apply dgmCosetFiber_subset_of_mem_of_stabilizer_eq
        (selectedCellSumset cells Finset.univ) ⟨y, hy⟩ K
      · exact heq
      · exact hy
    simpa [card_dgmCosetFiber] using Finset.card_le_card hfiber
  exact (Nat.not_le_of_lt hsmall) hperiod

/-- In the strict branch, all but at most `|K/H|-2` labelled cells are
singletons modulo the canonical stabilizer `H`.  This is the precise
Kneser/DGM omission estimate in the proof of Lemma 3.5. -/
theorem card_nonsingleton_canonicalStabilizer_le_internalQuotient_sub_two
    (K : AddSubgroup A) (cells : ι → Finset A)
    (hcells : ∀ i, (cells i).Nonempty)
    (hsingleK : ∀ i, (quotientLayer K (cells i)).card = 1)
    (hsmall : (selectedCellSumset cells Finset.univ).card < Nat.card K) :
    (nonsingletonModIndicesOn
        (selectedCellStabilizer cells Finset.univ) cells Finset.univ).card ≤
      Nat.card (K ⧸
        (selectedCellStabilizer cells Finset.univ).addSubgroupOf K) - 2 := by
  classical
  let H := selectedCellStabilizer cells Finset.univ
  let T := selectedCellSumset cells Finset.univ
  have hT : T.Nonempty := selectedCellSumset_nonempty cells Finset.univ
    (by simpa using hcells)
  have hHK : H < K := by
    simpa [H, T] using selectedCellStabilizer_lt_K_of_card_lt
      K cells hcells hsingleK hsmall
  have hdgm := selectedCellSumset_dgm_excess_bound
    cells (Finset.univ : Finset ι) (by simpa using hcells)
  have hstabCard : T.addStab.card = Nat.card H := by
    rw [card_addStab_eq_natCard_stabilizer T hT]
    rfl
  have hdgm' :
      (quotientExcessOn H cells Finset.univ + 1) * Nat.card H ≤ T.card := by
    simpa [H, T, hstabCard] using hdgm
  have hinsideCard : Nat.card (H.addSubgroupOf K) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHK.le)
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (H.addSubgroupOf K)
  rw [hinsideCard] at hfactor
  have hmul :
      (quotientExcessOn H cells Finset.univ + 1) * Nat.card H <
        Nat.card (K ⧸ H.addSubgroupOf K) * Nat.card H := by
    exact hdgm'.trans_lt (hsmall.trans_eq hfactor)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hexcessLt :
      quotientExcessOn H cells Finset.univ + 1 <
        Nat.card (K ⧸ H.addSubgroupOf K) :=
    (Nat.mul_lt_mul_right hHpos).mp hmul
  have homitted := card_nonsingletonModIndicesOn_le_quotientExcessOn
    H cells (Finset.univ : Finset ι) (by simpa using hcells)
  simpa [H] using homitted.trans (show
    quotientExcessOn H cells Finset.univ ≤
      Nat.card (K ⧸ H.addSubgroupOf K) - 2 by omega)

/-- The retained singleton-mod-stabilizer labels meet the recursive
`|H|-1` threshold.  This is the exact source-deficit arithmetic needed to
apply strong induction inside `H`. -/
theorem card_sub_one_le_card_singletonModIndices_canonical
    (K : AddSubgroup A) (cells : ι → Finset A)
    (hcells : ∀ i, (cells i).Nonempty)
    (hcardTwo : ∀ i, 2 ≤ (cells i).card)
    (hsingleK : ∀ i, (quotientLayer K (cells i)).card = 1)
    (hlength : Nat.card K - 1 ≤ Nat.card ι)
    (hsmall : (selectedCellSumset cells Finset.univ).card < Nat.card K) :
    Nat.card (selectedCellStabilizer cells Finset.univ) - 1 ≤
      (singletonModIndicesOn
        (selectedCellStabilizer cells Finset.univ) cells Finset.univ).card := by
  classical
  let H := selectedCellStabilizer cells Finset.univ
  let retained := singletonModIndicesOn H cells Finset.univ
  let omitted := nonsingletonModIndicesOn H cells Finset.univ
  have hHK : H < K := by
    simpa [H] using selectedCellStabilizer_lt_K_of_card_lt
      K cells hcells hsingleK hsmall
  have hHne : H ≠ ⊥ := by
    simpa [H] using selectedCellStabilizer_ne_bot_of_card_lt
      K cells hcells hcardTwo hsingleK hlength hsmall
  have hq2 : 2 ≤ Nat.card (K ⧸ H.addSubgroupOf K) :=
    two_le_natCard_internal_quotient_of_lt H K hHK
  have hH2 : 2 ≤ Nat.card H := by
    letI : Nontrivial H := (AddSubgroup.nontrivial_iff_ne_bot H).2 hHne
    exact (Finite.one_lt_card_iff_nontrivial).2 inferInstance
  have homit : omitted.card ≤ Nat.card (K ⧸ H.addSubgroupOf K) - 2 := by
    simpa [H, omitted] using
      card_nonsingleton_canonicalStabilizer_le_internalQuotient_sub_two
        K cells hcells hsingleK hsmall
  have hpartition : retained.card + omitted.card = Nat.card ι := by
    simpa [H, retained, omitted, Nat.card_eq_fintype_card] using
      card_singletonModIndicesOn_add_nonsingleton
        H cells (Finset.univ : Finset ι)
  have hinsideCard : Nat.card (H.addSubgroupOf K) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHK.le)
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (H.addSubgroupOf K)
  rw [hinsideCard] at hfactor
  by_contra hnot
  change ¬Nat.card H - 1 ≤ retained.card at hnot
  have hretSmall : retained.card + 2 ≤ Nat.card H := by omega
  have homitSmall : omitted.card + 2 ≤
      Nat.card (K ⧸ H.addSubgroupOf K) := by omega
  have htotal : Nat.card K ≤ retained.card + omitted.card + 1 := by omega
  rw [hfactor] at htotal
  nlinarith

/-! ## Retained-subtype recursion and quotient composition -/

/-- Literal occurrence type retained by the canonical singleton-mod-`H`
filter.  Using the finite-set subtype keeps repeated equal cells distinct. -/
def GeneralLemma35RetainedIndex
    (H : AddSubgroup A) (cells : ι → Finset A) : Type v :=
  ↥(singletonModIndicesOn H cells (Finset.univ : Finset ι))

noncomputable local instance generalLemma35RetainedFintype
    (H : AddSubgroup A) (cells : ι → Finset A) :
    Fintype (GeneralLemma35RetainedIndex H cells) := by
  classical
  unfold GeneralLemma35RetainedIndex
  infer_instance

@[simp]
theorem natCard_generalLemma35RetainedIndex
    (H : AddSubgroup A) (cells : ι → Finset A) :
    Nat.card (GeneralLemma35RetainedIndex H cells) =
      (singletonModIndicesOn H cells (Finset.univ : Finset ι)).card := by
  classical
  let R := singletonModIndicesOn H cells (Finset.univ : Finset ι)
  change Nat.card ↥R = R.card
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_coe R

/-- A finite labelled sumset is unchanged, up to reindexing, when a finite
carrier in a subtype is mapped injectively back to the original labels. -/
theorem selectedCellSumset_subtype_image
    {p : ι → Prop} [DecidablePred p]
    (cells : ι → Finset A) (s : Finset {i // p i}) :
    selectedCellSumset (fun j : {i // p i} ↦ cells j.1) s =
      selectedCellSumset cells (s.image Subtype.val) := by
  classical
  have hperm : (s.image Subtype.val).toList.Perm
      (s.toList.map Subtype.val) := by
    have hrightNodup : (s.toList.map Subtype.val).Nodup :=
      (Finset.nodup_toList s).map Subtype.val_injective
    apply (List.perm_ext_iff_of_nodup
      (Finset.nodup_toList (s.image Subtype.val)) hrightNodup).2
    intro i
    simp
  unfold selectedCellSumset indexedCellsOn
  rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
    fullLayerSumSpectrum_eq_iteratedFinsetSum]
  apply iteratedFinsetSum_eq_of_perm_general
  simpa [List.map_map, Function.comp_def] using (hperm.map cells).symm

theorem card_selectedCellSumset_translated_subtype_image
    {p : ι → Prop} [DecidablePred p]
    (cells : ι → Finset A) (center : {i // p i} → A)
    (s : Finset {i // p i}) :
    (selectedCellSumset
        (generalTranslatedCells (fun j : {i // p i} ↦ cells j.1) center) s).card =
      (selectedCellSumset cells (s.image Subtype.val)).card := by
  rw [card_selectedCellSumset_generalTranslatedCells,
    selectedCellSumset_subtype_image]

/-- `Finset.map` form of the subtype reindexing bridge.  It avoids making the
transport depend on a particular synthesized decidable-equality instance. -/
theorem selectedCellSumset_subtype_map
    {p : ι → Prop} [DecidablePred p]
    (cells : ι → Finset A) (s : Finset {i // p i}) :
    selectedCellSumset (fun j : {i // p i} ↦ cells j.1) s =
      selectedCellSumset cells
        (s.map ⟨Subtype.val, Subtype.val_injective⟩) := by
  classical
  have hperm : (s.map ⟨Subtype.val, Subtype.val_injective⟩).toList.Perm
      (s.toList.map Subtype.val) := by
    have hrightNodup : (s.toList.map Subtype.val).Nodup :=
      (Finset.nodup_toList s).map Subtype.val_injective
    apply (List.perm_ext_iff_of_nodup
      (Finset.nodup_toList (s.map ⟨Subtype.val, Subtype.val_injective⟩))
      hrightNodup).2
    intro i
    simp
  unfold selectedCellSumset indexedCellsOn
  rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
    fullLayerSumSpectrum_eq_iteratedFinsetSum]
  apply iteratedFinsetSum_eq_of_perm_general
  simpa [List.map_map, Function.comp_def] using (hperm.map cells).symm

theorem card_selectedCellSumset_translated_subtype_map
    {p : ι → Prop} [DecidablePred p]
    (cells : ι → Finset A) (center : {i // p i} → A)
    (s : Finset {i // p i}) :
    (selectedCellSumset
        (generalTranslatedCells (fun j : {i // p i} ↦ cells j.1) center) s).card =
      (selectedCellSumset cells
        (s.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  rw [card_selectedCellSumset_generalTranslatedCells,
    selectedCellSumset_subtype_map]

/-- Instance-stable transport through an explicitly supplied subtype-value
embedding. -/
theorem card_selectedCellSumset_translated_subtype_map_of_embedding
    {p : ι → Prop} [DecidablePred p]
    (cells : ι → Finset A) (center : {i // p i} → A)
    (e : {i // p i} ↪ ι) (he : ∀ j, e j = j.1)
    (s : Finset {i // p i}) :
    (selectedCellSumset
        (generalTranslatedCells (fun j : {i // p i} ↦ cells j.1) center) s).card =
      (selectedCellSumset cells (s.map e)).card := by
  classical
  rw [card_selectedCellSumset_generalTranslatedCells]
  have hperm : (s.map e).toList.Perm (s.toList.map e) := by
    have hrightNodup : (s.toList.map e).Nodup :=
      (Finset.nodup_toList s).map e.injective
    apply (List.perm_ext_iff_of_nodup
      (Finset.nodup_toList (s.map e)) hrightNodup).2
    intro i
    simp
  unfold selectedCellSumset indexedCellsOn
  rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
    fullLayerSumSpectrum_eq_iteratedFinsetSum]
  apply congrArg Finset.card
  apply iteratedFinsetSum_eq_of_perm_general
  have hmapped := (hperm.map cells).symm
  simp only [List.map_map] at hmapped
  have hfun : (cells ∘ e) =
      (fun j : {i // p i} ↦ cells j.1) := by
    funext j
    simp [Function.comp_apply, he j]
  rw [hfun] at hmapped
  exact hmapped

/-- Internal quotient cardinalities multiply along a chain `L ≤ H ≤ K`. -/
theorem natCard_internalQuotient_chain
    (L H K : AddSubgroup A) (hLH : L ≤ H) (hHK : H ≤ K) :
    Nat.card (K ⧸ L.addSubgroupOf K) =
      Nat.card (K ⧸ H.addSubgroupOf K) *
        Nat.card (H ⧸ L.addSubgroupOf H) := by
  have hLK : L ≤ K := hLH.trans hHK
  have hLKin : Nat.card (L.addSubgroupOf K) = Nat.card L :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hLK)
  have hHKin : Nat.card (H.addSubgroupOf K) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHK)
  have hLHin : Nat.card (L.addSubgroupOf H) = Nat.card L :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hLH)
  have hKL := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (L.addSubgroupOf K)
  have hKH := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (H.addSubgroupOf K)
  have hHL := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (L.addSubgroupOf H)
  rw [hLKin] at hKL
  rw [hHKin] at hKH
  rw [hLHin] at hHL
  apply Nat.mul_right_cancel (show 0 < Nat.card L from Nat.card_pos)
  calc
    Nat.card (K ⧸ L.addSubgroupOf K) * Nat.card L = Nat.card K := hKL.symm
    _ = Nat.card (K ⧸ H.addSubgroupOf K) * Nat.card H := hKH
    _ = Nat.card (K ⧸ H.addSubgroupOf K) *
          (Nat.card (H ⧸ L.addSubgroupOf H) * Nat.card L) := by rw [← hHL]
    _ = (Nat.card (K ⧸ H.addSubgroupOf K) *
          Nat.card (H ⧸ L.addSubgroupOf H)) * Nat.card L := by
        rw [Nat.mul_assoc]

omit [AddCommGroup A] [Fintype A] [Fintype ι] in
theorem general_sub_two_add_sub_two_le_mul_sub_two
    (a b : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (a - 2) + (b - 2) ≤ a * b - 2 := by
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp
  · have hb2 : 2 ≤ b := by omega
    have hmul : a + b ≤ a * b := by nlinarith
    omega

/-- Lift a recursive certificate from the translated retained-index problem.
The ambient group does not change: translating each retained cell makes it a
valid `H`-coset cell, and the recursive subgroup is already a subgroup of the
original ambient group. -/
noncomputable def generalLemma35Certificate_of_retained
    (K H : AddSubgroup A) (hHK : H < K)
    (cells : ι → Finset A)
    (hlength : Nat.card K - 1 ≤ Nat.card ι)
    (houter :
      (nonsingletonModIndicesOn H cells (Finset.univ : Finset ι)).card ≤
        Nat.card (K ⧸ H.addSubgroupOf K) - 2)
    (center :
      ↥(singletonModIndicesOn H cells (Finset.univ : Finset ι)) → A)
    (C : GeneralLemma35Certificate H
      (generalTranslatedCells
        (fun j : ↥(singletonModIndicesOn H cells
          (Finset.univ : Finset ι)) ↦ cells j.1) center)) :
    GeneralLemma35Certificate K cells := by
  classical
  let R := singletonModIndicesOn H cells (Finset.univ : Finset ι)
  let O := nonsingletonModIndicesOn H cells (Finset.univ : Finset ι)
  let valEmb : ↥(singletonModIndicesOn H cells
      (Finset.univ : Finset ι)) ↪ ι :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let retained := C.retained.map valEmb
  let core := C.core.map valEmb
  refine {
    H := C.H
    H_le_K := C.H_le_K.trans hHK.le
    H_ne_bot := C.H_ne_bot
    retained := retained
    core := core
    core_subset_retained := ?_
    retained_card_lower := ?_
    core_card := ?_
    core_sumset_card := ?_
    retained_singleton_mod := ?_
  }
  · exact Finset.map_subset_map.mpr C.core_subset_retained
  · have hretainedCard : retained.card = C.retained.card := by
      exact Finset.card_map valEmb
    have hRcard : Nat.card ↥R = R.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe R
    have hCcardLe : C.retained.card ≤
        Nat.card ↥R := by
      simpa [Nat.card_eq_fintype_card] using
        Finset.card_le_card (Finset.subset_univ C.retained)
    let a := Nat.card (K ⧸ H.addSubgroupOf K)
    let b := Nat.card (H ⧸ C.H.addSubgroupOf H)
    have ha : 2 ≤ a := by
      simpa [a] using two_le_natCard_internal_quotient_of_lt H K hHK
    have hb : 1 ≤ b := by exact Nat.card_pos
    have hinner :
        Nat.card ↥R - C.retained.card ≤
          b - 2 := by
      have hrec := C.retained_card_lower
      change min (Nat.card ↥R)
        (Nat.card ↥R - b + 2) ≤
          C.retained.card at hrec
      omega
    have hpartition : R.card + O.card = Nat.card ι := by
      simpa [R, O, Nat.card_eq_fintype_card] using
        card_singletonModIndicesOn_add_nonsingleton
          H cells (Finset.univ : Finset ι)
    have houter' : O.card ≤ a - 2 := by simpa [O, a] using houter
    have hsum : (a - 2) + (b - 2) ≤ a * b - 2 :=
      general_sub_two_add_sub_two_le_mul_sub_two a b ha hb
    have hquot : Nat.card (K ⧸ C.H.addSubgroupOf K) = a * b := by
      simpa [a, b] using
        natCard_internalQuotient_chain C.H H K C.H_le_K hHK.le
    have hdeficit : Nat.card ι - C.retained.card ≤ a * b - 2 := by
      omega
    have hquotCardFactor :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (C.H.addSubgroupOf K)
    have hCHinside : Nat.card (C.H.addSubgroupOf K) = Nat.card C.H :=
      Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe
        (C.H_le_K.trans hHK.le))
    rw [hCHinside, hquot] at hquotCardFactor
    have hCH2 : 2 ≤ Nat.card C.H := by
      letI : Nontrivial C.H :=
        (AddSubgroup.nontrivial_iff_ne_bot C.H).2 C.H_ne_bot
      exact (Finite.one_lt_card_iff_nontrivial).2 inferInstance
    have hKLeLength : Nat.card K ≤ Nat.card ι + 1 := by omega
    have hqLeLength : a * b ≤ Nat.card ι := by nlinarith
    rw [hretainedCard, hquot]
    omega
  · simpa [core, valEmb] using C.core_card
  · calc
      (selectedCellSumset cells core).card =
          (selectedCellSumset
            (generalTranslatedCells
              (fun j : ↥(singletonModIndicesOn H cells
                (Finset.univ : Finset ι)) ↦ cells j.1) center)
            C.core).card := by
        simpa [core] using
          (card_selectedCellSumset_translated_subtype_map_of_embedding
            cells center valEmb (by intro j; rfl) C.core).symm
      _ = Nat.card C.H := C.core_sumset_card
  · intro i hi
    change i ∈ C.retained.map valEmb at hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    have htranslated := C.retained_singleton_mod j hj
    rw [card_quotientLayer_generalTranslatedCells] at htranslated
    exact htranslated

/-! ## Strong induction and the complete source certificate -/

/-- Universe-polymorphic induction predicate, measured by the order of the
source subgroup rather than by the (possibly larger) ambient group. -/
def GeneralLemma35CertificateAtSubgroupCard (m : ℕ) : Prop :=
  ∀ (B : Type u) [AddCommGroup B] [Fintype B],
    ∀ (K : AddSubgroup B), Nat.card K = m → K ≠ ⊥ →
    ∀ (κ : Type v) [Fintype κ] (cells : κ → Finset B),
      (∀ i, 2 ≤ (cells i).card) →
      (∀ i, (quotientLayer K (cells i)).card = 1) →
      Nat.card K - 1 ≤ Nat.card κ →
      Nonempty (GeneralLemma35Certificate K cells)

/-- The full-cardinality branch of Lemma 3.5.  Independent cell translations
put zero in every cell; the deletion-minimal greedy carrier is then padded to
exactly `|K|-1` labels. -/
theorem generalLemma35Certificate_of_full_cardinality
    (K : AddSubgroup A) (hKne : K ≠ ⊥)
    (cells : ι → Finset A)
    (hcardTwo : ∀ i, 2 ≤ (cells i).card)
    (hsingleK : ∀ i, (quotientLayer K (cells i)).card = 1)
    (hlength : Nat.card K - 1 ≤ Nat.card ι)
    (hfull : (selectedCellSumset cells (Finset.univ : Finset ι)).card =
      Nat.card K) :
    Nonempty (GeneralLemma35Certificate K cells) := by
  classical
  have hcells : ∀ i, (cells i).Nonempty := by
    intro i
    apply Finset.card_pos.mp
    have hi := hcardTwo i
    omega
  let center : ι → A := fun i ↦ Classical.choose (hcells i)
  have hcenter : ∀ i, center i ∈ cells i := by
    intro i
    exact Classical.choose_spec (hcells i)
  let normalized := generalTranslatedCells cells center
  have hzero : ∀ i, 0 ∈ normalized i := by
    intro i
    exact zero_mem_generalTranslatedCells cells center i (hcenter i)
  have hfullNormalized :
      (selectedCellSumset normalized (Finset.univ : Finset ι)).card =
        Nat.card K := by
    simpa [normalized] using
      (card_selectedCellSumset_generalTranslatedCells
        cells center (Finset.univ : Finset ι)).trans hfull
  obtain ⟨core, hcoreCard, hcoreFull⟩ :=
    exists_selectedCellSumset_core_card_eq_target_sub_one
      normalized (Nat.card K) hzero hlength hfullNormalized
  have hqSelf : Nat.card (K ⧸ K.addSubgroupOf K) = 1 := by
    have hinside : K.addSubgroupOf K = ⊤ := by
      ext x
      simp
    rw [hinside]
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨QuotientAddGroup.subsingleton_quotient_top, ⟨0⟩⟩
  refine ⟨{
    H := K
    H_le_K := le_rfl
    H_ne_bot := hKne
    retained := Finset.univ
    core := core
    core_subset_retained := Finset.subset_univ core
    retained_card_lower := ?_
    core_card := hcoreCard
    core_sumset_card := ?_
    retained_singleton_mod := ?_
  }⟩
  · rw [hqSelf]
    simp [Nat.card_eq_fintype_card]
  · rw [← card_selectedCellSumset_generalTranslatedCells cells center core]
    simpa [normalized] using hcoreFull
  · intro i _hi
    exact hsingleK i

/-- Complete labelled form of GMO Lemma 3.5.  The proof follows the source
minimal-counterexample argument as a well-founded strong induction on `|K|`:
the full branch is the greedy leaf above; the strict branch recurses on the
nontrivial proper stabilizer after translating the retained cells. -/
theorem generalLemma35Certificate_exists
    (K : AddSubgroup A) (hKne : K ≠ ⊥)
    (cells : ι → Finset A)
    (hcardTwo : ∀ i, 2 ≤ (cells i).card)
    (hsingleK : ∀ i, (quotientLayer K (cells i)).card = 1)
    (hlength : Nat.card K - 1 ≤ Nat.card ι) :
    Nonempty (GeneralLemma35Certificate K cells) := by
  classical
  have outer : ∀ m : ℕ,
      GeneralLemma35CertificateAtSubgroupCard.{u, v} m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro B instGroup instFintype K hm hKne
        intro κ instIndexFintype cells hcardTwo hsingleK hlength
        have hcells : ∀ i, (cells i).Nonempty := by
          intro i
          apply Finset.card_pos.mp
          have hi := hcardTwo i
          omega
        let T := selectedCellSumset cells (Finset.univ : Finset κ)
        by_cases hfull : T.card = Nat.card K
        · exact generalLemma35Certificate_of_full_cardinality
            K hKne cells hcardTwo hsingleK hlength (by simpa [T] using hfull)
        · have hTnonempty : T.Nonempty := by
            simpa [T] using selectedCellSumset_nonempty cells
              (Finset.univ : Finset κ) (by simpa using hcells)
          have hquotT : (quotientLayer K T).card = 1 := by
            have hq := quotientLayer_selectedCellSumset_card_eq_one
              K cells (Finset.univ : Finset κ) (by simpa using hsingleK)
            simpa [T] using hq
          have hTle : T.card ≤ Nat.card K :=
            card_le_natCard_of_quotientLayer_card_eq_one
              K T hTnonempty hquotT
          have hsmall : T.card < Nat.card K := by omega
          let H := selectedCellStabilizer cells (Finset.univ : Finset κ)
          have hHK : H < K := by
            simpa [H, T] using selectedCellStabilizer_lt_K_of_card_lt
              K cells hcells hsingleK (by simpa [T] using hsmall)
          have hHne : H ≠ ⊥ := by
            simpa [H, T] using selectedCellStabilizer_ne_bot_of_card_lt
              K cells hcells hcardTwo hsingleK hlength
                (by simpa [T] using hsmall)
          let R := singletonModIndicesOn H cells (Finset.univ : Finset κ)
          let center : ↥R → B := fun j ↦ Classical.choose (hcells j.1)
          have hcenter : ∀ j : ↥R, center j ∈ cells j.1 := by
            intro j
            exact Classical.choose_spec (hcells j.1)
          let retainedCells : ↥R → Finset B :=
            generalTranslatedCells (fun j : ↥R ↦ cells j.1) center
          have hretainedCardTwo : ∀ j, 2 ≤ (retainedCells j).card := by
            intro j
            simpa [retainedCells] using hcardTwo j.1
          have hretainedSingle :
              ∀ j, (quotientLayer H (retainedCells j)).card = 1 := by
            intro j
            have hj : (quotientLayer H (cells j.1)).card = 1 := by
              exact (mem_singletonModIndicesOn_iff
                H cells (Finset.univ : Finset κ) j.1).1 j.2 |>.2
            simpa [retainedCells] using
              (card_quotientLayer_generalTranslatedCells H
                (fun j : ↥R ↦ cells j.1) center j).trans hj
          have hretainedLength : Nat.card H - 1 ≤ Nat.card ↥R := by
            have hcard := card_sub_one_le_card_singletonModIndices_canonical
              K cells hcells hcardTwo hsingleK hlength
                (by simpa [T] using hsmall)
            have hRcard : Nat.card ↥R = R.card := by
              rw [Nat.card_eq_fintype_card]
              exact Fintype.card_coe R
            rw [hRcard]
            simpa [H, R] using hcard
          have hHsmall : Nat.card H < m := by
            rw [← hm]
            exact natCard_lt_of_addSubgroup_lt hHK
          have hrecursive := ih (Nat.card H) hHsmall B H rfl hHne
            ↥R retainedCells hretainedCardTwo hretainedSingle hretainedLength
          obtain ⟨C⟩ := hrecursive
          have houter :
              (nonsingletonModIndicesOn H cells
                (Finset.univ : Finset κ)).card ≤
                Nat.card (K ⧸ H.addSubgroupOf K) - 2 := by
            simpa [H, T] using
              card_nonsingleton_canonicalStabilizer_le_internalQuotient_sub_two
                K cells hcells hsingleK (by simpa [T] using hsmall)
          exact ⟨generalLemma35Certificate_of_retained
            K H hHK cells hlength houter center C⟩
  exact outer (Nat.card K) A K rfl hKne ι cells
    hcardTwo hsingleK hlength

/-! ## Canonical bookkeeping certificate -/

/-- The canonical, always-available bookkeeping projection for a selected
labelled setpartition.  Unlike `GeneralLemma35Certificate`, this smaller
record exposes only the stabilizer/excess ledger and requires no source
length or two-elements-per-cell hypotheses. -/
structure GeneralLemma35Ledger
    (cells : ι → Finset A) (s : Finset ι) where
  H : AddSubgroup A
  H_eq : H = selectedCellStabilizer cells s
  retained : Finset ι
  retained_eq : retained = singletonModIndicesOn H cells s
  omitted_bound :
    (s \ retained).card ≤ quotientExcessOn H cells s
  dgm_excess_bound :
    (quotientExcessOn H cells s + 1) *
        (selectedCellSumset cells s).addStab.card ≤
      (selectedCellSumset cells s).card

/-- Every finite nonempty labelled setpartition has its canonical Lemma 3.5
ledger.  All fields are computed from the selected-cell sumset. -/
noncomputable def generalLemma35Ledger
    (cells : ι → Finset A) (s : Finset ι)
    (hcells : ∀ i ∈ s, (cells i).Nonempty) :
    GeneralLemma35Ledger cells s := by
  let H := selectedCellStabilizer cells s
  let retained := singletonModIndicesOn H cells s
  refine {
    H := H
    H_eq := rfl
    retained := retained
    retained_eq := rfl
    omitted_bound := ?_
    dgm_excess_bound := ?_
  }
  · simpa [retained, nonsingletonModIndicesOn] using
      card_nonsingletonModIndicesOn_le_quotientExcessOn
        H cells s hcells
  · simpa [H] using selectedCellSumset_dgm_excess_bound cells s hcells

end GaoLean

#print axioms GaoLean.card_nonsingletonModIndicesOn_le_quotientExcessOn
#print axioms GaoLean.exists_cell_center_of_quotientLayer_card_eq_one
#print axioms GaoLean.sum_card_quotientLayer_eq_card_add_excess
#print axioms GaoLean.selectedCellSumset_dgm_excess_bound
#print axioms GaoLean.quotientLayer_selectedCellSumset_card_eq_one
#print axioms GaoLean.selectedCellStabilizer_ne_bot_of_card_lt
#print axioms GaoLean.selectedCellStabilizer_lt_K_of_card_lt
#print axioms GaoLean.card_nonsingleton_canonicalStabilizer_le_internalQuotient_sub_two
#print axioms GaoLean.card_sub_one_le_card_singletonModIndices_canonical
#print axioms GaoLean.exists_selectedCellSumset_core_card_eq_target_sub_one
#print axioms GaoLean.natCard_internalQuotient_chain
#print axioms GaoLean.generalLemma35Certificate_of_retained
#print axioms GaoLean.generalLemma35Certificate_of_full_cardinality
#print axioms GaoLean.generalLemma35Certificate_exists
#print axioms GaoLean.generalLemma35Ledger
