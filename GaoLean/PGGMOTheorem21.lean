import GaoLean.PGSetpartitionOccurrences
import GaoLean.PGGMOOrdinarySource
import GaoLean.PGCapacity

/-!
# Occurrence-faithful statement of the GMO partition theorem

This file freezes Theorem 2.1 of Grynkiewicz--Marchan--Ordaz,
*A Weighted Generalization of Two Theorems of Gao* (arXiv:0903.2810v1),
in the ordinary additive setting used by the thirteen-page manuscript.

The source theorem starts with `S' | S`, replaces `S'` by an equally long
subsequence `S'' | S`, and partitions the labelled occurrences of `S''` into
`n` nonempty value-injective cells.  Its concentrated alternative concerns
the whole source `S`, not merely `S'` or `S''`.

`GMOTheorem21Statement` below is only the exact frozen source statement.  It
is not asserted.  The proved content of this module is the occurrence-level
semantics around that boundary: the output setpartition embeds in the exact
source spectrum, the periodic branch gives the existing canonical
concentration object without losing repetitions, and the full-source
setpartition together with its full-layer DGM bound is constructed from the
already proved occurrence-coloring and Kneser endpoint.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- An invariant-factor presentation used solely to give `d^*(A)` its
literal source meaning.  The moduli are nontrivial and form a divisibility
chain, and the displayed additive equivalence identifies `A` with their
finite direct product. -/
structure DStarPresentation (A : Type u) [AddCommGroup A] where
  rank : ℕ
  modulus : Fin rank → ℕ
  modulus_two_le : ∀ i, 2 ≤ modulus i
  chain : ∀ i j, i ≤ j → modulus i ∣ modulus j
  equiv : A ≃+ ((i : Fin rank) → ZMod (modulus i))

/-- The literal invariant-factor value `d^*(A) = sum_i (n_i - 1)`. -/
def DStarPresentation.value (data : DStarPresentation A) : ℕ :=
  ∑ i, (data.modulus i - 1)

/-- The maximum multiplicity of the occurrence-labelled subsequence `I` is
at most `n`.  This is the exact `h(S') ≤ n` hypothesis in Theorem 2.1. -/
noncomputable def SelectionMultiplicityAtMost
    (xs : List A) (I : Selection xs) (n : ℕ) : Prop :=
  by
    classical
    exact ∀ a : A,
      (I.filter fun i ↦ occurrenceValue xs i = a).card ≤ n

/-- An `n`-setpartition of a replacement subsequence `S'' | S` of prescribed
length `m`.  Cells are indexed, nonempty, pairwise occurrence-disjoint and
contain no repeated value.  Their union is the labelled replacement
subsequence. -/
structure Theorem21SetPartition (xs : List A) (n m : ℕ) where
  cells : Fin n → Selection xs
  cells_nonempty : ∀ c, (cells c).Nonempty
  cells_pairwise_disjoint : ∀ {c d}, c ≠ d → Disjoint (cells c) (cells d)
  value_injective : ∀ c,
    Set.InjOn (occurrenceValue xs) (cells c : Set (Occurrence xs))
  card_support : (Finset.univ.biUnion cells).card = m

/-- The labelled occurrence support of the replacement subsequence `S''`. -/
def Theorem21SetPartition.support
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    Selection xs :=
  Finset.univ.biUnion P.cells

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.card_support_eq
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.support.card = m := by
  exact P.card_support

/-- The finite value set contributed by one occurrence cell. -/
noncomputable def Theorem21SetPartition.valueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (c : Fin n) : Finset A := by
  classical
  exact (P.cells c).image (occurrenceValue xs : Occurrence xs → A)

/-- The ordered list of value cells consumed by the DGM sumset layer. -/
noncomputable def Theorem21SetPartition.valueCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    List (Finset A) := by
  classical
  exact List.ofFn fun c : Fin n ↦ P.valueCell c

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.length_valueCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.valueCells.length = n := by
  classical
  simp [Theorem21SetPartition.valueCells]

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.valueCells_nonempty
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    IsNonemptySetPartition P.valueCells := by
  classical
  intro B hB
  simp only [Theorem21SetPartition.valueCells, List.mem_ofFn] at hB
  obtain ⟨c, rfl⟩ := hB
  obtain ⟨i, hi⟩ := P.cells_nonempty c
  refine ⟨occurrenceValue xs i, ?_⟩
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Conversion of a partition of every source occurrence into the replacement
subsequence representation used by Theorem 2.1. -/
noncomputable def OccurrenceSetPartition.toTheorem21SetPartition
    {xs : List A} {n : ℕ} (P : OccurrenceSetPartition xs n) :
    Theorem21SetPartition xs n xs.length := by
  classical
  refine {
    cells := P.cells
    cells_nonempty := P.cells_nonempty
    cells_pairwise_disjoint := fun hcd ↦ P.cells_pairwise_disjoint hcd
    value_injective := P.value_injective
    card_support := ?_
  }
  rw [P.biUnion_cells]
  simp

/-- The full-layer sumset associated to the replacement setpartition. -/
noncomputable def Theorem21SetPartition.sumset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) : Finset A := by
  classical
  exact fullLayerSumSpectrum P.valueCells

/-- Every full-layer value choice lifts to `n` distinct labelled source
occurrences.  Thus Theorem 2.1's sumset is literally contained in the
project's occurrence-sensitive exact-`n` spectrum. -/
theorem Theorem21SetPartition.sumset_subset_ordinaryExactSpectrum
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.sumset ⊆ ordinaryExactSpectrum xs n := by
  classical
  intro y hy
  rw [Theorem21SetPartition.sumset] at hy
  rw [mem_fullLayerSumSpectrum_iff_exists_choice] at hy
  obtain ⟨a, ha, hsum⟩ := hy
  let e : Fin n ≃ Fin P.valueCells.length :=
    finCongr P.length_valueCells.symm
  let a' : Fin n → A := fun c ↦ a (e c)
  have ha' : ∀ c : Fin n, a' c ∈ P.valueCell c := by
    intro c
    have hc := ha (e c)
    simp only [Theorem21SetPartition.valueCells, List.get_ofFn] at hc
    dsimp only [a']
    convert hc using 1
    · congr 1
    · rfl
  have hsum' : (∑ c, a' c) = y := (e.sum_comp a).trans hsum
  have hpick : ∀ c : Fin n, ∃ i : Occurrence xs,
      i ∈ P.cells c ∧ occurrenceValue xs i = a' c := by
    intro c
    simpa [Theorem21SetPartition.valueCell] using ha' c
  let pick : Fin n → Occurrence xs := fun c ↦ Classical.choose (hpick c)
  have pick_mem (c : Fin n) : pick c ∈ P.cells c :=
    (Classical.choose_spec (hpick c)).1
  have pick_value (c : Fin n) : occurrenceValue xs (pick c) = a' c :=
    (Classical.choose_spec (hpick c)).2
  have pick_injective : Function.Injective pick := by
    intro c d hcd
    by_contra hne
    have hdisj := P.cells_pairwise_disjoint hne
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (pick_mem c) (hcd ▸ pick_mem d)
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

/-- Large-sumset branch (i) of Theorem 2.1. -/
structure GMOTheorem21LargeAlternative
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (P : Theorem21SetPartition xs n seed.card) : Prop where
  card_lower : min (Nat.card A) (seed.card - n + 1) ≤ P.sumset.card

/-- Periodic/concentrated branch (ii) of Theorem 2.1.  The exception count is
an exact count of labelled occurrences of the whole source `S`. -/
structure GMOTheorem21PeriodicAlternative
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (P : Theorem21SetPartition xs n seed.card) where
  H : AddSubgroup A
  nontrivial : ⊥ < H
  proper : H < ⊤
  periodic : H ≤ AddAction.stabilizer A (P.sumset : Set A)
  e : ℕ
  alpha : A
  spectrum_card_lower : (e + 1) * Nat.card H ≤ P.sumset.card
  outside_card :
    ((Finset.univ : Selection xs) \ occurrencesInAddCoset xs H alpha).card = e
  outside_le : e ≤ Nat.card (A ⧸ H) - 2

/-- Exact witness returned by Theorem 2.1: an equally long replacement
subsequence, an occurrence-faithful `n`-setpartition, and the unweakened
large/periodic alternative. -/
structure GMOTheorem21Output
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  partition : Theorem21SetPartition xs n seed.card
  alternative :
    GMOTheorem21LargeAlternative xs seed n partition ∨
      Nonempty (GMOTheorem21PeriodicAlternative xs seed n partition)

/-- Exact frozen ordinary statement of GMO Theorem 2.1.  `seed` is `S' | S`;
the output partition support is `S'' | S` and has cardinality `|S'|`.

This proposition is a source boundary, not a theorem asserted here.  The
module's proved lemmas below expose what is already derivable without hiding
this remaining partition-theorem argument. -/
def GMOTheorem21Statement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (data : DStarPresentation A) (xs : List A)
    (seed : Selection xs) (n : ℕ),
    data.value ≤ n →
    SelectionMultiplicityAtMost xs seed n →
    n ≤ seed.card →
    Nonempty (GMOTheorem21Output xs seed n)

/-! ## The smaller replacement/maximal-setpartition boundary (Theorem E) -/

/-- The finite set of elements of a subgroup, kept explicit so the source
expression `A_i + H` is represented by a literal finite sumset. -/
noncomputable def subgroupFinset (H : AddSubgroup A) : Finset A := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ H

@[simp]
theorem mem_subgroupFinset (H : AddSubgroup A) (x : A) :
    x ∈ subgroupFinset H ↔ x ∈ H := by
  classical
  simp [subgroupFinset]

/-- A literal finite additive coset `alpha + H`. -/
noncomputable def addCosetFinset (H : AddSubgroup A) (alpha : A) : Finset A := by
  classical
  exact (subgroupFinset H).image fun h ↦ alpha + h

@[simp]
theorem mem_addCosetFinset_iff (H : AddSubgroup A) (alpha x : A) :
    x ∈ addCosetFinset H alpha ↔ x - alpha ∈ H := by
  classical
  constructor
  · intro hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hx
    simpa using (mem_subgroupFinset H h).1 hh
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨x - alpha, (mem_subgroupFinset H (x - alpha)).2 hx, ?_⟩
    abel

@[simp]
theorem card_addCosetFinset (H : AddSubgroup A) (alpha : A) :
    (addCosetFinset H alpha).card = Nat.card H := by
  classical
  rw [addCosetFinset, Finset.card_image_of_injective]
  · simpa [subgroupFinset, Nat.card_eq_fintype_card] using
      (Fintype.card_subtype (fun x : A ↦ x ∈ H)).symm
  · intro x y hxy
    exact add_left_cancel hxy

/-- Two additive cosets are disjoint when the second representative is not
in the first coset. -/
theorem addCosetFinset_disjoint_of_not_mem
    (H : AddSubgroup A) {alpha beta : A}
    (hbeta : beta ∉ addCosetFinset H alpha) :
    Disjoint (addCosetFinset H alpha) (addCosetFinset H beta) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxalpha hxbeta
  have hxa : x - alpha ∈ H := (mem_addCosetFinset_iff H alpha x).1 hxalpha
  have hxb : x - beta ∈ H := (mem_addCosetFinset_iff H beta x).1 hxbeta
  apply hbeta
  apply (mem_addCosetFinset_iff H alpha beta).2
  have hdiff := H.sub_mem hxa hxb
  have heq : (x - alpha) - (x - beta) = beta - alpha := by abel
  rwa [heq] at hdiff

/-- The source set `A_i + H`. -/
noncomputable def Theorem21SetPartition.thickenedCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) : Finset A := by
  classical
  exact P.valueCell c + subgroupFinset H

/-- The common intersection `⋂_i (A_i + H)` in Theorem E. -/
noncomputable def Theorem21SetPartition.commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) : Finset A := by
  classical
  exact Finset.univ.filter fun x ↦ ∀ c : Fin n, x ∈ P.thickenedCell H c

/-- Labelled source occurrences whose values lie in the common core. -/
noncomputable def Theorem21SetPartition.occurrencesInCommonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i ↦ occurrenceValue xs i ∈ P.commonCore H

/-- The occurrences of one replacement cell whose values lie outside the
common core. -/
noncomputable def Theorem21SetPartition.outsideCoreCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) : Selection xs := by
  classical
  exact (P.cells c).filter fun i ↦ occurrenceValue xs i ∉ P.commonCore H

@[simp]
theorem Theorem21SetPartition.mem_commonCore_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (x : A) :
    x ∈ P.commonCore H ↔ ∀ c : Fin n, x ∈ P.thickenedCell H c := by
  classical
  simp [Theorem21SetPartition.commonCore]

@[simp]
theorem Theorem21SetPartition.mem_occurrencesInCommonCore_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (i : Occurrence xs) :
    i ∈ P.occurrencesInCommonCore H ↔
      occurrenceValue xs i ∈ P.commonCore H := by
  classical
  simp [Theorem21SetPartition.occurrencesInCommonCore]

@[simp]
theorem Theorem21SetPartition.mem_outsideCoreCell_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (i : Occurrence xs) :
    i ∈ P.outsideCoreCell H c ↔
      i ∈ P.cells c ∧ occurrenceValue xs i ∉ P.commonCore H := by
  classical
  simp [Theorem21SetPartition.outsideCoreCell]

/-- `N = |⋂_i(A_i+H)| / |H|` from Theorem E. -/
noncomputable def Theorem21SetPartition.commonCosetCount
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) : ℕ :=
  (P.commonCore H).card / Nat.card H

/-- The contribution of one cell to Theorem E's exception parameter. -/
noncomputable def Theorem21SetPartition.cellExceptionDefect
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) : ℕ := by
  classical
  exact (P.valueCell c).card -
    (P.valueCell c ∩ P.commonCore H).card

/-- `e = Σ_j (|A_j| - |A_j ∩ ⋂_i(A_i+H)|)` from Theorem E. -/
noncomputable def Theorem21SetPartition.exceptionDefect
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) : ℕ := by
  classical
  exact ∑ c : Fin n, P.cellExceptionDefect H c

/-- Exact ordinary specialization of the stronger replacement theorem called
Theorem E in the source of Theorems 2.4 and 2.5. -/
structure GMOTheoremEOutput
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  partition : Theorem21SetPartition xs n seed.card
  H : AddSubgroup A
  periodic : H ≤ AddAction.stabilizer A (partition.sumset : Set A)
  card_lower :
    ((partition.commonCosetCount H - 1) * n +
        partition.exceptionDefect H + 1) * Nat.card H ≤
      partition.sumset.card
  nontrivial_data : H ≠ ⊥ →
    1 ≤ partition.commonCosetCount H ∧
      ∀ i : Occurrence xs, i ∉ partition.support →
        occurrenceValue xs i ∈ partition.commonCore H

/-- Exact frozen ordinary Theorem E.  Singleton weight `1` automatically
satisfies the source coprimality condition, so its only hypotheses are the
literal `S' | S` setpartition criterion.  This is the smallest currently
unproved replacement/maximal-setpartition source boundary. -/
def GMOTheoremEStatement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (seed : Selection xs) (n : ℕ),
    SelectionMultiplicityAtMost xs seed n →
    n ≤ seed.card →
    Nonempty (GMOTheoremEOutput xs seed n)

/-- The exact remaining proper-nontrivial induction kernel after Theorem E.

The source proof of Theorems 2.4/2.5 does not in general retain the first
Theorem E partition: its reindexing and maximal-subgroup argument constructs
a replacement partition.  Consequently this boundary retains the literal
`d^*(A) ≤ n` and setpartition hypotheses and returns a possibly new complete
Theorem 2.1 output.  It deliberately does not assert that the initial
Theorem E output itself satisfies either final alternative. -/
def GMOTheorem25ProperInductionStatement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (data : DStarPresentation A) (xs : List A)
    (seed : Selection xs) (n : ℕ),
    data.value ≤ n →
    SelectionMultiplicityAtMost xs seed n →
    n ≤ seed.card →
    ∀ out : GMOTheoremEOutput xs seed n,
      out.H ≠ ⊥ → out.H < ⊤ →
      Nonempty (GMOTheorem21Output xs seed n)

omit [AddCommGroup A] [Fintype A] in
/-- No cardinality is lost on passing from a labelled cell to its value set. -/
theorem Theorem21SetPartition.card_valueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (c : Fin n) :
    (P.valueCell c).card = (P.cells c).card := by
  classical
  exact Finset.card_image_iff.mpr (P.value_injective c)

omit [AddCommGroup A] [Fintype A] in
/-- The cell cardinalities add to the exact replacement length. -/
theorem Theorem21SetPartition.sum_card_valueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    (∑ c : Fin n, (P.valueCell c).card) = m := by
  classical
  have hdisjoint :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint P.cells := by
    intro c _ d _ hcd
    exact P.cells_pairwise_disjoint hcd
  calc
    (∑ c : Fin n, (P.valueCell c).card) =
        ∑ c : Fin n, (P.cells c).card := by
          apply Finset.sum_congr rfl
          intro c _
          exact P.card_valueCell c
    _ = (Finset.univ.biUnion P.cells).card := by
      rw [Finset.card_biUnion hdisjoint]
    _ = m := P.card_support

/-- Within one cell, value injectivity identifies the occurrence defect with
the corresponding value-set defect used in Theorem E. -/
theorem Theorem21SetPartition.card_outsideCoreCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    (P.outsideCoreCell H c).card =
      P.cellExceptionDefect H c := by
  classical
  have hinj : Set.InjOn (occurrenceValue xs)
      (P.outsideCoreCell H c : Set (Occurrence xs)) :=
    (P.value_injective c).mono (by
      intro i hi
      exact (P.mem_outsideCoreCell_iff H c i).1 hi |>.1)
  have himage :
      (P.outsideCoreCell H c).image (occurrenceValue xs) =
        P.valueCell c \ P.commonCore H := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      have hi' := (P.mem_outsideCoreCell_iff H c i).1 hi
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨i, hi'.1, rfl⟩, hi'.2⟩
    · intro ha
      have ha' := Finset.mem_sdiff.mp ha
      obtain ⟨i, hi, hivalue⟩ := Finset.mem_image.mp ha'.1
      apply Finset.mem_image.mpr
      refine ⟨i, (P.mem_outsideCoreCell_iff H c i).2 ⟨hi, ?_⟩, hivalue⟩
      intro hicore
      exact ha'.2 (hivalue ▸ hicore)
  calc
    (P.outsideCoreCell H c).card =
        ((P.outsideCoreCell H c).image (occurrenceValue xs)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = (P.valueCell c \ P.commonCore H).card := congrArg Finset.card himage
    _ = (P.valueCell c).card -
        (P.commonCore H ∩ P.valueCell c).card := Finset.card_sdiff
    _ = P.cellExceptionDefect H c := by
      simp [Theorem21SetPartition.cellExceptionDefect, Finset.inter_comm]

/-- The sum of labelled outside-core cell sizes is exactly Theorem E's
defect parameter `e`. -/
theorem Theorem21SetPartition.sum_card_outsideCoreCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (∑ c : Fin n, (P.outsideCoreCell H c).card) =
      P.exceptionDefect H := by
  classical
  unfold Theorem21SetPartition.exceptionDefect
  apply Finset.sum_congr rfl
  intro c _
  exact P.card_outsideCoreCell H c

/-- Theorem E's nontrivial-subgroup clause says that every source occurrence
outside the common core belongs to the replacement support. -/
theorem GMOTheoremEOutput.outsideCommonCore_subset_support
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H ≠ ⊥) :
    (Finset.univ : Selection xs) \ h.partition.occurrencesInCommonCore h.H ⊆
      h.partition.support := by
  intro i hi
  by_contra hisupport
  have hcore := (h.nontrivial_data hH).2 i hisupport
  have hnotcore : occurrenceValue xs i ∉ h.partition.commonCore h.H := by
    intro hmem
    exact (Finset.mem_sdiff.mp hi).2
      ((h.partition.mem_occurrencesInCommonCore_iff h.H i).2 hmem)
  exact hnotcore hcore

/-- For nontrivial `H`, the labelled occurrences outside the common core are
exactly the disjoint union of the outside-core pieces of the replacement
cells. -/
theorem GMOTheoremEOutput.outsideCommonCore_eq_biUnion_outsideCoreCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H ≠ ⊥) :
    (Finset.univ : Selection xs) \ h.partition.occurrencesInCommonCore h.H =
      Finset.univ.biUnion (h.partition.outsideCoreCell h.H) := by
  classical
  ext i
  constructor
  · intro hi
    have hisupport := h.outsideCommonCore_subset_support hH hi
    rw [Theorem21SetPartition.support] at hisupport
    obtain ⟨c, _, hicell⟩ := Finset.mem_biUnion.mp hisupport
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ c, ?_⟩
    exact (h.partition.mem_outsideCoreCell_iff h.H c i).2
      ⟨hicell, fun hcore ↦ (Finset.mem_sdiff.mp hi).2
        ((h.partition.mem_occurrencesInCommonCore_iff h.H i).2 hcore)⟩
  · intro hi
    obtain ⟨c, _, hicell⟩ := Finset.mem_biUnion.mp hi
    have hout := (h.partition.mem_outsideCoreCell_iff h.H c i).1 hicell
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun hincore ↦
      hout.2 ((h.partition.mem_occurrencesInCommonCore_iff h.H i).1 hincore)⟩

/-- The parameter `e` of nontrivial-period Theorem E is therefore the exact
number of labelled occurrences of the whole source outside its common core;
repetitions are not collapsed. -/
theorem GMOTheoremEOutput.card_outsideCommonCore
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H ≠ ⊥) :
    ((Finset.univ : Selection xs) \
        h.partition.occurrencesInCommonCore h.H).card =
      h.partition.exceptionDefect h.H := by
  classical
  rw [h.outsideCommonCore_eq_biUnion_outsideCoreCell hH]
  have hdisjoint :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (h.partition.outsideCoreCell h.H) := by
    intro c _ d _ hcd
    change Disjoint (h.partition.outsideCoreCell h.H c)
      (h.partition.outsideCoreCell h.H d)
    rw [Finset.disjoint_left]
    intro i hic hid
    exact (Finset.disjoint_left.mp
      (h.partition.cells_pairwise_disjoint hcd))
      ((h.partition.mem_outsideCoreCell_iff h.H c i).1 hic).1
      ((h.partition.mem_outsideCoreCell_iff h.H d i).1 hid).1
  rw [Finset.card_biUnion hdisjoint]
  exact h.partition.sum_card_outsideCoreCell h.H

/-- The common core is contained in every thickened cell, exactly as its
intersection notation in Theorem E requires. -/
theorem Theorem21SetPartition.commonCore_subset_thickenedCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    P.commonCore H ⊆ P.thickenedCell H c := by
  intro x hx
  exact (P.mem_commonCore_iff H x).1 hx c

/-- Every thickened cell `A_i + H` is closed under translation by `H`. -/
theorem Theorem21SetPartition.add_mem_thickenedCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) {h x : A}
    (hh : h ∈ H) (hx : x ∈ P.thickenedCell H c) :
    h + x ∈ P.thickenedCell H c := by
  classical
  rcases Finset.mem_add.mp hx with ⟨a, ha, k, hk, rfl⟩
  refine Finset.mem_add.mpr ⟨a, ha, h + k, ?_, ?_⟩
  · exact (mem_subgroupFinset H (h + k)).2
      (H.add_mem hh ((mem_subgroupFinset H k).1 hk))
  · ac_rfl

/-- Membership in a thickened cell is invariant under translation by `H`. -/
theorem Theorem21SetPartition.add_mem_thickenedCell_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) {h x : A} (hh : h ∈ H) :
    h + x ∈ P.thickenedCell H c ↔ x ∈ P.thickenedCell H c := by
  constructor
  · intro hx
    have hback := P.add_mem_thickenedCell H c (H.neg_mem hh) hx
    simpa [add_assoc] using hback
  · exact P.add_mem_thickenedCell H c hh

/-- The common core, being an intersection of `H`-thickened cells, is itself
`H`-periodic. -/
theorem Theorem21SetPartition.commonCore_periodic
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    H ≤ AddAction.stabilizer A (P.commonCore H : Set A) := by
  intro h hh
  rw [AddAction.mem_stabilizer_set]
  intro x
  simp only [Finset.mem_coe]
  simp_rw [P.mem_commonCore_iff H]
  constructor
  · intro hx c
    exact (P.add_mem_thickenedCell_iff H c hh).1 (hx c)
  · intro hx c
    exact (P.add_mem_thickenedCell_iff H c hh).2 (hx c)

/-- Pointwise closure form of common-core periodicity. -/
theorem Theorem21SetPartition.add_mem_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) {h x : A} (hh : h ∈ H)
    (hx : x ∈ P.commonCore H) :
    h + x ∈ P.commonCore H := by
  apply (P.mem_commonCore_iff H (h + x)).2
  intro c
  exact P.add_mem_thickenedCell H c hh
    ((P.mem_commonCore_iff H x).1 hx c)

/-- The source number `N = |commonCore| / |H|` really counts cosets at the
endpoint `N = 1`: periodicity forces the common core to be one literal
`H`-coset. -/
theorem Theorem21SetPartition.commonCore_eq_addCosetFinset_of_count_eq_one
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (hN : P.commonCosetCount H = 1) :
    ∃ alpha : A, P.commonCore H = addCosetFinset H alpha := by
  classical
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hdiv : (P.commonCore H).card / Nat.card H = 1 := hN
  have hcoreLower : Nat.card H ≤ (P.commonCore H).card := by
    have hone : 1 ≤ (P.commonCore H).card / Nat.card H := by omega
    have := (Nat.le_div_iff_mul_le hHpos).1 hone
    simpa using this
  have hcoreUpper : (P.commonCore H).card < 2 * Nat.card H := by
    apply (Nat.div_lt_iff_lt_mul hHpos).1
    omega
  obtain ⟨alpha, halpha⟩ :=
    Finset.card_pos.mp (hHpos.trans_le hcoreLower)
  refine ⟨alpha, Finset.Subset.antisymm ?_ ?_⟩
  · intro beta hbeta
    by_contra hbetaCoset
    have hbetaCore : beta ∈ P.commonCore H := hbeta
    have hcosetAlpha : addCosetFinset H alpha ⊆ P.commonCore H := by
      intro x hx
      have hxH := (mem_addCosetFinset_iff H alpha x).1 hx
      have hadd := P.add_mem_commonCore H hxH halpha
      simpa [sub_add_cancel] using hadd
    have hcosetBeta : addCosetFinset H beta ⊆ P.commonCore H := by
      intro x hx
      have hxH := (mem_addCosetFinset_iff H beta x).1 hx
      have hadd := P.add_mem_commonCore H hxH hbetaCore
      simpa [sub_add_cancel] using hadd
    have hunion :
        addCosetFinset H alpha ∪ addCosetFinset H beta ⊆ P.commonCore H :=
      Finset.union_subset hcosetAlpha hcosetBeta
    have hdisjoint := addCosetFinset_disjoint_of_not_mem H hbetaCoset
    have htwo : 2 * Nat.card H ≤ (P.commonCore H).card := by
      calc
        2 * Nat.card H =
            (addCosetFinset H alpha).card + (addCosetFinset H beta).card := by simp [two_mul]
        _ = (addCosetFinset H alpha ∪ addCosetFinset H beta).card :=
          (Finset.card_union_of_disjoint hdisjoint).symm
        _ ≤ (P.commonCore H).card := Finset.card_le_card hunion
    omega
  · intro x hx
    have hxH := (mem_addCosetFinset_iff H alpha x).1 hx
    have hadd := P.add_mem_commonCore H hxH halpha
    simpa [sub_add_cancel] using hadd

/-- The terminal `N = 1` configuration of Theorem E converts, without any
loss of labelled multiplicity, to Theorem 2.1's periodic alternative. -/
theorem GMOTheoremEOutput.nonempty_periodicAlternative_of_terminal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n)
    (hnontrivial : h.H ≠ ⊥) (hproper : h.H < ⊤)
    (hN : h.partition.commonCosetCount h.H = 1)
    (he : h.partition.exceptionDefect h.H ≤ Nat.card (A ⧸ h.H) - 2) :
    Nonempty (GMOTheorem21PeriodicAlternative xs seed n h.partition) := by
  classical
  obtain ⟨alpha, hcore⟩ :=
    h.partition.commonCore_eq_addCosetFinset_of_count_eq_one h.H hN
  refine ⟨{
    H := h.H
    nontrivial := (bot_lt_iff_ne_bot.mpr hnontrivial)
    proper := hproper
    periodic := h.periodic
    e := h.partition.exceptionDefect h.H
    alpha := alpha
    spectrum_card_lower := ?_
    outside_card := ?_
    outside_le := he
  }⟩
  · have hbound := h.card_lower
    rw [hN] at hbound
    simpa using hbound
  · have houtside := h.card_outsideCommonCore hnontrivial
    have hoccurrences :
        h.partition.occurrencesInCommonCore h.H =
          occurrencesInAddCoset xs h.H alpha := by
      ext i
      rw [h.partition.mem_occurrencesInCommonCore_iff,
        mem_occurrencesInAddCoset_iff, hcore,
        mem_addCosetFinset_iff]
    rwa [hoccurrences] at houtside

omit [AddCommGroup A] [Fintype A] in
/-- Summing pointwise natural-number differences is exact once the removed
constant is restored once per index. -/
theorem sum_sub_const_add_card_mul
    {ι : Type*} (s : Finset ι) (f : ι → ℕ) (k : ℕ)
    (hk : ∀ i ∈ s, k ≤ f i) :
    (∑ i ∈ s, (f i - k)) + s.card * k = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hka : k ≤ f a := hk a (by simp)
      have hks : ∀ i ∈ s, k ≤ f i := by
        intro i hi
        exact hk i (by simp [hi])
      have hih := ih hks
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      rw [Nat.succ_mul, ← hih]
      omega

@[simp]
theorem subgroupFinset_bot :
    subgroupFinset (⊥ : AddSubgroup A) = ({0} : Finset A) := by
  classical
  ext x
  simp

@[simp]
theorem Theorem21SetPartition.thickenedCell_bot
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (c : Fin n) :
    P.thickenedCell (⊥ : AddSubgroup A) c = P.valueCell c := by
  classical
  simp only [Theorem21SetPartition.thickenedCell, subgroupFinset_bot]
  change P.valueCell c + (0 : Finset A) = P.valueCell c
  exact add_zero _

/-- With trivial period, the common core is literally contained in every
unthickened value cell. -/
theorem Theorem21SetPartition.commonCore_bot_subset_valueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (c : Fin n) :
    P.commonCore (⊥ : AddSubgroup A) ⊆ P.valueCell c := by
  simpa only [P.thickenedCell_bot c] using
    P.commonCore_subset_thickenedCell (⊥ : AddSubgroup A) c

@[simp]
theorem Theorem21SetPartition.commonCosetCount_bot
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.commonCosetCount (⊥ : AddSubgroup A) =
      (P.commonCore (⊥ : AddSubgroup A)).card := by
  simp [Theorem21SetPartition.commonCosetCount]

/-- At trivial period, Theorem E's exception defect plus the uniform common
core incidence recovers the exact replacement length. -/
theorem Theorem21SetPartition.exceptionDefect_bot_add_core_incidence
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.exceptionDefect (⊥ : AddSubgroup A) +
        n * (P.commonCore (⊥ : AddSubgroup A)).card = m := by
  classical
  let k := (P.commonCore (⊥ : AddSubgroup A)).card
  have hk (c : Fin n) : k ≤ (P.valueCell c).card := by
    exact Finset.card_le_card (P.commonCore_bot_subset_valueCell c)
  have hinter (c : Fin n) :
      (P.valueCell c ∩ P.commonCore (⊥ : AddSubgroup A)).card = k := by
    rw [Finset.inter_eq_right.mpr (P.commonCore_bot_subset_valueCell c)]
  have hsum := sum_sub_const_add_card_mul (Finset.univ : Finset (Fin n))
    (fun c ↦ (P.valueCell c).card) k (by
      intro c _
      exact hk c)
  simpa [Theorem21SetPartition.exceptionDefect,
    Theorem21SetPartition.cellExceptionDefect, hinter, k,
    P.sum_card_valueCell, Nat.mul_comm] using hsum

/-- The trivial-period specialization of Theorem E's numerical bound is at
least the large-branch threshold `|S'| - n + 1`.  The empty-common-core case
is kept separate because natural subtraction makes `N - 1` truncate. -/
theorem GMOTheoremEOutput.card_lower_of_H_eq_bot
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H = ⊥)
    (hlen : n ≤ seed.card) :
    seed.card - n + 1 ≤ h.partition.sumset.card := by
  have hbound := h.card_lower
  rw [hH] at hbound
  simp only [h.partition.commonCosetCount_bot, Nat.card_unique, mul_one] at hbound
  have hincidence := h.partition.exceptionDefect_bot_add_core_incidence
  cases hcore : (h.partition.commonCore (⊥ : AddSubgroup A)).card with
  | zero =>
      rw [hcore, mul_zero, add_zero] at hincidence
      rw [hcore] at hbound
      simp only [Nat.zero_sub, zero_mul, zero_add] at hbound
      omega
  | succ k =>
      rw [hcore] at hbound hincidence
      simp only [Nat.succ_sub_one] at hbound
      simp only [Nat.mul_succ] at hincidence
      rw [Nat.mul_comm n k] at hincidence
      omega

/-- Thus the trivial-period output of Theorem E is already branch (i) of
Theorem 2.1, with no change to its numerical threshold. -/
theorem GMOTheoremEOutput.largeAlternative_of_H_eq_bot
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H = ⊥)
    (hlen : n ≤ seed.card) :
    GMOTheorem21LargeAlternative xs seed n h.partition := by
  refine ⟨?_⟩
  exact (min_le_right (Nat.card A) (seed.card - n + 1)).trans
    (h.card_lower_of_H_eq_bot hH hlen)

omit [Fintype A] in
/-- Nonempty cells make the full-layer replacement sumset nonempty. -/
theorem Theorem21SetPartition.sumset_nonempty
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.sumset.Nonempty := by
  classical
  unfold Theorem21SetPartition.sumset fullLayerSumSpectrum
  exact layerSubsumSpectrum_nonempty P.valueCells P.valueCells_nonempty
    P.valueCells.length le_rfl

/-- In Theorem E, a top stabilizing subgroup forces the replacement sumset
itself to be the whole ambient group. -/
theorem GMOTheoremEOutput.sumset_eq_univ_of_H_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H = ⊤) :
    h.partition.sumset = Finset.univ := by
  classical
  have hstabTop :
      AddAction.stabilizer A (h.partition.sumset : Set A) = ⊤ := by
    apply top_unique
    simpa [hH] using h.periodic
  by_contra hne
  have hlt := stabilizer_lt_top_of_finset_nonempty_ne_univ
    h.partition.sumset h.partition.sumset_nonempty hne
  rw [hstabTop] at hlt
  exact (lt_irrefl _ hlt)

/-- The top-period output of Theorem E is also branch (i) of Theorem 2.1. -/
theorem GMOTheoremEOutput.largeAlternative_of_H_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H = ⊤) :
    GMOTheorem21LargeAlternative xs seed n h.partition := by
  classical
  refine ⟨?_⟩
  have hsumset := h.sumset_eq_univ_of_H_eq_top hH
  rw [hsumset, Finset.card_univ]
  simpa only [Nat.card_eq_fintype_card] using
    min_le_left (Nat.card A) (seed.card - n + 1)

/-- Theorem E plus only the proper-nontrivial `N,e` induction kernel yields
the full occurrence-faithful Theorem 2.1 statement.  Trivial and top periods,
the choice of the terminal coset, and the whole-source exception count are
all discharged by proved lemmas above. -/
theorem GMOTheorem21Statement_of_theoremE_and_properInduction
    (hE : GMOTheoremEStatement A)
    (hInduction : GMOTheorem25ProperInductionStatement A) :
    GMOTheorem21Statement A := by
  intro data xs seed n hdstar hcap hlen
  obtain ⟨out⟩ := hE xs seed n hcap hlen
  by_cases hbot : out.H = ⊥
  · exact ⟨{
      partition := out.partition
      alternative := Or.inl (out.largeAlternative_of_H_eq_bot hbot hlen)
    }⟩
  by_cases htop : out.H = ⊤
  · exact ⟨{
      partition := out.partition
      alternative := Or.inl (out.largeAlternative_of_H_eq_top htop)
    }⟩
  have hproper : out.H < ⊤ := lt_top_iff_ne_top.mpr htop
  exact hInduction data xs seed n hdstar hcap hlen out hbot hproper

/-- Hence the top-subgroup case already forces the exact ordinary spectrum
to be the whole ambient group. -/
theorem GMOTheoremEOutput.ordinarySpectrumFull_of_H_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H = ⊤) :
    OrdinarySpectrumFull xs n := by
  classical
  have hsumsetUniv := h.sumset_eq_univ_of_H_eq_top hH
  rw [ordinarySpectrumFull_iff_exactSpectrum_eq_univ]
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  apply h.partition.sumset_subset_ordinaryExactSpectrum
  rw [hsumsetUniv]
  exact Finset.mem_univ y

/-- Branch (ii) gives exactly the canonical labelled coset-count inequality
used by the ordinary structural GMO consumer. -/
theorem GMOTheorem21PeriodicAlternative.coset_card_lower
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {P : Theorem21SetPartition xs n seed.card}
    (h : GMOTheorem21PeriodicAlternative xs seed n P)
    (hsourceWide : Nat.card (A ⧸ h.H) ≤ xs.length) :
    xs.length - Nat.card (A ⧸ h.H) + 2 ≤
      (occurrencesInAddCoset xs h.H h.alpha).card := by
  classical
  let C : Selection xs := occurrencesInAddCoset xs h.H h.alpha
  have hC : C ⊆ (Finset.univ : Selection xs) := Finset.subset_univ C
  have hcount : h.e + C.card = xs.length := by
    have hpartition := Finset.card_sdiff_add_card_eq_card hC
    rw [h.outside_card] at hpartition
    simpa [C] using hpartition
  have hquotient : 2 ≤ Nat.card (A ⧸ h.H) :=
    two_le_natCard_quotient_of_lt_top h.H h.proper
  have headd : h.e + 2 ≤ Nat.card (A ⧸ h.H) :=
    (Nat.le_sub_iff_add_le hquotient).mp h.outside_le
  dsimp only [C] at hcount ⊢
  rw [← hcount]
  omega

/-- Branch (ii), with its nontriviality and periodicity data retained, maps
to the existing occurrence-labelled concentration structure. -/
noncomputable def GMOTheorem21PeriodicAlternative.toOrdinaryGMOConcentration
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {P : Theorem21SetPartition xs n seed.card}
    (h : GMOTheorem21PeriodicAlternative xs seed n P)
    (hsourceWide : Nat.card (A ⧸ h.H) ≤ xs.length) :
    OrdinaryGMOConcentration xs where
  K := h.H
  strict := h.proper
  alpha := h.alpha
  selected := occurrencesInAddCoset xs h.H h.alpha
  sourceCoset := by
    intro i hi
    exact (mem_occurrencesInAddCoset_iff xs h.H h.alpha i).1 hi
  card_lower := h.coset_card_lower hsourceWide

/-- If branch (i)'s numerical minimum reaches the ambient group order, its
sumset is all of `A`, and the occurrence exact-`n` spectrum is therefore all
of `A` as well. -/
theorem GMOTheorem21LargeAlternative.ordinarySpectrumFull
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {P : Theorem21SetPartition xs n seed.card}
    (h : GMOTheorem21LargeAlternative xs seed n P)
    (hwide : Nat.card A ≤ seed.card - n + 1) :
    OrdinarySpectrumFull xs n := by
  classical
  have hcardLower : Nat.card A ≤ P.sumset.card := by
    have hbound := h.card_lower
    rw [min_eq_left hwide] at hbound
    exact hbound
  have hcardUpper : P.sumset.card ≤ Nat.card A := by
    simpa using Finset.card_le_univ P.sumset
  have hcard : P.sumset.card = Fintype.card A := by
    simpa using Nat.le_antisymm hcardUpper hcardLower
  have hsumset : P.sumset = Finset.univ :=
    Finset.eq_univ_of_card P.sumset hcard
  rw [ordinarySpectrumFull_iff_exactSpectrum_eq_univ]
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  apply P.sumset_subset_ordinaryExactSpectrum
  rw [hsumset]
  exact Finset.mem_univ y

/-- The exact Theorem 2.1 output gives the current full/concentrated consumer
alternative whenever the large branch has enough width to force cardinality
`|A|`. -/
theorem GMOTheorem21Output.full_or_concentrated
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheorem21Output xs seed n)
    (hwide : Nat.card A ≤ seed.card - n + 1)
    (hsourceWide : Nat.card A ≤ xs.length) :
    OrdinarySpectrumFull xs n ∨ Nonempty (OrdinaryGMOConcentration xs) := by
  rcases h.alternative with hlarge | hperiodic
  · exact Or.inl (hlarge.ordinarySpectrumFull hwide)
  · obtain ⟨hperiodic⟩ := hperiodic
    have hquotientLe : Nat.card (A ⧸ hperiodic.H) ≤ Nat.card A :=
      Nat.le_of_dvd Nat.card_pos hperiodic.H.card_quotient_dvd_card
    exact Or.inr
      ⟨hperiodic.toOrdinaryGMOConcentration
        (hquotientLe.trans hsourceWide)⟩

/-- Honest proved DGM endpoint for a source whose own occurrences already
satisfy the setpartition criterion.  This is strictly weaker than Theorem
2.1: it does not perform the replacement/structural induction, but it does
construct the labelled setpartition, its exact spectrum embedding, and the
full-layer DGM inequality without any new assumption. -/
theorem exists_fullSource_theorem21SetPartition_with_dgm
    [DecidableEq A]
    (xs : List A) (n : ℕ)
    (hcap : OccurrenceMultiplicityAtMost xs n)
    (hlen : n ≤ xs.length) :
    ∃ P : Theorem21SetPartition xs n xs.length,
      P.sumset ⊆ ordinaryExactSpectrum xs n ∧
        DGMSetpartitionBound P.valueCells n := by
  classical
  obtain ⟨Q⟩ := exists_occurrenceSetPartition xs n hcap hlen
  let P : Theorem21SetPartition xs n xs.length :=
    Q.toTheorem21SetPartition
  refine ⟨P, P.sumset_subset_ordinaryExactSpectrum, ?_⟩
  have hdgm := dgmSetpartitionBound_full P.valueCells P.valueCells_nonempty
  simpa using hdgm

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.sumset_subset_ordinaryExactSpectrum
#print axioms GaoLean.GMOTheorem21PeriodicAlternative.coset_card_lower
#print axioms GaoLean.GMOTheorem21LargeAlternative.ordinarySpectrumFull
#print axioms GaoLean.GMOTheorem21Output.full_or_concentrated
#print axioms GaoLean.exists_fullSource_theorem21SetPartition_with_dgm
#print axioms GaoLean.Theorem21SetPartition.commonCore_periodic
#print axioms GaoLean.GMOTheoremEOutput.card_outsideCommonCore
#print axioms GaoLean.GMOTheoremEOutput.card_lower_of_H_eq_bot
#print axioms GaoLean.GMOTheoremEOutput.largeAlternative_of_H_eq_top
#print axioms GaoLean.Theorem21SetPartition.commonCore_eq_addCosetFinset_of_count_eq_one
#print axioms GaoLean.GMOTheoremEOutput.nonempty_periodicAlternative_of_terminal
#print axioms GaoLean.GMOTheorem21Statement_of_theoremE_and_properInduction
