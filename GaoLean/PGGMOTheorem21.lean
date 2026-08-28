import GaoLean.PGSetpartitionOccurrences
import GaoLean.PGGMOOrdinarySource
import GaoLean.PGCapacity
import GaoLean.PGScherk
import GaoLean.PGDavenportConvolution
import GaoLean.PGDGMCore

/-!
# Occurrence-faithful statement of the GMO partition theorem

This file freezes Theorem 2.1 and the Section 5 proof of
Grynkiewicz--Marchan--Ordaz, *Representation of finite abelian group
elements by subsequence sums* (arXiv:0806.0309; DOI 10.5802/jtnb.689),
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

/-- A coloring of a finite family is proper on the fibers of its value map. -/
def FiberColoringProper {X V : Type*} (value : X → V) (n : ℕ)
    (color : X → Fin n) : Prop :=
  ∀ x y, value x = value y → color x = color y → x = y

/-- Fiberwise multiplicity at most `n`, together with at least `n` labelled
objects, gives a surjective proper `Fin n` coloring.  This is the finite
combinatorial core of the setpartition criterion, stated independently of
list positions so that it applies verbatim to a selected subsequence. -/
theorem exists_surjective_fiberColoring
    {X V : Type*} [Fintype X] [DecidableEq V]
    (value : X → V) (n : ℕ)
    (hcap : ∀ a : V,
      ((Finset.univ : Finset X).filter fun x ↦ value x = a).card ≤ n)
    (hlen : n ≤ Fintype.card X) :
    ∃ color : X → Fin n,
      Function.Surjective color ∧ FiberColoringProper value n color := by
  classical
  let orderEquiv : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  letI : LinearOrder X := LinearOrder.lift' orderEquiv orderEquiv.injective
  let before (x : X) : Finset X :=
    Finset.univ.filter fun y ↦ value y = value x ∧ y < x
  have hbefore_lt (x : X) :
      (before x).card <
        ((Finset.univ : Finset X).filter fun y ↦ value y = value x).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro y hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2.1⟩
    · intro heq
      have hxFiber : x ∈
          (Finset.univ : Finset X).filter fun y ↦ value y = value x := by simp
      have hxBefore : x ∉ before x := by simp [before]
      exact hxBefore (heq ▸ hxFiber)
  let color₀ : X → Fin n := fun x ↦
    ⟨(before x).card, (hbefore_lt x).trans_le (hcap (value x))⟩
  have hcolor₀ : FiberColoringProper value n color₀ := by
    intro x y hvalue hxy
    have hcard : (before x).card = (before y).card := congrArg Fin.val hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxylt | hyxlt
    · have hstrict : before x ⊂ before y := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · intro z hz
          have hz' := (Finset.mem_filter.mp hz).2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hz'.1.trans hvalue, hz'.2.trans hxylt⟩
        · intro heq
          have hxyMem : x ∈ before y := by
            simp [before, hvalue, hxylt]
          have hxx : x ∉ before x := by simp [before]
          exact hxx (heq ▸ hxyMem)
      exact (ne_of_lt (Finset.card_lt_card hstrict)) hcard
    · have hstrict : before y ⊂ before x := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · intro z hz
          have hz' := (Finset.mem_filter.mp hz).2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hz'.1.trans hvalue.symm, hz'.2.trans hyxlt⟩
        · intro heq
          have hyxMem : y ∈ before x := by
            simp [before, hvalue, hyxlt]
          have hyy : y ∉ before y := by simp [before]
          exact hyy (heq ▸ hyxMem)
      exact (ne_of_gt (Finset.card_lt_card hstrict)) hcard
  let good : Finset (X → Fin n) :=
    Finset.univ.filter fun color ↦ FiberColoringProper value n color
  have hcolor₀good : color₀ ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcolor₀
  obtain ⟨color, hcolorGood, hmax⟩ := Finset.exists_max_image good
    (fun color ↦ (Finset.univ.image color).card) ⟨color₀, hcolor₀good⟩
  have hproper : FiberColoringProper value n color :=
    (Finset.mem_filter.mp hcolorGood).2
  refine ⟨color, ?_, hproper⟩
  by_contra hnotSurj
  obtain ⟨missing, hmissing⟩ :
      ∃ missing : Fin n, ∀ x : X, color x ≠ missing := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnotSurj
  have hnotInj : ¬ Function.Injective color := by
    intro hinj
    have hlt := Fintype.card_lt_of_injective_not_surjective color hinj hnotSurj
    simp only [Fintype.card_fin] at hlt
    omega
  obtain ⟨x, y, hcolorxy, hxy⟩ := Function.not_injective_iff.mp hnotInj
  let recolor : X → Fin n := Function.update color x missing
  have hrecolorProper : FiberColoringProper value n recolor := by
    intro a b habValue habColor
    by_cases hax : a = x
    · subst a
      by_cases hbx : b = x
      · exact hbx.symm
      · exfalso
        have hmissingb : missing = color b := by
          simpa [recolor, hbx] using habColor
        exact hmissing b hmissingb.symm
    · by_cases hbx : b = x
      · subst b
        exfalso
        have hamissing : color a = missing := by
          simpa [recolor, hax] using habColor
        exact hmissing a hamissing
      · apply hproper a b habValue
        simpa [recolor, hax, hbx] using habColor
  have hrecolorGood : recolor ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrecolorProper
  have hrangeSubset :
      Finset.univ.image color ⊆ Finset.univ.image recolor := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨z, -, rfl⟩
    by_cases hzx : z = x
    · subst z
      refine Finset.mem_image.mpr ⟨y, Finset.mem_univ _, ?_⟩
      simp [recolor, hxy.symm, hcolorxy]
    · exact Finset.mem_image.mpr
        ⟨z, Finset.mem_univ _, by simp [recolor, hzx]⟩
  have hmissingRecolor : missing ∈ Finset.univ.image recolor := by
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by simp [recolor]⟩
  have hmissingColor : missing ∉ Finset.univ.image color := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨z, -, hz⟩
    exact hmissing z hz
  have hrangeStrict : Finset.univ.image color ⊂
      Finset.univ.image recolor := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hrangeSubset, ?_⟩
    intro heq
    exact hmissingColor (heq ▸ hmissingRecolor)
  have hcardLt := Finset.card_lt_card hrangeStrict
  have hcardMax := hmax recolor hrecolorGood
  omega

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

/-- A color cell inside a labelled selected subsequence.  The existential
membership proof makes the definition independent of proof terms. -/
noncomputable def selectedColorCell
    {xs : List A} (seed : Selection xs) {n : ℕ}
    (color : (↥seed) → Fin n) (c : Fin n) : Selection xs := by
  classical
  exact seed.filter fun i ↦ ∃ hi : i ∈ seed, color ⟨i, hi⟩ = c

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem mem_selectedColorCell_iff
    {xs : List A} (seed : Selection xs) {n : ℕ}
    (color : (↥seed) → Fin n) (c : Fin n) (i : Occurrence xs) :
    i ∈ selectedColorCell seed color c ↔
      ∃ hi : i ∈ seed, color ⟨i, hi⟩ = c := by
  classical
  simp [selectedColorCell]

omit [AddCommGroup A] [Fintype A] in
/-- The literal selected-subsequence form of the setpartition criterion.
Unlike the earlier full-source constructor, its support has exactly
`seed.card` occurrences and may be a proper subsequence of `xs`. -/
theorem exists_selected_theorem21SetPartition
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (hcap : SelectionMultiplicityAtMost xs seed n)
    (hlen : n ≤ seed.card) :
    ∃ P : Theorem21SetPartition xs n seed.card,
      Finset.univ.biUnion P.cells = seed := by
  classical
  let value : (↥seed) → A := fun i ↦ occurrenceValue xs i.1
  have hcap' (a : A) :
      ((Finset.univ : Finset (↥seed)).filter fun i ↦ value i = a).card ≤ n := by
    change (seed.attach.filter fun i : ↥seed ↦
      occurrenceValue xs i.1 = a).card ≤ n
    have heq := Finset.filter_attach
      (fun i : Occurrence xs ↦ occurrenceValue xs i = a) seed
    have hcards := congrArg Finset.card heq
    simp only [Finset.card_map, Finset.card_attach] at hcards
    rw [hcards]
    exact hcap a
  have hcard : Fintype.card (↥seed) = seed.card := Fintype.card_coe seed
  obtain ⟨color, hsurj, hproper⟩ :=
    exists_surjective_fiberColoring value n hcap' (hcard ▸ hlen)
  let cells : Fin n → Selection xs := selectedColorCell seed color
  refine ⟨{
    cells := cells
    cells_nonempty := ?_
    cells_pairwise_disjoint := ?_
    value_injective := ?_
    card_support := ?_
  }, ?_⟩
  · intro c
    obtain ⟨i, hi⟩ := hsurj c
    exact ⟨i.1, (mem_selectedColorCell_iff seed color c i.1).2
      ⟨i.2, hi⟩⟩
  · intro c d hcd
    rw [Finset.disjoint_left]
    intro i hic hid
    obtain ⟨hiSeed, hicColor⟩ :=
      (mem_selectedColorCell_iff seed color c i).1 hic
    obtain ⟨hiSeed', hidColor⟩ :=
      (mem_selectedColorCell_iff seed color d i).1 hid
    apply hcd
    rw [← hicColor, ← hidColor]
  · intro c i hi j hj hij
    obtain ⟨hiSeed, hiColor⟩ :=
      (mem_selectedColorCell_iff seed color c i).1 hi
    obtain ⟨hjSeed, hjColor⟩ :=
      (mem_selectedColorCell_iff seed color c j).1 hj
    have hsub : (⟨i, hiSeed⟩ : ↥seed) = ⟨j, hjSeed⟩ := by
      apply hproper
      · exact hij
      · exact hiColor.trans hjColor.symm
    exact congrArg Subtype.val hsub
  · have hunion : Finset.univ.biUnion cells = seed := by
      ext i
      constructor
      · intro hi
        obtain ⟨c, -, hic⟩ := Finset.mem_biUnion.mp hi
        exact ((mem_selectedColorCell_iff seed color c i).1 hic).1
      · intro hi
        apply Finset.mem_biUnion.mpr
        refine ⟨color ⟨i, hi⟩, Finset.mem_univ _, ?_⟩
        exact (mem_selectedColorCell_iff seed color (color ⟨i, hi⟩) i).2
          ⟨hi, rfl⟩
    rw [hunion]
  · ext i
    constructor
    · intro hi
      obtain ⟨c, -, hic⟩ := Finset.mem_biUnion.mp hi
      exact ((mem_selectedColorCell_iff seed color c i).1 hic).1
    · intro hi
      apply Finset.mem_biUnion.mpr
      refine ⟨color ⟨i, hi⟩, Finset.mem_univ _, ?_⟩
      exact (mem_selectedColorCell_iff seed color (color ⟨i, hi⟩) i).2
        ⟨hi, rfl⟩

omit [AddCommGroup A] [Fintype A] in
@[ext]
theorem Theorem21SetPartition.ext_cells
    {xs : List A} {n m : ℕ}
    {P Q : Theorem21SetPartition xs n m}
    (h : ∀ c, P.cells c = Q.cells c) : P = Q := by
  cases P
  cases Q
  congr
  funext c
  exact h c

omit [AddCommGroup A] [Fintype A] in
noncomputable instance theorem21SetPartitionFinite
    {xs : List A} {n m : ℕ} :
    Finite (Theorem21SetPartition xs n m) := by
  apply Finite.of_injective
    (fun P : Theorem21SetPartition xs n m ↦ P.cells)
  intro P Q hcells
  apply Theorem21SetPartition.ext_cells
  exact congrFun hcells

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

omit [Fintype A] in
/-- Full-layer sumsets are invariant under permutation of their layers. -/
theorem fullLayerSumSpectrum_eq_of_perm [DecidableEq A]
    {L R : List (Finset A)}
    (h : L.Perm R) : fullLayerSumSpectrum L = fullLayerSumSpectrum R := by
  induction h with
  | nil => rfl
  | cons C _ ih => simp [fullLayerSumSpectrum_cons, ih]
  | swap B C T =>
      simp only [fullLayerSumSpectrum_cons]
      ac_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [AddCommGroup A] [Fintype A] in
/-- Relabel the ordered cells by a finite permutation.  Occurrences and their
support are unchanged; only the cell indices move. -/
noncomputable def Theorem21SetPartition.reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) : Theorem21SetPartition xs n m := by
  classical
  refine {
    cells := fun c ↦ P.cells (sigma c)
    cells_nonempty := fun c ↦ P.cells_nonempty (sigma c)
    cells_pairwise_disjoint := ?_
    value_injective := fun c ↦ P.value_injective (sigma c)
    card_support := ?_
  }
  · intro c d hcd
    exact P.cells_pairwise_disjoint fun h ↦ hcd (sigma.injective h)
  · have hunion :
        Finset.univ.biUnion (fun c ↦ P.cells (sigma c)) =
          Finset.univ.biUnion P.cells := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨c, hic⟩
        exact ⟨sigma c, hic⟩
      · rintro ⟨d, hid⟩
        exact ⟨sigma.symm d, by simpa using hid⟩
    rw [hunion]
    exact P.card_support

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.cells_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (c : Fin n) :
    (P.reindex sigma).cells c = P.cells (sigma c) := by
  rfl

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.valueCell_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (c : Fin n) :
    (P.reindex sigma).valueCell c = P.valueCell (sigma c) := by
  rfl

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.support_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) :
    (P.reindex sigma).support = P.support := by
  classical
  ext i
  simp only [Theorem21SetPartition.support, Finset.mem_biUnion,
    Finset.mem_univ, true_and, P.cells_reindex]
  constructor
  · rintro ⟨c, hic⟩
    exact ⟨sigma c, hic⟩
  · rintro ⟨d, hid⟩
    exact ⟨sigma.symm d, by simpa using hid⟩

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.reindex_symm_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) :
    (P.reindex sigma).reindex sigma.symm = P := by
  apply Theorem21SetPartition.ext_cells
  intro c
  simp

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.reindex_reindex_symm
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) :
    (P.reindex sigma.symm).reindex sigma = P := by
  apply Theorem21SetPartition.ext_cells
  intro c
  simp

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.reindex_injective
    {xs : List A} {n m : ℕ} (sigma : Equiv.Perm (Fin n)) :
    Function.Injective
      (fun P : Theorem21SetPartition xs n m ↦ P.reindex sigma) := by
  intro P Q h
  have := congrArg (fun R : Theorem21SetPartition xs n m ↦
    R.reindex sigma.symm) h
  simpa using this

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.valueCells_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) :
    (P.reindex sigma).valueCells =
      List.ofFn ((fun c : Fin n ↦ P.valueCell c) ∘ sigma) := by
  classical
  simp [Theorem21SetPartition.valueCells, Function.comp_def]

omit [Fintype A] in
theorem Theorem21SetPartition.sumset_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) :
    (P.reindex sigma).sumset = P.sumset := by
  classical
  unfold Theorem21SetPartition.sumset
  rw [P.valueCells_reindex sigma]
  exact fullLayerSumSpectrum_eq_of_perm (sigma.ofFn_comp_perm _)

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

/-- The quotient-incidence quantity maximized in the first nontrivial stage
of the Partition Theorem's iterated extremal construction. -/
noncomputable def Theorem21SetPartition.stabilizerQuotientIncidence
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) : ℕ := by
  classical
  exact ∑ c : Fin n,
    (stabilizerQuotientLayer P.sumset (P.valueCell c)).card

/-- Number of replacement occurrences already captured outside the common
core for the stabilizer of the replacement sumset. -/
noncomputable def Theorem21SetPartition.capturedOutsideCommonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) : ℕ := by
  classical
  let H : AddSubgroup A := AddAction.stabilizer A (P.sumset : Set A)
  exact (P.support.filter fun i ↦
    occurrenceValue xs i ∉ P.commonCore H).card

/-! ### Source-faithful Theorem E base family -/

/-- The actual input of the Partition Theorem's Theorem E is an already
chosen occurrence-faithful `n`-setpartition of `S'`, together with one fixed
anchor occurrence in every cell.  The multiplicity and length hypotheses are
used earlier to construct this object; they are not hypotheses of Theorem E
itself. -/
structure GMOTheoremEInput
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  initial : Theorem21SetPartition xs n seed.card
  initial_support : initial.support = seed
  anchor : Fin n → Occurrence xs
  anchor_mem : ∀ c, anchor c ∈ initial.cells c

omit [AddCommGroup A] [Fintype A] in
@[ext]
theorem GMOTheoremEInput.ext
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I J : GMOTheoremEInput xs seed n}
    (hinitial : I.initial = J.initial) (hanchor : I.anchor = J.anchor) :
    I = J := by
  cases I
  cases J
  cases hinitial
  cases hanchor
  rfl

/-- Literal `Lambda_0` admissibility in dissertation Definition 1: the
initial full sumset is contained in the replacement full sumset, and every
distinguished anchor value remains in its indexed cell. -/
def GMOReplacementAdmissible
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n)
    (P : Theorem21SetPartition xs n seed.card) : Prop :=
  I.initial.sumset ⊆ P.sumset ∧
    ∀ c : Fin n,
      occurrenceValue xs (I.anchor c) ∈ P.valueCell c

omit [Fintype A] in
/-- Reindex the source partition and its anchors together.  This is the
source-faithful transport required when Lemma 5 permutes only tail cells. -/
noncomputable def GMOTheoremEInput.reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (sigma : Equiv.Perm (Fin n)) :
    GMOTheoremEInput xs seed n := by
  classical
  refine {
    initial := I.initial.reindex sigma
    initial_support := ?_
    anchor := fun c ↦ I.anchor (sigma c)
    anchor_mem := ?_
  }
  · rw [I.initial.support_reindex, I.initial_support]
  · intro c
    simpa using I.anchor_mem (sigma c)

omit [Fintype A] in
theorem GMOReplacementAdmissible.reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {P : Theorem21SetPartition xs n seed.card}
    (hP : GMOReplacementAdmissible I P)
    (sigma : Equiv.Perm (Fin n)) :
    GMOReplacementAdmissible (I.reindex sigma) (P.reindex sigma) := by
  classical
  constructor
  · simpa [GMOTheoremEInput.reindex,
      Theorem21SetPartition.sumset_reindex] using hP.1
  · intro c
    simpa [GMOTheoremEInput.reindex] using hP.2 (sigma c)

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem GMOTheoremEInput.reindex_symm_reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (sigma : Equiv.Perm (Fin n)) :
    (I.reindex sigma).reindex sigma.symm = I := by
  apply GMOTheoremEInput.ext
  · simp [GMOTheoremEInput.reindex]
  · funext c
    simp [GMOTheoremEInput.reindex]

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem GMOTheoremEInput.reindex_reindex_symm
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (sigma : Equiv.Perm (Fin n)) :
    (I.reindex sigma.symm).reindex sigma = I := by
  simpa using I.reindex_symm_reindex sigma.symm

omit [Fintype A] in
/-- The initial partition belongs to its literal source base family. -/
theorem GMOTheoremEInput.initial_admissible
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) :
    GMOReplacementAdmissible I I.initial := by
  classical
  constructor
  · exact Finset.Subset.rfl
  · intro c
    exact Finset.mem_image.mpr ⟨I.anchor c, I.anchor_mem c, rfl⟩

/-- The ordered tail `A_{r+1}, ..., A_n` of value cells (with zero-based
Lean index `r`). -/
noncomputable def Theorem21SetPartition.tailValueCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (r : ℕ) : List (Finset A) :=
  P.valueCells.drop r

/-- The tail sumset used at stage `r` of Definition 1. -/
noncomputable def Theorem21SetPartition.tailSumset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (r : ℕ) : Finset A := by
  classical
  exact fullLayerSumSpectrum (P.tailValueCells r)

/-- Sum of the cardinalities of all cell images modulo a fixed subgroup.
This is Definition 1's first maximized quantity at each positive stage. -/
noncomputable def Theorem21SetPartition.quotientIncidenceAt
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) : ℕ := by
  classical
  exact ∑ c : Fin n, (quotientLayer H (P.valueCell c)).card

/-- The cellwise quotient-image constraint in Definition 1's `Υ_r` stage. -/
def Theorem21SetPartition.quotientImagesIncluded
    {xs : List A} {n m : ℕ} (F P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) : Prop :=
  ∀ c : Fin n, quotientLayer H (F.valueCell c) ⊆
    quotientLayer H (P.valueCell c)

/-- The first three finite lexicographic stages of Definition 1 in the
source Partition Theorem, specialized to ordinary weights and with no fixed
distinguished elements: maximize the full sumset, then quotient incidence
at its stabilizer while keeping that sumset fixed, then the number of
outside-core source occurrences captured by the replacement. -/
structure TheoremEMaximalReplacement
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  partition : Theorem21SetPartition xs n seed.card
  sumset_maximal : ∀ Q : Theorem21SetPartition xs n seed.card,
    Q.sumset.card ≤ partition.sumset.card
  quotientIncidence_maximal :
    ∀ Q : Theorem21SetPartition xs n seed.card,
      Q.sumset = partition.sumset →
      Q.stabilizerQuotientIncidence ≤
        partition.stabilizerQuotientIncidence
  capturedOutside_maximal :
    ∀ Q : Theorem21SetPartition xs n seed.card,
      Q.sumset = partition.sumset →
      Q.stabilizerQuotientIncidence =
        partition.stabilizerQuotientIncidence →
      Q.capturedOutsideCommonCore ≤
        partition.capturedOutsideCommonCore

/-- The ordinary finite maximal-replacement object exists as soon as the
selected subsequence satisfies the literal setpartition criterion. -/
theorem exists_theoremEMaximalReplacement
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (hcap : SelectionMultiplicityAtMost xs seed n)
    (hlen : n ≤ seed.card) :
    Nonempty (TheoremEMaximalReplacement xs seed n) := by
  classical
  letI : Fintype (Theorem21SetPartition xs n seed.card) := Fintype.ofFinite _
  obtain ⟨initial, _⟩ :=
    exists_selected_theorem21SetPartition xs seed n hcap hlen
  let all : Finset (Theorem21SetPartition xs n seed.card) := Finset.univ
  obtain ⟨P, _hPall, hPmax⟩ := Finset.exists_max_image all
    (fun Q ↦ Q.sumset.card) ⟨initial, Finset.mem_univ _⟩
  let sameSumset := all.filter fun Q ↦ Q.sumset = P.sumset
  have hPsame : P ∈ sameSumset := by simp [sameSumset, all]
  obtain ⟨Q, hQsame, hQmax⟩ := Finset.exists_max_image sameSumset
    Theorem21SetPartition.stabilizerQuotientIncidence ⟨P, hPsame⟩
  have hQsumset : Q.sumset = P.sumset :=
    (Finset.mem_filter.mp hQsame).2
  let sameIncidence := sameSumset.filter fun R ↦
    R.stabilizerQuotientIncidence = Q.stabilizerQuotientIncidence
  have hQincidence : Q ∈ sameIncidence := by
    simp [sameIncidence, hQsame]
  obtain ⟨R, hRsame, hRmax⟩ := Finset.exists_max_image sameIncidence
    Theorem21SetPartition.capturedOutsideCommonCore ⟨Q, hQincidence⟩
  have hRincidence :
      R.stabilizerQuotientIncidence = Q.stabilizerQuotientIncidence :=
    (Finset.mem_filter.mp hRsame).2
  have hRsameSumset : R ∈ sameSumset :=
    (Finset.mem_filter.mp hRsame).1
  have hRsumsetP : R.sumset = P.sumset :=
    (Finset.mem_filter.mp hRsameSumset).2
  refine ⟨{
    partition := R
    sumset_maximal := ?_
    quotientIncidence_maximal := ?_
    capturedOutside_maximal := ?_
  }⟩
  · intro Z
    rw [hRsumsetP]
    exact hPmax Z (Finset.mem_univ Z)
  · intro Z hZsumset
    rw [hRincidence]
    apply hQmax Z
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ Z, ?_⟩
    exact hZsumset.trans hRsumsetP
  · intro Z hZsumset hZincidence
    apply hRmax Z
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ Z, hZsumset.trans hRsumsetP⟩
    · exact hZincidence.trans hRincidence

/-! ### The full finite extremal chain of dissertation Definition 1 -/

/-- One finite `Υ_r` state: its candidate family and the chosen `G_r`.
The candidate family is retained explicitly, so later stages may and usually
do choose a different replacement partition. -/
structure Definition1ExtremalState
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  upsilon : Finset (Theorem21SetPartition xs n seed.card)
  chosen : Theorem21SetPartition xs n seed.card
  chosen_mem : chosen ∈ upsilon

omit [Fintype A] in
/-- Relabel every partition in one finite extremal family, including its
chosen representative. -/
noncomputable def Definition1ExtremalState.reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (state : Definition1ExtremalState xs seed n)
    (sigma : Equiv.Perm (Fin n)) : Definition1ExtremalState xs seed n := by
  classical
  refine {
    upsilon := state.upsilon.image fun P ↦ P.reindex sigma
    chosen := state.chosen.reindex sigma
    chosen_mem := ?_
  }
  exact Finset.mem_image.mpr ⟨state.chosen, state.chosen_mem, rfl⟩

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Definition1ExtremalState.mem_reindex_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (state : Definition1ExtremalState xs seed n)
    (sigma : Equiv.Perm (Fin n))
    (P : Theorem21SetPartition xs n seed.card) :
    P.reindex sigma ∈ (state.reindex sigma).upsilon ↔
      P ∈ state.upsilon := by
  classical
  constructor
  · intro hP
    obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
    have hQP' : Q = P :=
      Theorem21SetPartition.reindex_injective sigma hQP
    exact hQP' ▸ hQ
  · intro hP
    exact Finset.mem_image.mpr ⟨P, hP, rfl⟩

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Definition1ExtremalState.reindex_symm_reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (state : Definition1ExtremalState xs seed n)
    (sigma : Equiv.Perm (Fin n)) :
    (state.reindex sigma).reindex sigma.symm = state := by
  cases state with
  | mk upsilon chosen chosen_mem =>
      simp only [Definition1ExtremalState.reindex]
      congr 1
      ext P
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨Q, ⟨R, hR, rfl⟩, rfl⟩
        simpa using hR
      · intro hP
        refine ⟨P.reindex sigma, ?_, by simp⟩
        exact ⟨P, hP, rfl⟩
      · exact Theorem21SetPartition.reindex_symm_reindex chosen sigma

/-- Exact validity condition for `Υ_0`: the family of all replacements with
maximum full-sumset cardinality. -/
structure Definition1InitialValid
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (state : Definition1ExtremalState xs seed n) : Prop where
  maximal : ∀ P : Theorem21SetPartition xs n seed.card,
    P.sumset.card ≤ state.chosen.sumset.card
  mem_upsilon_iff : ∀ P : Theorem21SetPartition xs n seed.card,
    P ∈ state.upsilon ↔ P.sumset.card = state.chosen.sumset.card

/-- Source-faithful `Upsilon_0`: maximality is taken only inside the literal
`Lambda_0` family determined by the initial sumset and anchors. -/
structure Definition1InitialValidUnder
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n)
    (state : Definition1ExtremalState xs seed n) : Prop where
  chosen_admissible : GMOReplacementAdmissible I state.chosen
  maximal : ∀ P : Theorem21SetPartition xs n seed.card,
    GMOReplacementAdmissible I P →
    P.sumset.card ≤ state.chosen.sumset.card
  mem_upsilon_iff : ∀ P : Theorem21SetPartition xs n seed.card,
    P ∈ state.upsilon ↔
      GMOReplacementAdmissible I P ∧
        P.sumset.card = state.chosen.sumset.card

/-- One positive-stage transition of Definition 1.  At zero-based stage
`r`, `H` is the maximal period of the previous chosen tail beginning at
`r`.  The intermediate witness `F` is chosen after maximizing total quotient
incidence subject to fixing that tail sumset.  The next `Υ` family then fixes
those maximum data, imposes the cellwise quotient-image inclusion from `F`,
and maximizes the following tail beginning at `r+1`. -/
structure Definition1Transition
    {xs : List A} {seed : Selection xs} {n : ℕ} (r : ℕ)
    (previous next : Definition1ExtremalState xs seed n)
    (F : Theorem21SetPartition xs n seed.card) : Prop where
  F_mem_previous : F ∈ previous.upsilon
  F_tail_fixed : F.tailSumset r = previous.chosen.tailSumset r
  incidence_maximal :
    ∀ P : Theorem21SetPartition xs n seed.card,
      P ∈ previous.upsilon →
      P.tailSumset r = previous.chosen.tailSumset r →
      P.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) ≤
        F.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A))
  tail_maximal :
    ∀ P : Theorem21SetPartition xs n seed.card,
      P ∈ previous.upsilon →
      P.tailSumset r = previous.chosen.tailSumset r →
      P.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) =
        F.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) →
      F.quotientImagesIncluded P
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) →
      (P.tailSumset (r + 1)).card ≤
        (next.chosen.tailSumset (r + 1)).card
  mem_next_upsilon_iff :
    ∀ P : Theorem21SetPartition xs n seed.card,
      P ∈ next.upsilon ↔
        P ∈ previous.upsilon ∧
        P.tailSumset r = previous.chosen.tailSumset r ∧
        P.quotientIncidenceAt
            (AddAction.stabilizer A
              (previous.chosen.tailSumset r : Set A)) =
          F.quotientIncidenceAt
            (AddAction.stabilizer A
              (previous.chosen.tailSumset r : Set A)) ∧
        F.quotientImagesIncluded P
            (AddAction.stabilizer A
              (previous.chosen.tailSumset r : Set A)) ∧
        (P.tailSumset (r + 1)).card =
          (next.chosen.tailSumset (r + 1)).card

/-- Literal membership predicate for the intermediate `Lambda_{r+1}` family
of Definition 1.  Unlike `next.upsilon`, it stops after fixing the current
tail and maximizing quotient incidence; retaining this seam is essential in
the `l = min (rho + 1) q` proof of Lemma 1. -/
def Definition1Transition.InLambda
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F : Theorem21SetPartition xs n seed.card}
    (_step : Definition1Transition r previous next F)
    (P : Theorem21SetPartition xs n seed.card) : Prop :=
  P ∈ previous.upsilon ∧
    P.tailSumset r = previous.chosen.tailSumset r ∧
    P.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)) =
      F.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A))

omit [Fintype A] in
/-- Every member of the following `Upsilon` lies in the preceding literal
`Lambda`; the converse intentionally need not hold. -/
theorem Definition1Transition.inLambda_of_mem_next
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F P : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous next F)
    (hP : P ∈ next.upsilon) : step.InLambda P := by
  have hPdata := (step.mem_next_upsilon_iff P).1 hP
  exact ⟨hPdata.1, hPdata.2.1, hPdata.2.2.1⟩

omit [Fintype A] in
/-- The initial `Υ_0/G_0` state exists by a genuine finite argmax. -/
theorem exists_definition1InitialState
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (hcap : SelectionMultiplicityAtMost xs seed n)
    (hlen : n ≤ seed.card) :
    ∃ state : Definition1ExtremalState xs seed n,
      Definition1InitialValid state := by
  classical
  letI : Fintype (Theorem21SetPartition xs n seed.card) := Fintype.ofFinite _
  obtain ⟨initial, _⟩ :=
    exists_selected_theorem21SetPartition xs seed n hcap hlen
  let all : Finset (Theorem21SetPartition xs n seed.card) := Finset.univ
  obtain ⟨G, _hGall, hGmax⟩ := Finset.exists_max_image all
    (fun P ↦ P.sumset.card) ⟨initial, Finset.mem_univ _⟩
  let upsilon := all.filter fun P ↦ P.sumset.card = G.sumset.card
  have hGmem : G ∈ upsilon := by simp [upsilon, all]
  refine ⟨{
    upsilon := upsilon
    chosen := G
    chosen_mem := hGmem
  }, ?_⟩
  refine {
    maximal := ?_
    mem_upsilon_iff := ?_
  }
  · intro P
    exact hGmax P (Finset.mem_univ P)
  · intro P
    simp [upsilon, all]

omit [Fintype A] in
/-- The literal source `Upsilon_0` exists by a finite argmax over
`GMOReplacementAdmissible I`; the initial partition witnesses that this
family is nonempty. -/
theorem exists_definition1InitialStateUnder
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) :
    ∃ state : Definition1ExtremalState xs seed n,
      Definition1InitialValidUnder I state := by
  classical
  letI : Fintype (Theorem21SetPartition xs n seed.card) := Fintype.ofFinite _
  let all : Finset (Theorem21SetPartition xs n seed.card) := Finset.univ
  let lambda0 := all.filter fun P ↦ GMOReplacementAdmissible I P
  have hinitial : I.initial ∈ lambda0 := by
    simp [lambda0, all, I.initial_admissible]
  obtain ⟨G, hGlambda, hGmax⟩ := Finset.exists_max_image lambda0
    (fun P ↦ P.sumset.card) ⟨I.initial, hinitial⟩
  let upsilon := lambda0.filter fun P ↦ P.sumset.card = G.sumset.card
  have hGupsilon : G ∈ upsilon := by simp [upsilon, hGlambda]
  let state : Definition1ExtremalState xs seed n := {
    upsilon := upsilon
    chosen := G
    chosen_mem := hGupsilon
  }
  refine ⟨state, {
    chosen_admissible := ?_
    maximal := ?_
    mem_upsilon_iff := ?_
  }⟩
  · exact (Finset.mem_filter.mp hGlambda).2
  · intro P hPadmissible
    exact hGmax P (Finset.mem_filter.mpr
      ⟨Finset.mem_univ P, hPadmissible⟩)
  · intro P
    simp [state, upsilon, lambda0, all]

omit [Fintype A] in
/-- Every valid finite `Υ_r/G_r` state admits the next
`Λ_{r+1}/F_{r+1}/Υ_{r+1}/G_{r+1}` stage. -/
theorem exists_definition1Transition
    {xs : List A} {seed : Selection xs} {n : ℕ} (r : ℕ)
    (previous : Definition1ExtremalState xs seed n) :
    ∃ (next : Definition1ExtremalState xs seed n)
      (F : Theorem21SetPartition xs n seed.card),
      Definition1Transition r previous next F := by
  classical
  let H : AddSubgroup A := AddAction.stabilizer A
    (previous.chosen.tailSumset r : Set A)
  let lambdaBase := previous.upsilon.filter fun P ↦
    P.tailSumset r = previous.chosen.tailSumset r
  have hchosenBase : previous.chosen ∈ lambdaBase := by
    simp [lambdaBase, previous.chosen_mem]
  obtain ⟨F, hFbase, hFmax⟩ := Finset.exists_max_image lambdaBase
    (fun P ↦ P.quotientIncidenceAt H) ⟨previous.chosen, hchosenBase⟩
  let lambda := lambdaBase.filter fun P ↦
    P.quotientIncidenceAt H = F.quotientIncidenceAt H
  have hFlambda : F ∈ lambda := by simp [lambda, hFbase]
  let upsilonBase := lambda.filter fun P ↦ F.quotientImagesIncluded P H
  have hFupsilonBase : F ∈ upsilonBase := by
    simp only [upsilonBase, Finset.mem_filter, hFlambda, true_and]
    intro c
    exact Finset.Subset.rfl
  obtain ⟨G, hGbase, hGmax⟩ := Finset.exists_max_image upsilonBase
    (fun P ↦ (P.tailSumset (r + 1)).card) ⟨F, hFupsilonBase⟩
  let nextUpsilon := upsilonBase.filter fun P ↦
    (P.tailSumset (r + 1)).card = (G.tailSumset (r + 1)).card
  have hGnext : G ∈ nextUpsilon := by simp [nextUpsilon, hGbase]
  let next : Definition1ExtremalState xs seed n := {
    upsilon := nextUpsilon
    chosen := G
    chosen_mem := hGnext
  }
  refine ⟨next, F, {
    F_mem_previous := ?_
    F_tail_fixed := ?_
    incidence_maximal := ?_
    tail_maximal := ?_
    mem_next_upsilon_iff := ?_
  }⟩
  · exact (Finset.mem_filter.mp hFbase).1
  · exact (Finset.mem_filter.mp hFbase).2
  · intro P hPprev hPtail
    exact hFmax P (Finset.mem_filter.mpr ⟨hPprev, hPtail⟩)
  · intro P hPprev hPtail hPinc hPimages
    apply hGmax P
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨hPprev, hPtail⟩, hPinc⟩
    · exact hPimages
  · intro P
    simp only [next, nextUpsilon, Finset.mem_filter, upsilonBase,
      lambda, lambdaBase]
    tauto

omit [Fintype A] in
/-- Recenter a Definition 1 stage at an arbitrary member of its literal
`Lambda`.  The incidence maximum is unchanged, while the following `Upsilon`
is rebuilt by a fresh finite argmax using this partition's quotient images as
the reference.  This is the normalization needed in dissertation Lemma 5;
it does not identify the old fixed `F` or old `next` with the new ones. -/
theorem Definition1Transition.exists_recentered
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous oldNext : Definition1ExtremalState xs seed n}
    {oldF P : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous oldNext oldF)
    (hP : step.InLambda P) :
    ∃ next : Definition1ExtremalState xs seed n,
      Definition1Transition r previous next P := by
  classical
  let H : AddSubgroup A := AddAction.stabilizer A
    (previous.chosen.tailSumset r : Set A)
  let upsilonBase := previous.upsilon.filter fun Q ↦
    Q.tailSumset r = previous.chosen.tailSumset r ∧
      Q.quotientIncidenceAt H = P.quotientIncidenceAt H ∧
      P.quotientImagesIncluded Q H
  have hPbase : P ∈ upsilonBase := by
    apply Finset.mem_filter.mpr
    refine ⟨hP.1, hP.2.1, rfl, ?_⟩
    intro c
    exact Finset.Subset.rfl
  obtain ⟨G, hGbase, hGmax⟩ := Finset.exists_max_image upsilonBase
    (fun Q ↦ (Q.tailSumset (r + 1)).card) ⟨P, hPbase⟩
  let nextUpsilon := upsilonBase.filter fun Q ↦
    (Q.tailSumset (r + 1)).card = (G.tailSumset (r + 1)).card
  have hGnext : G ∈ nextUpsilon := by simp [nextUpsilon, hGbase]
  let next : Definition1ExtremalState xs seed n := {
    upsilon := nextUpsilon
    chosen := G
    chosen_mem := hGnext
  }
  refine ⟨next, {
    F_mem_previous := hP.1
    F_tail_fixed := hP.2.1
    incidence_maximal := ?_
    tail_maximal := ?_
    mem_next_upsilon_iff := ?_
  }⟩
  · intro Q hQprevious hQtail
    have hmax := step.incidence_maximal Q hQprevious hQtail
    rw [← hP.2.2] at hmax
    simpa [H] using hmax
  · intro Q hQprevious hQtail hQinc hQimages
    apply hGmax Q
    exact Finset.mem_filter.mpr
      ⟨hQprevious, hQtail, by simpa [H] using hQinc,
        by simpa [H] using hQimages⟩
  · intro Q
    simp only [next, nextUpsilon, Finset.mem_filter, upsilonBase]
    tauto

/-- The full finite chain, indexed by its last stage.  The indexed inductive
type prevents any accidental reuse of a fixed partition: every successor
stores a fresh state connected only by the exact Definition 1 transition. -/
inductive Definition1ExtremalChain
    (xs : List A) (seed : Selection xs) (n : ℕ) :
    ℕ → Definition1ExtremalState xs seed n → Type (u + 1)
  | initial (state) (valid : Definition1InitialValid state) :
      Definition1ExtremalChain xs seed n 0 state
  | next {r previous}
      (chain : Definition1ExtremalChain xs seed n r previous)
      (state) (F : Theorem21SetPartition xs n seed.card)
      (valid : Definition1Transition r previous state F) :
      Definition1ExtremalChain xs seed n (r + 1) state

omit [Fintype A] in
/-- Definition 1's iterated extremal chain exists to every finite depth. -/
theorem exists_definition1ExtremalChain
    (xs : List A) (seed : Selection xs) (n r : ℕ)
    (hcap : SelectionMultiplicityAtMost xs seed n)
    (hlen : n ≤ seed.card) :
    ∃ state : Definition1ExtremalState xs seed n,
      Nonempty (Definition1ExtremalChain xs seed n r state) := by
  induction r with
  | zero =>
      obtain ⟨state, hstate⟩ :=
        exists_definition1InitialState xs seed n hcap hlen
      exact ⟨state, ⟨Definition1ExtremalChain.initial state hstate⟩⟩
  | succ r ih =>
      obtain ⟨previous, ⟨chain⟩⟩ := ih
      obtain ⟨state, F, htransition⟩ :=
        exists_definition1Transition r previous
      exact ⟨state,
        ⟨Definition1ExtremalChain.next chain state F htransition⟩⟩

/-- Source-faithful Definition 1 chain.  Only its initial constructor differs
from the projected chain: `Upsilon_0` is maximized under the literal
`Lambda_0` admissibility predicate.  All successor transitions are the same
finite `Lambda/F/Upsilon/G/H` construction. -/
inductive Definition1SourceChain
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) :
    ℕ → Definition1ExtremalState xs seed n → Type (u + 1)
  | initial (state) (valid : Definition1InitialValidUnder I state) :
      Definition1SourceChain I 0 state
  | next {r previous}
      (chain : Definition1SourceChain I r previous)
      (state) (F : Theorem21SetPartition xs n seed.card)
      (valid : Definition1Transition r previous state F) :
      Definition1SourceChain I (r + 1) state

omit [Fintype A] in
/-- A member of the final source-chain family belongs to the literal
`Lambda_{j+1}` at every earlier stage `j`.  The returned transition retains
its independently chosen `F_{j+1}`; no exact-`F` normalization is assumed.
-/
theorem Definition1SourceChain.exists_transition_at
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (chain : Definition1SourceChain I r state)
    (P : Theorem21SetPartition xs n seed.card)
    (hP : P ∈ state.upsilon) {j : ℕ} (hj : j < r) :
    ∃ (previous next : Definition1ExtremalState xs seed n)
      (F : Theorem21SetPartition xs n seed.card),
      ∃ (_prior : Definition1SourceChain I j previous)
        (step : Definition1Transition j previous next F),
        step.InLambda P := by
  induction chain with
  | initial state valid => omega
  | @next r previous prior next F step ih =>
      by_cases hjr : j = r
      · subst j
        exact ⟨previous, next, F, prior, step,
          step.inLambda_of_mem_next hP⟩
      · have hjlt : j < r := by omega
        have hPprevious : P ∈ previous.upsilon :=
          ((step.mem_next_upsilon_iff P).1 hP).1
        exact ih hPprevious hjlt

omit [Fintype A] in
/-- The literal source chain exists to every finite depth. -/
theorem exists_definition1SourceChain
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (r : ℕ) :
    ∃ state : Definition1ExtremalState xs seed n,
      Nonempty (Definition1SourceChain I r state) := by
  induction r with
  | zero =>
      obtain ⟨state, hstate⟩ := exists_definition1InitialStateUnder I
      exact ⟨state, ⟨Definition1SourceChain.initial state hstate⟩⟩
  | succ r ih =>
      obtain ⟨previous, ⟨chain⟩⟩ := ih
      obtain ⟨state, F, htransition⟩ :=
        exists_definition1Transition r previous
      exact ⟨state,
        ⟨Definition1SourceChain.next chain state F htransition⟩⟩

/-! ### The doubled-exception removal step (dissertation Lemma 1) -/

/-- A value is an `H`-exception for a setpartition when its quotient class is
missing from at least one cell.  This is the literal ordinary-weight
specialization of the dissertation's exception terminology. -/
noncomputable def Theorem21SetPartition.IsHException
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (x : A) : Prop :=
  ∃ c : Fin n,
    QuotientAddGroup.mk' H x ∉ quotientLayer H (P.valueCell c)

/-- The quotient class of `x` is doubled in cell `c`: the cell contains a
different value in the same `H`-coset. -/
noncomputable def Theorem21SetPartition.IsHDoubledInCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (x : A) : Prop :=
  x ∈ P.valueCell c ∧
    ∃ y ∈ P.valueCell c, y ≠ x ∧
      QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x

/-- A doubled exception records both roles and the cell in which the
duplicate occurs. -/
noncomputable def Theorem21SetPartition.IsHDoubledException
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (x : A) : Prop :=
  P.IsHException H x ∧ ∃ c : Fin n, P.IsHDoubledInCell H c x

/-! ### Literal zero-based weak factor forms (dissertation Definition 2) -/

/-- Actual stabilizer of the source tail beginning at one-based cell
`r + 1`. -/
noncomputable def Theorem21SetPartition.tailPeriod
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (r : ℕ) : AddSubgroup A :=
  AddAction.stabilizer A (P.tailSumset r : Set A)

/-- Zero-based leading cells `X₁, ..., X_rho`. -/
def leadingIndices (n rho : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c ↦ c.val < rho

/-- Zero-based tail cells `Y_{rho+1}, ..., Y_n`. -/
def tailIndices (n rho : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c ↦ rho ≤ c.val

/-- Canonical zero-based indexing of the suffix beginning at rho. -/
def tailIndex (n rho : ℕ) (j : Fin (n - rho)) : Fin n :=
  ⟨rho + j.val, by omega⟩

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem tailIndex_val {n rho : ℕ} (j : Fin (n - rho)) :
    (tailIndex n rho j).val = rho + j.val := rfl

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem mem_tailIndices {n rho : ℕ} (c : Fin n) :
    c ∈ tailIndices n rho ↔ rho ≤ c.val := by
  simp [tailIndices]

omit [AddCommGroup A] [Fintype A] in
/-- The suffix list is literally the ofFn enumeration of the canonical
tail indices. -/
theorem Theorem21SetPartition.tailValueCells_eq_ofFn_tailIndex
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m) :
    P.tailValueCells rho =
      List.ofFn fun j : Fin (n - rho) ↦ P.valueCell (tailIndex n rho j) := by
  classical
  have hlenLeft : (P.tailValueCells rho).length = n - rho := by
    simp [Theorem21SetPartition.tailValueCells, P.length_valueCells]
  have hlenRight :
      (List.ofFn fun j : Fin (n - rho) ↦
        P.valueCell (tailIndex n rho j)).length = n - rho := by simp
  apply List.ext_get (hlenLeft.trans hlenRight.symm)
  intro j hjLeft hjRight
  simp only [Theorem21SetPartition.tailValueCells,
    Theorem21SetPartition.valueCells, List.get_eq_getElem,
    List.getElem_drop, List.getElem_ofFn]
  congr 2

omit [AddCommGroup A] [Fintype A] in
/-- The list sum of tail-cell cardinalities agrees with the indexed
incidence sum used in factor-form conditions. -/
theorem Theorem21SetPartition.sum_card_tailValueCells_eq_tailIndices
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m) :
    (P.tailValueCells rho |>.map Finset.card).sum =
      ∑ c ∈ tailIndices n rho, (P.valueCell c).card := by
  classical
  rw [P.tailValueCells_eq_ofFn_tailIndex]
  simp only [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_bij (fun j _ ↦ tailIndex n rho j) ?_ ?_ ?_ ?_
  · intro j _
    exact mem_tailIndices (tailIndex n rho j) |>.2 (by simp)
  · intro i _ j _ hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    simp only [tailIndex_val] at hv
    omega
  · intro c hc
    have hrc : rho ≤ c.val := (mem_tailIndices c).1 hc
    let j : Fin (n - rho) := ⟨c.val - rho, by omega⟩
    refine ⟨j, Finset.mem_univ j, ?_⟩
    apply Fin.ext
    simp [j, tailIndex]
    omega
  · intro j _
    rfl

omit [Fintype A] in
/-- Quotient-incidence version of the preceding tail reindexing identity. -/
theorem Theorem21SetPartition.sum_card_quotientLayer_tailValueCells_eq_tailIndices
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (P.tailValueCells rho |>.map fun B ↦ (quotientLayer H B).card).sum =
      ∑ c ∈ tailIndices n rho,
        (quotientLayer H (P.valueCell c)).card := by
  classical
  rw [P.tailValueCells_eq_ofFn_tailIndex]
  simp only [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_bij (fun j _ ↦ tailIndex n rho j) ?_ ?_ ?_ ?_
  · intro j _
    exact mem_tailIndices (tailIndex n rho j) |>.2 (by simp)
  · intro i _ j _ hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    simp only [tailIndex_val] at hv
    omega
  · intro c hc
    have hrc : rho ≤ c.val := (mem_tailIndices c).1 hc
    let j : Fin (n - rho) := ⟨c.val - rho, by omega⟩
    refine ⟨j, Finset.mem_univ j, ?_⟩
    apply Fin.ext
    simp [j, tailIndex]
    omega
  · intro j _
    rfl

omit [AddCommGroup A] [Fintype A] in
/-- A cell permutation fixes the initial segment strictly before `rho`.
This is the exact reindexing condition used by the WLOG step in
dissertation Lemma 5: leading cells keep their names, while the remaining
tail may be permuted arbitrarily. -/
def PrefixFixed (sigma : Equiv.Perm (Fin n)) (rho : ℕ) : Prop :=
  ∀ c : Fin n, c.val < rho → sigma c = c

omit [AddCommGroup A] [Fintype A] in
theorem PrefixFixed.symm
    {sigma : Equiv.Perm (Fin n)} {rho : ℕ}
    (hfix : PrefixFixed sigma rho) : PrefixFixed sigma.symm rho := by
  intro c hc
  apply sigma.injective
  simp [hfix c hc]

omit [AddCommGroup A] [Fintype A] in
/-- A prefix-fixing permutation maps the complementary tail to itself. -/
theorem PrefixFixed.tail_mapped
    {sigma : Equiv.Perm (Fin n)} {rho : ℕ}
    (hfix : PrefixFixed sigma rho) (c : Fin n) (hc : rho ≤ c.val) :
    rho ≤ (sigma c).val := by
  by_contra htail
  have hlt : (sigma c).val < rho := Nat.lt_of_not_ge htail
  have hfixed := hfix (sigma c) hlt
  have hcs : c = sigma c := by
    apply sigma.injective
    rw [hfixed]
  rw [hcs] at hc
  omega

omit [AddCommGroup A] [Fintype A] in
/-- Converting a tail index to an ambient index and back by subtraction is
exact; the explicit lemma avoids dependent proof-term noise below. -/
theorem tailIndex_sub_eq (c : Fin n) {rho : ℕ} (hc : rho ≤ c.val) :
    tailIndex n rho ⟨c.val - rho, by omega⟩ = c := by
  apply Fin.ext
  simp only [tailIndex_val]
  omega

omit [AddCommGroup A] [Fintype A] in
/-- The permutation induced on the canonical `Fin (n-rho)` indexing of a
prefix-fixed tail. -/
noncomputable def tailRestrictionPerm
    (sigma : Equiv.Perm (Fin n)) (rho : ℕ)
    (hfix : PrefixFixed sigma rho) : Equiv.Perm (Fin (n - rho)) where
  toFun j := ⟨(sigma (tailIndex n rho j)).val - rho, by
    have hlower := hfix.tail_mapped (tailIndex n rho j) (by simp)
    have hupper := (sigma (tailIndex n rho j)).isLt
    omega⟩
  invFun j := ⟨(sigma.symm (tailIndex n rho j)).val - rho, by
    have hlower := hfix.symm.tail_mapped (tailIndex n rho j) (by simp)
    have hupper := (sigma.symm (tailIndex n rho j)).isLt
    omega⟩
  left_inv j := by
    apply Fin.ext
    have hforward := hfix.tail_mapped (tailIndex n rho j) (by simp)
    change (sigma.symm (tailIndex n rho
      ⟨(sigma (tailIndex n rho j)).val - rho, by omega⟩)).val - rho = j.val
    rw [tailIndex_sub_eq (sigma (tailIndex n rho j)) hforward,
      sigma.symm_apply_apply]
    simp only [tailIndex_val]
    omega
  right_inv j := by
    apply Fin.ext
    have hforward := hfix.symm.tail_mapped (tailIndex n rho j) (by simp)
    change (sigma (tailIndex n rho
      ⟨(sigma.symm (tailIndex n rho j)).val - rho, by omega⟩)).val - rho = j.val
    rw [tailIndex_sub_eq (sigma.symm (tailIndex n rho j)) hforward,
      sigma.apply_symm_apply]
    simp only [tailIndex_val]
    omega

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem tailIndex_tailRestrictionPerm
    (sigma : Equiv.Perm (Fin n)) (rho : ℕ)
    (hfix : PrefixFixed sigma rho) (j : Fin (n - rho)) :
    tailIndex n rho (tailRestrictionPerm sigma rho hfix j) =
      sigma (tailIndex n rho j) := by
  apply Fin.ext
  have hlower := hfix.tail_mapped (tailIndex n rho j) (by simp)
  exact congrArg Fin.val
    (tailIndex_sub_eq (sigma (tailIndex n rho j)) hlower)

omit [AddCommGroup A] [Fintype A] in
/-- Reindexing by a prefix-fixing permutation merely permutes the layers of
the corresponding tail. -/
theorem Theorem21SetPartition.tailValueCells_reindex_perm
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (hfix : PrefixFixed sigma rho) :
    List.Perm ((P.reindex sigma).tailValueCells rho)
      (P.tailValueCells rho) := by
  classical
  rw [(P.reindex sigma).tailValueCells_eq_ofFn_tailIndex,
    P.tailValueCells_eq_ofFn_tailIndex]
  let tau := tailRestrictionPerm sigma rho hfix
  have hperm := tau.ofFn_comp_perm
    (fun j : Fin (n - rho) ↦ P.valueCell (tailIndex n rho j))
  have hfun :
      (fun j : Fin (n - rho) ↦ P.valueCell (tailIndex n rho j)) ∘ tau =
        fun j : Fin (n - rho) ↦
          P.valueCell (sigma (tailIndex n rho j)) := by
    funext j
    change P.valueCell (tailIndex n rho (tau j)) = _
    rw [show tailIndex n rho (tau j) = sigma (tailIndex n rho j) by
      simpa only [tau] using tailIndex_tailRestrictionPerm sigma rho hfix j]
  rw [hfun] at hperm
  simpa only [Theorem21SetPartition.valueCell_reindex] using hperm

omit [Fintype A] in
/-- Every prefix-fixed reindexing preserves the corresponding tail sumset. -/
theorem Theorem21SetPartition.tailSumset_reindex
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (hfix : PrefixFixed sigma rho) :
    (P.reindex sigma).tailSumset rho = P.tailSumset rho := by
  classical
  unfold Theorem21SetPartition.tailSumset
  exact fullLayerSumSpectrum_eq_of_perm
    (P.tailValueCells_reindex_perm sigma hfix)

omit [Fintype A] in
@[simp]
theorem Theorem21SetPartition.quotientIncidenceAt_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) :
    (P.reindex sigma).quotientIncidenceAt H = P.quotientIncidenceAt H := by
  classical
  unfold Theorem21SetPartition.quotientIncidenceAt
  simpa only [Theorem21SetPartition.valueCell_reindex] using
    (sigma.sum_comp (Finset.univ : Finset (Fin n))
      (fun c : Fin n ↦ (quotientLayer H (P.valueCell c)).card) (by simp))

omit [Fintype A] in
theorem Theorem21SetPartition.quotientImagesIncluded_reindex_iff
    {xs : List A} {n m : ℕ}
    (F P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) :
    (F.reindex sigma).quotientImagesIncluded (P.reindex sigma) H ↔
      F.quotientImagesIncluded P H := by
  classical
  constructor
  · intro h c
    simpa using h (sigma.symm c)
  · intro h c
    simpa using h (sigma c)

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Definition1ExtremalState.mem_reindex_iff_preimage
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (state : Definition1ExtremalState xs seed n)
    (sigma : Equiv.Perm (Fin n))
    (P : Theorem21SetPartition xs n seed.card) :
    P ∈ (state.reindex sigma).upsilon ↔
      P.reindex sigma.symm ∈ state.upsilon := by
  simpa using state.mem_reindex_iff sigma (P.reindex sigma.symm)

omit [Fintype A] in
/-- The literal source base family and its full-sumset argmax transport under
a simultaneous reindexing of the input, anchors, and extremal state. -/
theorem Definition1InitialValidUnder.reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (valid : Definition1InitialValidUnder I state)
    (sigma : Equiv.Perm (Fin n)) :
    Definition1InitialValidUnder (I.reindex sigma) (state.reindex sigma) := by
  classical
  refine {
    chosen_admissible := valid.chosen_admissible.reindex sigma
    maximal := ?_
    mem_upsilon_iff := ?_
  }
  · intro P hP
    have hPinv : GMOReplacementAdmissible I (P.reindex sigma.symm) := by
      have := hP.reindex sigma.symm
      simpa using this
    have hmax := valid.maximal (P.reindex sigma.symm) hPinv
    simpa [Definition1ExtremalState.reindex,
      Theorem21SetPartition.sumset_reindex] using hmax
  · intro P
    rw [state.mem_reindex_iff_preimage sigma P,
      valid.mem_upsilon_iff]
    constructor
    · rintro ⟨hPadm, hPcard⟩
      have hPadm' := hPadm.reindex sigma
      refine ⟨?_, ?_⟩
      · simpa using hPadm'
      · simpa [Definition1ExtremalState.reindex,
          Theorem21SetPartition.sumset_reindex] using hPcard
    · rintro ⟨hPadm, hPcard⟩
      have hPadm' := hPadm.reindex sigma.symm
      refine ⟨?_, ?_⟩
      · simpa using hPadm'
      · simpa [Definition1ExtremalState.reindex,
          Theorem21SetPartition.sumset_reindex] using hPcard

omit [Fintype A] in
@[simp]
theorem Theorem21SetPartition.tailPeriod_reindex
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (hfix : PrefixFixed sigma rho) :
    (P.reindex sigma).tailPeriod rho = P.tailPeriod rho := by
  unfold Theorem21SetPartition.tailPeriod
  rw [P.tailSumset_reindex sigma hfix]

@[simp]
theorem Theorem21SetPartition.thickenedCell_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) (c : Fin n) :
    (P.reindex sigma).thickenedCell H c = P.thickenedCell H (sigma c) := by
  simp [Theorem21SetPartition.thickenedCell]

/-- The common intersection is insensitive to a permutation of all cells. -/
@[simp]
theorem Theorem21SetPartition.commonCore_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) :
    (P.reindex sigma).commonCore H = P.commonCore H := by
  classical
  ext x
  simp only [P.mem_commonCore_iff, (P.reindex sigma).mem_commonCore_iff,
    P.thickenedCell_reindex]
  constructor
  · intro h c
    simpa using h (sigma.symm c)
  · intro h c
    exact h (sigma c)

@[simp]
theorem Theorem21SetPartition.commonCosetCount_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) :
    (P.reindex sigma).commonCosetCount H = P.commonCosetCount H := by
  simp [Theorem21SetPartition.commonCosetCount]

@[simp]
theorem Theorem21SetPartition.cellExceptionDefect_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) (c : Fin n) :
    (P.reindex sigma).cellExceptionDefect H c =
      P.cellExceptionDefect H (sigma c) := by
  simp [Theorem21SetPartition.cellExceptionDefect]

@[simp]
theorem Theorem21SetPartition.exceptionDefect_reindex
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) :
    (P.reindex sigma).exceptionDefect H = P.exceptionDefect H := by
  classical
  unfold Theorem21SetPartition.exceptionDefect
  simpa only [P.cellExceptionDefect_reindex] using
    (sigma.sum_comp (Finset.univ : Finset (Fin n))
      (fun c : Fin n ↦ P.cellExceptionDefect H c) (by simp))

omit [Fintype A] in
theorem Theorem21SetPartition.isHException_reindex_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A) (x : A) :
    (P.reindex sigma).IsHException H x ↔ P.IsHException H x := by
  classical
  unfold Theorem21SetPartition.IsHException
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨sigma c, by simpa using hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨sigma.symm c, by simpa using hc⟩

omit [Fintype A] in
theorem Theorem21SetPartition.isHDoubledInCell_reindex_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (sigma : Equiv.Perm (Fin n)) (H : AddSubgroup A)
    (c : Fin n) (x : A) :
    (P.reindex sigma).IsHDoubledInCell H c x ↔
      P.IsHDoubledInCell H (sigma c) x := by
  simp [Theorem21SetPartition.IsHDoubledInCell]

omit [AddCommGroup A] [Fintype A] in
/-- Any named tail cell can be moved to the first tail position while every
leading cell remains fixed. -/
theorem exists_prefixFixed_swap_to_rho
    {n rho : ℕ} (q : Fin n) (hrhoq : rho ≤ q.val) (hrhon : rho < n) :
    ∃ sigma : Equiv.Perm (Fin n),
      PrefixFixed sigma rho ∧
        sigma ⟨rho, hrhon⟩ = q := by
  let r : Fin n := ⟨rho, hrhon⟩
  let sigma : Equiv.Perm (Fin n) := Equiv.swap q r
  refine ⟨sigma, ?_, ?_⟩
  · intro c hc
    have hcq : c ≠ q := by
      intro h
      have := congrArg Fin.val h
      omega
    have hcr : c ≠ r := by
      intro h
      have := congrArg Fin.val h
      simp only [r] at this
      omega
    exact Equiv.swap_apply_of_ne_of_ne hcq hcr
  · exact Equiv.swap_apply_right q r

omit [Fintype A] in
/-- A positive Definition 1 stage transports under any reindexing fixing
all cells through its current pivot `r`.  This hypothesis is exactly what
preserves both tails used by the transition, at `r` and at `r+1`. -/
theorem Definition1Transition.reindex
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous next F)
    (sigma : Equiv.Perm (Fin n))
    (hfix : PrefixFixed sigma (r + 1)) :
    Definition1Transition r (previous.reindex sigma)
      (next.reindex sigma) (F.reindex sigma) := by
  classical
  have hfixr : PrefixFixed sigma r := by
    intro c hc
    exact hfix c (by omega)
  have hpreviousR :
      ((previous.reindex sigma).chosen.tailSumset r) =
        previous.chosen.tailSumset r := by
    simpa only [Definition1ExtremalState.reindex] using
      previous.chosen.tailSumset_reindex sigma hfixr
  have hpreviousSucc :
      ((previous.reindex sigma).chosen.tailSumset (r + 1)) =
        previous.chosen.tailSumset (r + 1) := by
    simpa only [Definition1ExtremalState.reindex] using
      previous.chosen.tailSumset_reindex sigma hfix
  have hnextSucc :
      ((next.reindex sigma).chosen.tailSumset (r + 1)) =
        next.chosen.tailSumset (r + 1) := by
    simpa only [Definition1ExtremalState.reindex] using
      next.chosen.tailSumset_reindex sigma hfix
  refine {
    F_mem_previous := (previous.mem_reindex_iff sigma F).2
      step.F_mem_previous
    F_tail_fixed := ?_
    incidence_maximal := ?_
    tail_maximal := ?_
    mem_next_upsilon_iff := ?_
  }
  · calc
      (F.reindex sigma).tailSumset r = F.tailSumset r :=
        F.tailSumset_reindex sigma hfixr
      _ = previous.chosen.tailSumset r := step.F_tail_fixed
      _ = (previous.reindex sigma).chosen.tailSumset r := hpreviousR.symm
  · intro P hPmem hPtail
    let Q := P.reindex sigma.symm
    have hQmem : Q ∈ previous.upsilon :=
      (previous.mem_reindex_iff_preimage sigma P).1 hPmem
    have hQtailP : Q.tailSumset r = P.tailSumset r := by
      simpa only [Q] using P.tailSumset_reindex sigma.symm hfixr.symm
    have hQtail : Q.tailSumset r = previous.chosen.tailSumset r :=
      hQtailP.trans (hPtail.trans hpreviousR)
    have hmax := step.incidence_maximal Q hQmem hQtail
    rw [hpreviousR]
    simpa only [Q, Theorem21SetPartition.quotientIncidenceAt_reindex] using hmax
  · intro P hPmem hPtail hPinc hPimages
    let Q := P.reindex sigma.symm
    have hQmem : Q ∈ previous.upsilon :=
      (previous.mem_reindex_iff_preimage sigma P).1 hPmem
    have hQtailP : Q.tailSumset r = P.tailSumset r := by
      simpa only [Q] using P.tailSumset_reindex sigma.symm hfixr.symm
    have hQtail : Q.tailSumset r = previous.chosen.tailSumset r :=
      hQtailP.trans (hPtail.trans hpreviousR)
    have hQinc : Q.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) =
        F.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) := by
      rw [hpreviousR] at hPinc
      simpa only [Q, Theorem21SetPartition.quotientIncidenceAt_reindex]
        using hPinc
    have hQimages : F.quotientImagesIncluded Q
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)) := by
      rw [hpreviousR] at hPimages
      have hQback : Q.reindex sigma = P := by simp [Q]
      have htemp : (F.reindex sigma).quotientImagesIncluded
          (Q.reindex sigma)
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) := by
        rw [hQback]
        exact hPimages
      exact (F.quotientImagesIncluded_reindex_iff Q sigma _).1 htemp
    have hmax := step.tail_maximal Q hQmem hQtail hQinc hQimages
    have hQsucc : Q.tailSumset (r + 1) = P.tailSumset (r + 1) := by
      simpa only [Q] using P.tailSumset_reindex sigma.symm hfix.symm
    rw [hQsucc, ← hnextSucc] at hmax
    exact hmax
  · intro P
    let Q := P.reindex sigma.symm
    rw [next.mem_reindex_iff_preimage sigma P,
      step.mem_next_upsilon_iff Q]
    have hQtailR : Q.tailSumset r = P.tailSumset r := by
      simpa only [Q] using P.tailSumset_reindex sigma.symm hfixr.symm
    have hQtailSucc : Q.tailSumset (r + 1) = P.tailSumset (r + 1) := by
      simpa only [Q] using P.tailSumset_reindex sigma.symm hfix.symm
    have hQback : Q.reindex sigma = P := by simp [Q]
    constructor
    · rintro ⟨hQmem, hQtail, hQinc, hQimages, hQnext⟩
      refine ⟨(previous.mem_reindex_iff_preimage sigma P).2 hQmem,
        ?_, ?_, ?_, ?_⟩
      · exact hQtailR.symm.trans (hQtail.trans hpreviousR.symm)
      · rw [hpreviousR]
        simpa only [Q, Theorem21SetPartition.quotientIncidenceAt_reindex]
          using hQinc
      · have htemp :=
          (F.quotientImagesIncluded_reindex_iff Q sigma _).2 hQimages
        rw [hpreviousR, ← hQback]
        exact htemp
      · calc
          (P.tailSumset (r + 1)).card =
              (Q.tailSumset (r + 1)).card :=
            congrArg Finset.card hQtailSucc.symm
          _ = (next.chosen.tailSumset (r + 1)).card := hQnext
          _ = ((next.reindex sigma).chosen.tailSumset (r + 1)).card :=
            congrArg Finset.card hnextSucc.symm
    · rintro ⟨hPmem, hPtail, hPinc, hPimages, hPnext⟩
      refine ⟨(previous.mem_reindex_iff_preimage sigma P).1 hPmem,
        ?_, ?_, ?_, ?_⟩
      · exact hQtailR.trans (hPtail.trans hpreviousR)
      · rw [hpreviousR] at hPinc
        simpa only [Q, Theorem21SetPartition.quotientIncidenceAt_reindex]
          using hPinc
      · have htemp : (F.reindex sigma).quotientImagesIncluded
            (Q.reindex sigma)
          (AddAction.stabilizer A
              (previous.chosen.tailSumset r : Set A)) := by
          rw [hpreviousR] at hPimages
          rw [hQback]
          exact hPimages
        exact (F.quotientImagesIncluded_reindex_iff Q sigma _).1 htemp
      · calc
          (Q.tailSumset (r + 1)).card =
              (P.tailSumset (r + 1)).card :=
            congrArg Finset.card hQtailSucc
          _ = ((next.reindex sigma).chosen.tailSumset (r + 1)).card := hPnext
          _ = (next.chosen.tailSumset (r + 1)).card :=
            congrArg Finset.card hnextSucc

omit [Fintype A] in
/-- A source-faithful extremal chain transports under a permutation fixing
its entire leading prefix.  Each successor invokes the preceding theorem
with its own true stage, so no final transition is reused at an earlier
prefix. -/
noncomputable def Definition1SourceChain.reindex
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (chain : Definition1SourceChain I rho state)
    (sigma : Equiv.Perm (Fin n))
    (hfix : PrefixFixed sigma rho) :
    Definition1SourceChain (I.reindex sigma) rho (state.reindex sigma) := by
  induction chain with
  | initial state valid =>
      exact Definition1SourceChain.initial (state.reindex sigma)
        (valid.reindex sigma)
  | @next r previous prior state F step ih =>
      have hfixr : PrefixFixed sigma r := by
        intro c hc
        exact hfix c (by omega)
      have hfixSucc : PrefixFixed sigma (r + 1) := by
        simpa only using hfix
      exact Definition1SourceChain.next (ih hfixr) (state.reindex sigma)
        (F.reindex sigma) (step.reindex sigma hfixSucc)

omit [AddCommGroup A] [Fintype A] in
/-- There are exactly `n-rho` cells in the zero-based tail. -/
theorem card_tailIndices {n rho : ℕ} (hrho : rho ≤ n) :
    (tailIndices n rho).card = n - rho := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun c : Fin n ↦ c.val < rho)
  have hlead :
      ((Finset.univ : Finset (Fin n)).filter
        (fun c : Fin n ↦ c.val < rho)).card = rho := by
    simp [Fin.card_filter_val_lt, min_eq_right hrho]
  have htotal :
      ((Finset.univ : Finset (Fin n)).filter
          (fun c : Fin n ↦ c.val < rho)).card +
        (tailIndices n rho).card = n := by
    simpa only [tailIndices, not_lt, Finset.card_univ,
      Fintype.card_fin] using hpart
  rw [hlead] at htotal
  omega

omit [AddCommGroup A] [Fintype A] in
/-- There are exactly `rho` leading cells when `rho ≤ n`. -/
theorem card_leadingIndices {n rho : ℕ} (hrho : rho ≤ n) :
    (leadingIndices n rho).card = rho := by
  classical
  simp [leadingIndices, Fin.card_filter_val_lt, min_eq_right hrho]

omit [AddCommGroup A] [Fintype A] in
/-- Every value cell contributes at least one value, so the tail incidence
sum cannot truncate below its number of cells. -/
theorem Theorem21SetPartition.card_tailIndices_le_sum_card_valueCell
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (hrho : rho ≤ n) :
    n - rho ≤ ∑ c ∈ tailIndices n rho, (P.valueCell c).card := by
  classical
  rw [← card_tailIndices hrho]
  calc
    (tailIndices n rho).card =
        ∑ c ∈ tailIndices n rho, 1 := by simp
    _ ≤ ∑ c ∈ tailIndices n rho, (P.valueCell c).card := by
      exact Finset.sum_le_sum fun c _ ↦
        Finset.card_pos.mpr (P.valueCells_nonempty (P.valueCell c) (by
          simp [Theorem21SetPartition.valueCells]))

omit [AddCommGroup A] [Fintype A] in
/-- Splitting the tail incidence sum at a named tail cell. -/
theorem Theorem21SetPartition.sum_tailIndices_erase_add
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : rho ≤ q.val) :
    (∑ c ∈ (tailIndices n rho).erase q, (P.valueCell c).card) +
        (P.valueCell q).card =
      ∑ c ∈ tailIndices n rho, (P.valueCell c).card := by
  classical
  exact Finset.sum_erase_add _ _ (mem_tailIndices q |>.2 hrq)

/-- Literal weak `rho`-factor form, with source cell `rho + 1` represented by
Lean tail index `rho`.  The transition retains its independently fixed
`F_{rho+1}`, while `partition_inLambda` only requires the factor partition to
belong to the genuine intermediate `Lambda_{rho+1}`, exactly as condition
(V) states.  The chain starts from source-admissible `Lambda_0`; conditions
(I) and (IV) are explicit, while (II) and (III) belong to `FactorForm`. -/
structure WeakFactorForm
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (rho : ℕ) where
  range : rho + 2 ≤ n
  partition : Theorem21SetPartition xs n seed.card
  admissible : GMOReplacementAdmissible I partition
  previous : Definition1ExtremalState xs seed n
  chain : Definition1SourceChain I rho previous
  next : Definition1ExtremalState xs seed n
  F : Theorem21SetPartition xs n seed.card
  transition : Definition1Transition rho previous next F
  partition_inLambda : transition.InLambda partition
  tail_actual : ∀ r, r ≤ rho →
    ⊥ < partition.tailPeriod r ∧ partition.tailPeriod r < ⊤
  leading_exception : ∀ c : Fin n, c.val < rho →
    ∃ x ∈ partition.valueCell c,
      partition.IsHException (partition.tailPeriod c.val) x

/-- Conditions (II) and (III) completing a weak factor form.  Natural-number
subtraction is kept in the same parenthesization as the source inequalities.
-/
structure FactorForm
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (rho : ℕ)
    extends WeakFactorForm I rho where
  quotient_growth :
    ((quotientLayer (partition.tailPeriod rho)
          (partition.tailSumset rho)).card +
        (∑ c ∈ leadingIndices n rho,
          (quotientLayer (partition.tailPeriod rho)
            (partition.valueCell c)).card) - (rho + 1) + 1) ≤
      (quotientLayer (partition.tailPeriod rho)
        partition.sumset).card
  tail_deficit :
    (partition.tailSumset rho).card <
      (∑ c ∈ tailIndices n rho, (partition.valueCell c).card) -
        (n - rho) + 1

omit [Fintype A] in
/-- Condition (V) in explicit `InLambda` form. -/
theorem WeakFactorForm.inLambda
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) :
    W.transition.InLambda W.partition := by
  exact W.partition_inLambda

omit [Fintype A] in
/-- Restricting a weak `rho`-factor form to any earlier stage produces an
honest weak `j`-factor form for the same partition.  The stage data are
extracted from the recursive source chain rather than fabricated by reusing
the final transition. -/
theorem WeakFactorForm.exists_prefix
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) {j : ℕ} (hj : j < rho) :
    ∃ Wj : WeakFactorForm I j, Wj.partition = W.partition := by
  have hPfinal : W.partition ∈ W.previous.upsilon :=
    W.partition_inLambda.1
  obtain ⟨previous, next, F, prior, step, hPinLambda⟩ :=
    W.chain.exists_transition_at W.partition hPfinal hj
  refine ⟨{
    range := by
      have := W.range
      omega
    partition := W.partition
    admissible := W.admissible
    previous := previous
    chain := prior
    next := next
    F := F
    transition := step
    partition_inLambda := hPinLambda
    tail_actual := ?_
    leading_exception := ?_
  }, rfl⟩
  · intro s hs
    exact W.tail_actual s (hs.trans (Nat.le_of_lt hj))
  · intro c hc
    exact W.leading_exception c (hc.trans hj)

omit [Fintype A] in
/-- Elementary removal engine used in dissertation Lemma 1.  If `x` has a
different representative `y` in the same `H`-coset and the sumset after
removing `x` is still `H`-periodic, then removal does not change the sumset.
This isolates the precise periodic/nonperiodic fork before any appeal to the
Definition 1 extremal chain. -/
theorem add_erase_eq_of_periodic_of_quotient_eq
    [DecidableEq A] (H : AddSubgroup A) (B C : Finset A) {x y : A}
    (hy : y ∈ C) (hxy : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x)
    (hperiodic : H ≤
      AddAction.stabilizer A ((B + C.erase x : Finset A) : Set A)) :
    B + C = B + C.erase x := by
  classical
  apply Finset.Subset.antisymm
  · intro z hz
    rcases Finset.mem_add.mp hz with ⟨b, hb, c, hc, rfl⟩
    by_cases hcx : c = x
    · subst c
      have hyErase : y ∈ C.erase x := Finset.mem_erase.mpr ⟨hxy, hy⟩
      have hby : b + y ∈ B + C.erase x :=
        Finset.mem_add.mpr ⟨b, hb, y, hyErase, rfl⟩
      have hyxH : y - x ∈ H :=
        QuotientAddGroup.eq_iff_sub_mem.mp hquot
      have hxyH : x - y ∈ H := by
        simpa only [neg_sub] using H.neg_mem hyxH
      have hstab := hperiodic hxyH
      rw [AddAction.mem_stabilizer_set] at hstab
      have htranslated := (hstab (b + y)).2 hby
      change (x - y) + (b + y) ∈ B + C.erase x at htranslated
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        htranslated
    · exact Finset.mem_add.mpr
        ⟨b, hb, c, Finset.mem_erase.mpr ⟨hcx, hc⟩, rfl⟩
  · intro z hz
    rcases Finset.mem_add.mp hz with ⟨b, hb, c, hc, rfl⟩
    exact Finset.mem_add.mpr
      ⟨b, hb, c, Finset.mem_of_mem_erase hc, rfl⟩

omit [Fintype A] in
/-- Checkable removal dichotomy in the exact direction used by Lemma 1:
either the reduced sumset loses `H`-periodicity, or it is equal to the
unreduced sumset. -/
theorem add_erase_not_periodic_or_eq_of_quotient_eq
    [DecidableEq A] (H : AddSubgroup A) (B C : Finset A) {x y : A}
    (hy : y ∈ C) (hxy : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x) :
    ¬ H ≤ AddAction.stabilizer A
        ((B + C.erase x : Finset A) : Set A) ∨
      B + C = B + C.erase x := by
  classical
  by_cases hperiodic : H ≤ AddAction.stabilizer A
      ((B + C.erase x : Finset A) : Set A)
  · exact Or.inr (add_erase_eq_of_periodic_of_quotient_eq
      H B C hy hxy hquot hperiodic)
  · exact Or.inl hperiodic

/-- Cell family obtained by moving one labelled occurrence from `q` to `d`.
The source erase precedes the target insert; the hypothesis `q ≠ d` used
below makes these two clauses disjoint. -/
def Theorem21SetPartition.moveOccurrenceCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q d : Fin n) (i : Occurrence xs) (c : Fin n) : Selection xs :=
  if c = q then (P.cells c).erase i
  else if c = d then insert i (P.cells c)
  else P.cells c

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.mem_moveOccurrenceCells_iff_of_ne
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q d : Fin n) (i x : Occurrence xs) (c : Fin n) (hxi : x ≠ i) :
    x ∈ P.moveOccurrenceCells q d i c ↔ x ∈ P.cells c := by
  by_cases hcq : c = q
  · subst c
    simp [Theorem21SetPartition.moveOccurrenceCells, hxi]
  · by_cases hcd : c = d
    · subst c
      simp [Theorem21SetPartition.moveOccurrenceCells, hcq, hxi]
    · simp [Theorem21SetPartition.moveOccurrenceCells, hcq, hcd]

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.not_mem_cell_of_mem_of_ne
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q c : Fin n} {i : Occurrence xs}
    (hiq : i ∈ P.cells q) (hcq : c ≠ q) :
    i ∉ P.cells c := by
  intro hic
  exact (Finset.disjoint_left.mp
    (P.cells_pairwise_disjoint hcq.symm)) hiq hic

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.mem_moveOccurrenceCells_self_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q d : Fin n} {i : Occurrence xs} (hqd : q ≠ d)
    (hiq : i ∈ P.cells q) (c : Fin n) :
    i ∈ P.moveOccurrenceCells q d i c ↔ c = d := by
  by_cases hcq : c = q
  · subst c
    simp [Theorem21SetPartition.moveOccurrenceCells, hqd]
  · by_cases hcd : c = d
    · subst c
      simp [Theorem21SetPartition.moveOccurrenceCells, hqd.symm]
    · have hnot : i ∉ P.cells c := P.not_mem_cell_of_mem_of_ne hiq hcq
      simp [Theorem21SetPartition.moveOccurrenceCells, hcq, hcd, hnot]

omit [AddCommGroup A] [Fintype A] in
/-- Moving one labelled occurrence between distinct cells preserves the exact
setpartition structure, provided the source retains another occurrence and
the target contains no occurrence with the moved value.  The support itself,
not only its cardinality, is preserved. -/
theorem Theorem21SetPartition.exists_moveOccurrence
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q d : Fin n} {i : Occurrence xs}
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hsource : ∃ j ∈ P.cells q, j ≠ i)
    (htarget : ∀ j ∈ P.cells d,
      occurrenceValue xs j ≠ occurrenceValue xs i) :
    ∃ Q : Theorem21SetPartition xs n m,
      (∀ c, Q.cells c = P.moveOccurrenceCells q d i c) ∧
      Q.support = P.support := by
  classical
  let moved : Fin n → Selection xs := P.moveOccurrenceCells q d i
  have hmovedNonempty : ∀ c, (moved c).Nonempty := by
    intro c
    by_cases hcq : c = q
    · subst c
      obtain ⟨j, hj, hji⟩ := hsource
      exact ⟨j, by
        simp [moved, Theorem21SetPartition.moveOccurrenceCells, hji, hj]⟩
    · by_cases hcd : c = d
      · subst c
        exact ⟨i, by
          simp [moved, Theorem21SetPartition.moveOccurrenceCells, hqd.symm]⟩
      · obtain ⟨j, hj⟩ := P.cells_nonempty c
        exact ⟨j, by
          simp [moved, Theorem21SetPartition.moveOccurrenceCells, hcq, hcd, hj]⟩
  have hmovedDisjoint : ∀ {c e}, c ≠ e → Disjoint (moved c) (moved e) := by
    intro c e hce
    rw [Finset.disjoint_left]
    intro x hxc hxe
    by_cases hxi : x = i
    · subst x
      have hcd := (P.mem_moveOccurrenceCells_self_iff hqd hiq c).1 hxc
      have hed := (P.mem_moveOccurrenceCells_self_iff hqd hiq e).1 hxe
      exact hce (hcd.trans hed.symm)
    · have hxc' : x ∈ P.cells c :=
        (P.mem_moveOccurrenceCells_iff_of_ne q d i x c hxi).1 hxc
      have hxe' : x ∈ P.cells e :=
        (P.mem_moveOccurrenceCells_iff_of_ne q d i x e hxi).1 hxe
      exact (Finset.disjoint_left.mp
        (P.cells_pairwise_disjoint hce)) hxc' hxe'
  have hmovedInjective : ∀ c,
      Set.InjOn (occurrenceValue xs) (moved c : Set (Occurrence xs)) := by
    intro c x hxc y hyc hvalue
    by_cases hxi : x = i
    · subst x
      by_cases hyi : y = i
      · exact hyi.symm
      · have hcd := (P.mem_moveOccurrenceCells_self_iff hqd hiq c).1 hxc
        subst c
        have hyTarget : y ∈ P.cells d :=
          (P.mem_moveOccurrenceCells_iff_of_ne q d i y d hyi).1 hyc
        exact False.elim ((htarget y hyTarget) hvalue.symm)
    · by_cases hyi : y = i
      · subst y
        have hcd := (P.mem_moveOccurrenceCells_self_iff hqd hiq c).1 hyc
        subst c
        have hxTarget : x ∈ P.cells d :=
          (P.mem_moveOccurrenceCells_iff_of_ne q d i x d hxi).1 hxc
        exact False.elim ((htarget x hxTarget) hvalue)
      · apply P.value_injective c
        · exact (P.mem_moveOccurrenceCells_iff_of_ne q d i x c hxi).1 hxc
        · exact (P.mem_moveOccurrenceCells_iff_of_ne q d i y c hyi).1 hyc
        · exact hvalue
  have hsupport : Finset.univ.biUnion moved = P.support := by
    ext x
    by_cases hxi : x = i
    · subst x
      constructor
      · intro _
        apply Finset.mem_biUnion.mpr
        exact ⟨q, Finset.mem_univ q, hiq⟩
      · intro _
        apply Finset.mem_biUnion.mpr
        exact ⟨d, Finset.mem_univ d,
          (P.mem_moveOccurrenceCells_self_iff hqd hiq d).2 rfl⟩
    · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Theorem21SetPartition.support]
      constructor
      · rintro ⟨c, hxc⟩
        exact ⟨c,
          (P.mem_moveOccurrenceCells_iff_of_ne q d i x c hxi).1 hxc⟩
      · rintro ⟨c, hxc⟩
        exact ⟨c,
          (P.mem_moveOccurrenceCells_iff_of_ne q d i x c hxi).2 hxc⟩
  let Q : Theorem21SetPartition xs n m := {
    cells := moved
    cells_nonempty := hmovedNonempty
    cells_pairwise_disjoint := hmovedDisjoint
    value_injective := hmovedInjective
    card_support := by rw [hsupport]; exact P.card_support
  }
  refine ⟨Q, ?_, ?_⟩
  · intro c
    rfl
  · exact hsupport

/-- Cell family obtained by deleting a used labelled occurrence y from
cell q and inserting a genuinely unused labelled occurrence x into the
distinct cell d.  Unlike moveOccurrenceCells, this changes the selected
replacement subsequence while preserving its cardinality. -/
def Theorem21SetPartition.replaceUsedWithUnusedCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q d : Fin n) (y x : Occurrence xs) (c : Fin n) : Selection xs :=
  if c = q then (P.cells c).erase y
  else if c = d then insert x (P.cells c)
  else P.cells c

omit [AddCommGroup A] [Fintype A] in
/-- Exact membership formula for cross-support replacement.  It records
that x is present only in the target cell, while every old occurrence
except y remains in its old cell. -/
theorem Theorem21SetPartition.mem_replaceUsedWithUnusedCells_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q d : Fin n} {y x z : Occurrence xs} (c : Fin n)
    (hqd : q ≠ d) (hyq : y ∈ P.cells q) (hxunused : x ∉ P.support) :
    z ∈ P.replaceUsedWithUnusedCells q d y x c ↔
      (c = d ∧ z = x) ∨ (z ∈ P.cells c ∧ z ≠ y) := by
  classical
  have hxnot (e : Fin n) : x ∉ P.cells e := by
    intro hxe
    apply hxunused
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ e, hxe⟩
  by_cases hcq : c = q
  · subst c
    simp only [Theorem21SetPartition.replaceUsedWithUnusedCells, if_pos,
      hqd, false_and, false_or, Finset.mem_erase]
    exact and_comm
  · by_cases hcd : c = d
    · subst c
      have hynot : y ∉ P.cells d :=
        P.not_mem_cell_of_mem_of_ne hyq hqd.symm
      simp only [Theorem21SetPartition.replaceUsedWithUnusedCells,
        if_neg hqd.symm, if_pos, Finset.mem_insert, true_and]
      constructor
      · intro hz
        rcases hz with hzx | hzOld
        · exact Or.inl hzx
        · exact Or.inr ⟨hzOld, fun hzy ↦ hynot (hzy ▸ hzOld)⟩
      · rintro (hzx | hzOld)
        · exact Or.inl hzx
        · exact Or.inr hzOld.1
    · have hynot : y ∉ P.cells c :=
        P.not_mem_cell_of_mem_of_ne hyq hcq
      simp only [Theorem21SetPartition.replaceUsedWithUnusedCells,
        if_neg hcq, hcd, false_and, false_or]
      exact ⟨fun hz ↦ ⟨hz, fun hzy ↦ hynot (hzy ▸ hz)⟩, And.left⟩

omit [AddCommGroup A] [Fintype A] in
/-- Honest occurrence-level cross-support replacement.  The resulting
support is exactly (P.support.erase y).insert x, so its cardinality is
unchanged; no occurrence or multiplicity is silently forgotten. -/
theorem Theorem21SetPartition.exists_replaceUsedWithUnused
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q d : Fin n} {y x : Occurrence xs}
    (hqd : q ≠ d) (hyq : y ∈ P.cells q)
    (hsource : ∃ j ∈ P.cells q, j ≠ y)
    (hxunused : x ∉ P.support)
    (htarget : ∀ j ∈ P.cells d,
      occurrenceValue xs j ≠ occurrenceValue xs x) :
    ∃ Q : Theorem21SetPartition xs n m,
      (∀ c, Q.cells c = P.replaceUsedWithUnusedCells q d y x c) ∧
      Q.support = insert x (P.support.erase y) := by
  classical
  let replaced : Fin n → Selection xs :=
    P.replaceUsedWithUnusedCells q d y x
  have hmem (z : Occurrence xs) (c : Fin n) :
      z ∈ replaced c ↔
        (c = d ∧ z = x) ∨ (z ∈ P.cells c ∧ z ≠ y) := by
    exact P.mem_replaceUsedWithUnusedCells_iff c hqd hyq hxunused
  have hreplacedNonempty : ∀ c, (replaced c).Nonempty := by
    intro c
    by_cases hcq : c = q
    · subst c
      obtain ⟨j, hj, hjy⟩ := hsource
      exact ⟨j, (hmem j q).2 (Or.inr ⟨hj, hjy⟩)⟩
    · by_cases hcd : c = d
      · exact ⟨x, (hmem x c).2 (Or.inl ⟨hcd, rfl⟩)⟩
      · obtain ⟨j, hj⟩ := P.cells_nonempty c
        have hjy : j ≠ y := by
          intro hjyeq
          subst j
          exact (P.not_mem_cell_of_mem_of_ne hyq hcq) hj
        exact ⟨j, (hmem j c).2 (Or.inr ⟨hj, hjy⟩)⟩
  have hreplacedDisjoint : ∀ {c e}, c ≠ e →
      Disjoint (replaced c) (replaced e) := by
    intro c e hce
    rw [Finset.disjoint_left]
    intro z hzc hze
    rcases (hmem z c).1 hzc with hxc | hzcOld
    · rcases (hmem z e).1 hze with hxe | hzeOld
      · exact hce (hxc.1.trans hxe.1.symm)
      · rcases hxc with ⟨hcd, hzx⟩
        subst z
        subst c
        exact hxunused (Finset.mem_biUnion.mpr
          ⟨e, Finset.mem_univ e, hzeOld.1⟩)
    · rcases (hmem z e).1 hze with hxe | hzeOld
      · rcases hxe with ⟨hed, hzx⟩
        subst z
        subst e
        exact hxunused (Finset.mem_biUnion.mpr
          ⟨c, Finset.mem_univ c, hzcOld.1⟩)
      · exact (Finset.disjoint_left.mp
          (P.cells_pairwise_disjoint hce)) hzcOld.1 hzeOld.1
  have hreplacedInjective : ∀ c,
      Set.InjOn (occurrenceValue xs) (replaced c : Set (Occurrence xs)) := by
    intro c a ha b hb hab
    rcases (hmem a c).1 ha with hax | haOld
    · rcases (hmem b c).1 hb with hbx | hbOld
      · exact hax.2.trans hbx.2.symm
      · rcases hax with ⟨hcd, hax⟩
        subst c
        subst a
        exact False.elim ((htarget b hbOld.1) hab.symm)
    · rcases (hmem b c).1 hb with hbx | hbOld
      · rcases hbx with ⟨hcd, hbx⟩
        subst c
        subst b
        exact False.elim ((htarget a haOld.1) hab)
      · exact P.value_injective c haOld.1 hbOld.1 hab
  have hsupport : Finset.univ.biUnion replaced =
      insert x (P.support.erase y) := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_erase, Theorem21SetPartition.support]
    constructor
    · rintro ⟨c, hzc⟩
      rcases (hmem z c).1 hzc with hzx | hzOld
      · exact Or.inl hzx.2
      · exact Or.inr ⟨hzOld.2, ⟨c, hzOld.1⟩⟩
    · rintro (hzx | ⟨hzy, c, hzc⟩)
      · exact ⟨d, (hmem z d).2 (Or.inl ⟨rfl, hzx⟩)⟩
      · exact ⟨c, (hmem z c).2 (Or.inr ⟨hzc, hzy⟩)⟩
  have hySupport : y ∈ P.support :=
    Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, hyq⟩
  have hxErase : x ∉ P.support.erase y := by
    exact fun hx ↦ hxunused (Finset.mem_of_mem_erase hx)
  let Q : Theorem21SetPartition xs n m := {
    cells := replaced
    cells_nonempty := hreplacedNonempty
    cells_pairwise_disjoint := hreplacedDisjoint
    value_injective := hreplacedInjective
    card_support := by
      rw [hsupport, Finset.card_insert_of_notMem hxErase,
        Finset.card_erase_of_mem hySupport,
        Nat.sub_add_cancel (Finset.card_pos.mpr ⟨y, hySupport⟩)]
      exact P.card_support
  }
  refine ⟨Q, ?_, ?_⟩
  · intro c
    rfl
  · exact hsupport

/-- Same-cell form of cross-support replacement.  The source occurrence is
erased before the unused occurrence is inserted into that very cell. -/
def Theorem21SetPartition.replaceUsedWithUnusedSameCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (y x : Occurrence xs) (c : Fin n) : Selection xs :=
  if c = q then insert x ((P.cells c).erase y) else P.cells c

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.mem_replaceUsedWithUnusedSameCell_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q : Fin n} {y x z : Occurrence xs} (c : Fin n)
    (hyq : y ∈ P.cells q) :
    z ∈ P.replaceUsedWithUnusedSameCell q y x c ↔
      (c = q ∧ z = x) ∨ (z ∈ P.cells c ∧ z ≠ y) := by
  classical
  by_cases hcq : c = q
  · subst c
    simp only [Theorem21SetPartition.replaceUsedWithUnusedSameCell, if_pos,
      Finset.mem_insert, Finset.mem_erase, true_and]
    tauto
  · have hynot : y ∉ P.cells c :=
      P.not_mem_cell_of_mem_of_ne hyq hcq
    simp only [Theorem21SetPartition.replaceUsedWithUnusedSameCell,
      hcq, false_and, false_or]
    exact ⟨fun hz ↦ ⟨hz, fun hzy ↦ hynot (hzy ▸ hz)⟩, And.left⟩

omit [AddCommGroup A] [Fintype A] in
/-- Same-cell replacement preserves the selected length and has exactly the
same changed occurrence support as the distinct-cell operation. -/
theorem Theorem21SetPartition.exists_replaceUsedWithUnusedSameCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {q : Fin n} {y x : Occurrence xs}
    (hyq : y ∈ P.cells q) (hxunused : x ∉ P.support)
    (hvalue : ∀ j ∈ P.cells q, j ≠ y →
      occurrenceValue xs j ≠ occurrenceValue xs x) :
    ∃ Q : Theorem21SetPartition xs n m,
      (∀ c, Q.cells c = P.replaceUsedWithUnusedSameCell q y x c) ∧
      Q.support = insert x (P.support.erase y) := by
  classical
  let replaced : Fin n → Selection xs :=
    P.replaceUsedWithUnusedSameCell q y x
  have hmem (z : Occurrence xs) (c : Fin n) :
      z ∈ replaced c ↔
        (c = q ∧ z = x) ∨ (z ∈ P.cells c ∧ z ≠ y) := by
    exact P.mem_replaceUsedWithUnusedSameCell_iff c hyq
  have hnonempty : ∀ c, (replaced c).Nonempty := by
    intro c
    by_cases hcq : c = q
    · exact ⟨x, (hmem x c).2 (Or.inl ⟨hcq, rfl⟩)⟩
    · obtain ⟨j, hj⟩ := P.cells_nonempty c
      have hjy : j ≠ y := by
        intro hjyeq
        subst j
        exact (P.not_mem_cell_of_mem_of_ne hyq hcq) hj
      exact ⟨j, (hmem j c).2 (Or.inr ⟨hj, hjy⟩)⟩
  have hdisjoint : ∀ {c d}, c ≠ d →
      Disjoint (replaced c) (replaced d) := by
    intro c d hcd
    rw [Finset.disjoint_left]
    intro z hzc hzd
    rcases (hmem z c).1 hzc with hxc | hzcOld
    · rcases (hmem z d).1 hzd with hxd | hzdOld
      · exact hcd (hxc.1.trans hxd.1.symm)
      · rcases hxc with ⟨hcq, hzx⟩
        subst z
        exact hxunused (Finset.mem_biUnion.mpr
          ⟨d, Finset.mem_univ d, hzdOld.1⟩)
    · rcases (hmem z d).1 hzd with hxd | hzdOld
      · rcases hxd with ⟨hdq, hzx⟩
        subst z
        exact hxunused (Finset.mem_biUnion.mpr
          ⟨c, Finset.mem_univ c, hzcOld.1⟩)
      · exact (Finset.disjoint_left.mp
          (P.cells_pairwise_disjoint hcd)) hzcOld.1 hzdOld.1
  have hinjective : ∀ c,
      Set.InjOn (occurrenceValue xs) (replaced c : Set (Occurrence xs)) := by
    intro c a ha b hb hab
    rcases (hmem a c).1 ha with hax | haOld
    · rcases (hmem b c).1 hb with hbx | hbOld
      · exact hax.2.trans hbx.2.symm
      · rcases hax with ⟨hcq, hax⟩
        subst c
        subst a
        exact False.elim ((hvalue b hbOld.1 hbOld.2) hab.symm)
    · rcases (hmem b c).1 hb with hbx | hbOld
      · rcases hbx with ⟨hcq, hbx⟩
        subst c
        subst b
        exact False.elim ((hvalue a haOld.1 haOld.2) hab)
      · exact P.value_injective c haOld.1 hbOld.1 hab
  have hsupport : Finset.univ.biUnion replaced =
      insert x (P.support.erase y) := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_erase, Theorem21SetPartition.support]
    constructor
    · rintro ⟨c, hzc⟩
      rcases (hmem z c).1 hzc with hzx | hzOld
      · exact Or.inl hzx.2
      · exact Or.inr ⟨hzOld.2, ⟨c, hzOld.1⟩⟩
    · rintro (hzx | ⟨hzy, c, hzc⟩)
      · exact ⟨q, (hmem z q).2 (Or.inl ⟨rfl, hzx⟩)⟩
      · exact ⟨c, (hmem z c).2 (Or.inr ⟨hzc, hzy⟩)⟩
  have hySupport : y ∈ P.support :=
    Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, hyq⟩
  have hxErase : x ∉ P.support.erase y :=
    fun hx ↦ hxunused (Finset.mem_of_mem_erase hx)
  let Q : Theorem21SetPartition xs n m := {
    cells := replaced
    cells_nonempty := hnonempty
    cells_pairwise_disjoint := hdisjoint
    value_injective := hinjective
    card_support := by
      rw [hsupport, Finset.card_insert_of_notMem hxErase,
        Finset.card_erase_of_mem hySupport,
        Nat.sub_add_cancel (Finset.card_pos.mpr ⟨y, hySupport⟩)]
      exact P.card_support
  }
  exact ⟨Q, fun _ ↦ rfl, hsupport⟩

omit [Fintype A] in
/-- A doubled exception supplies all occurrence-level hypotheses needed for
an honest move to a cell missing its quotient class.  In particular, the
second representative keeps the source cell nonempty, while absence of the
whole quotient class is stronger than the target value-injectivity condition.
-/
theorem Theorem21SetPartition.exists_moveOccurrence_of_isHDoubledException
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) {x : A} (hx : P.IsHDoubledException H x) :
    ∃ (q d : Fin n) (i : Occurrence xs)
      (Q : Theorem21SetPartition xs n m),
      q ≠ d ∧ i ∈ P.cells q ∧ occurrenceValue xs i = x ∧
      (∀ c, Q.cells c = P.moveOccurrenceCells q d i c) ∧
      Q.support = P.support := by
  classical
  rcases hx with ⟨⟨d, hdMissing⟩, q, hxq, y, hyq, hyx, hyquot⟩
  rcases Finset.mem_image.mp hxq with ⟨i, hiq, hix⟩
  rcases Finset.mem_image.mp hyq with ⟨j, hjq, hjy⟩
  have hqd : q ≠ d := by
    intro hqd
    subst d
    apply hdMissing
    exact (mem_quotientLayer_iff H (P.valueCell q) _).2 ⟨x, hxq, rfl⟩
  have hji : j ≠ i := by
    intro hji
    subst j
    apply hyx
    rw [← hix, ← hjy]
  have htarget : ∀ k ∈ P.cells d,
      occurrenceValue xs k ≠ occurrenceValue xs i := by
    intro k hkd hkvalue
    apply hdMissing
    apply (mem_quotientLayer_iff H (P.valueCell d) _).2
    refine ⟨occurrenceValue xs k, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨k, hkd, rfl⟩
    · simp [hkvalue, hix]
  obtain ⟨Q, hQcells, hQsupport⟩ := P.exists_moveOccurrence
    hqd hiq ⟨j, hjq, hji⟩ htarget
  exact ⟨q, d, i, Q, hqd, hiq, hix, hQcells, hQsupport⟩

omit [Fintype A] in
/-- Erasing one representative of a doubled quotient class does not change
the quotient image of the finite set. -/
theorem quotientLayer_erase_eq_of_duplicate
    [DecidableEq A] (H : AddSubgroup A) (C : Finset A) {x y : A}
    (hy : y ∈ C) (hxy : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x) :
    quotientLayer H (C.erase x) = quotientLayer H C := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨z, hz, rfl⟩ := (mem_quotientLayer_iff H (C.erase x) q).1 hq
    exact (mem_quotientLayer_iff H C _).2
      ⟨z, Finset.mem_of_mem_erase hz, rfl⟩
  · intro hq
    obtain ⟨z, hz, hzq⟩ := (mem_quotientLayer_iff H C q).1 hq
    by_cases hzx : z = x
    · subst z
      exact (mem_quotientLayer_iff H (C.erase x) q).2
        ⟨y, Finset.mem_erase.mpr ⟨hxy, hy⟩, hquot.trans hzq⟩
    · exact (mem_quotientLayer_iff H (C.erase x) q).2
        ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩, hzq⟩

omit [Fintype A] in
/-- Inserting a value whose quotient class was absent adds exactly one class
to the quotient image. -/
theorem card_quotientLayer_insert_of_not_mem
    [DecidableEq A] (H : AddSubgroup A) (C : Finset A) (x : A)
    (hx : QuotientAddGroup.mk' H x ∉ quotientLayer H C) :
    (quotientLayer H (insert x C)).card = (quotientLayer H C).card + 1 := by
  classical
  have himage : quotientLayer H (insert x C) =
      insert (QuotientAddGroup.mk' H x) (quotientLayer H C) := by
    ext q
    simp [mem_quotientLayer_iff, eq_comm]
  rw [himage, Finset.card_insert_of_notMem hx]

/-- Instance-independent wrapper used in theorem statements about removing a
value from a finite cell. -/
noncomputable def eraseValue (C : Finset A) (x : A) : Finset A := by
  classical
  exact C.erase x

/-- Instance-independent wrapper used in theorem statements about inserting
a value into a finite cell. -/
noncomputable def insertValue (x : A) (C : Finset A) : Finset A := by
  classical
  exact insert x C

omit [AddCommGroup A] [Fintype A] in
/-- On the source cell, an occurrence move erases exactly its value.  The
cell's value-injectivity is what rules out accidentally erasing a second
labelled occurrence with the same value. -/
theorem Theorem21SetPartition.valueCell_eq_erase_of_moveOccurrence
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs}
    (hiq : i ∈ P.cells q)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c) :
    Q.valueCell q = eraseValue (P.valueCell q) (occurrenceValue xs i) := by
  classical
  unfold eraseValue
  rw [Theorem21SetPartition.valueCell, hQcells q]
  simp only [Theorem21SetPartition.moveOccurrenceCells]
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨j, hj, hja⟩
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    apply Finset.mem_erase.mpr
    constructor
    · intro hai
      apply hji
      apply P.value_injective q (Finset.mem_of_mem_erase hj) hiq
      rw [hja, hai]
    · exact Finset.mem_image.mpr
        ⟨j, Finset.mem_of_mem_erase hj, hja⟩
  · intro ha
    have ha' := Finset.mem_erase.mp ha
    rcases Finset.mem_image.mp ha'.2 with ⟨j, hj, hja⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_erase.mpr ⟨?_, hj⟩, hja⟩
    intro hji
    subst j
    exact ha'.1 hja.symm

omit [AddCommGroup A] [Fintype A] in
/-- On the target cell, an occurrence move inserts exactly its value. -/
theorem Theorem21SetPartition.valueCell_eq_insert_of_moveOccurrence
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs} (hqd : q ≠ d)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c) :
    Q.valueCell d = insertValue (occurrenceValue xs i) (P.valueCell d) := by
  classical
  unfold insertValue
  rw [Theorem21SetPartition.valueCell, hQcells d]
  simp only [Theorem21SetPartition.moveOccurrenceCells, if_neg hqd.symm]
  ext a
  simp [Theorem21SetPartition.valueCell, eq_comm]

omit [AddCommGroup A] [Fintype A] in
/-- Every untouched cell has exactly its original value set. -/
theorem Theorem21SetPartition.valueCell_eq_of_moveOccurrence_of_ne
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs}
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    {c : Fin n} (hcq : c ≠ q) (hcd : c ≠ d) :
    Q.valueCell c = P.valueCell c := by
  classical
  rw [Theorem21SetPartition.valueCell, hQcells c]
  simp only [Theorem21SetPartition.moveOccurrenceCells, if_neg hcq,
    if_neg hcd]
  rfl

omit [AddCommGroup A] [Fintype A] in
/-- Cross-support replacement erases exactly the used occurrence's value
from its source cell. -/
theorem Theorem21SetPartition.valueCell_eq_erase_of_replaceUsedWithUnused
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {y x : Occurrence xs}
    (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c) :
    Q.valueCell q = eraseValue (P.valueCell q) (occurrenceValue xs y) := by
  classical
  unfold eraseValue
  rw [Theorem21SetPartition.valueCell, hQcells q]
  simp only [Theorem21SetPartition.replaceUsedWithUnusedCells, if_pos]
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨j, hj, hja⟩
    have hjy : j ≠ y := (Finset.mem_erase.mp hj).1
    apply Finset.mem_erase.mpr
    constructor
    · intro hay
      apply hjy
      apply P.value_injective q (Finset.mem_of_mem_erase hj) hyq
      rw [hja, hay]
    · exact Finset.mem_image.mpr
        ⟨j, Finset.mem_of_mem_erase hj, hja⟩
  · intro ha
    have ha' := Finset.mem_erase.mp ha
    rcases Finset.mem_image.mp ha'.2 with ⟨j, hj, hja⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_erase.mpr ⟨?_, hj⟩, hja⟩
    intro hjy
    subst j
    exact ha'.1 hja.symm

omit [AddCommGroup A] [Fintype A] in
/-- Cross-support replacement inserts exactly the unused occurrence's value
in its target cell. -/
theorem Theorem21SetPartition.valueCell_eq_insert_of_replaceUsedWithUnused
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {y x : Occurrence xs} (hqd : q ≠ d)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c) :
    Q.valueCell d = insertValue (occurrenceValue xs x) (P.valueCell d) := by
  classical
  unfold insertValue
  rw [Theorem21SetPartition.valueCell, hQcells d]
  simp only [Theorem21SetPartition.replaceUsedWithUnusedCells,
    if_neg hqd.symm, if_pos]
  ext a
  simp [Theorem21SetPartition.valueCell, eq_comm]

omit [AddCommGroup A] [Fintype A] in
/-- Every cell other than the source and target is unchanged by
cross-support replacement. -/
theorem Theorem21SetPartition.valueCell_eq_of_replaceUsedWithUnused_of_ne
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {y x : Occurrence xs}
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c)
    {c : Fin n} (hcq : c ≠ q) (hcd : c ≠ d) :
    Q.valueCell c = P.valueCell c := by
  classical
  rw [Theorem21SetPartition.valueCell, hQcells c]
  simp only [Theorem21SetPartition.replaceUsedWithUnusedCells,
    if_neg hcq, if_neg hcd]
  rfl

omit [AddCommGroup A] [Fintype A] in
/-- Exact value-set formula for same-cell cross-support replacement. -/
theorem Theorem21SetPartition.valueCell_eq_insert_erase_of_replaceSameCell
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q : Fin n} {y x : Occurrence xs} (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c) :
    Q.valueCell q =
      insertValue (occurrenceValue xs x)
        (eraseValue (P.valueCell q) (occurrenceValue xs y)) := by
  classical
  unfold insertValue eraseValue
  rw [Theorem21SetPartition.valueCell, hQcells q]
  simp only [Theorem21SetPartition.replaceUsedWithUnusedSameCell, if_pos]
  ext a
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨j, hj, hja⟩
    rcases Finset.mem_insert.mp hj with hjx | hjOld
    · subst j
      exact Finset.mem_insert.mpr (Or.inl hja.symm)
    · have hjData := Finset.mem_erase.mp hjOld
      apply Finset.mem_insert.mpr
      right
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image.mpr ⟨j, hjData.2, hja⟩⟩
      intro hay
      apply hjData.1
      apply P.value_injective q hjData.2 hyq
      rw [hja, hay]
  · intro ha
    rcases Finset.mem_insert.mp ha with hax | haOld
    · apply Finset.mem_image.mpr
      exact ⟨x, Finset.mem_insert.mpr (Or.inl rfl), hax.symm⟩
    · have haData := Finset.mem_erase.mp haOld
      rcases Finset.mem_image.mp haData.2 with ⟨j, hj, hja⟩
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_insert.mpr (Or.inr
        (Finset.mem_erase.mpr ⟨?_, hj⟩)), hja⟩
      intro hjy
      subst j
      exact haData.1 hja.symm

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.valueCell_eq_of_replaceSameCell_of_ne
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q : Fin n} {y x : Occurrence xs}
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c)
    {c : Fin n} (hcq : c ≠ q) :
    Q.valueCell c = P.valueCell c := by
  classical
  rw [Theorem21SetPartition.valueCell, hQcells c]
  simp only [Theorem21SetPartition.replaceUsedWithUnusedSameCell, if_neg hcq]
  rfl

omit [Fintype A] in
/-- A same-support occurrence move stays in the literal source `Lambda_0`
family when it enlarges the full sumset and does not erase the distinguished
anchor value of its source cell. -/
theorem GMOReplacementAdmissible.moveOccurrence
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q d : Fin n} {i : Occurrence xs}
    (hP : GMOReplacementAdmissible I P)
    (hqd : q ≠ d)
    (hiq : i ∈ P.cells q)
    (hanchor : occurrenceValue xs (I.anchor q) ≠ occurrenceValue xs i)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (hsumset : P.sumset ⊆ Q.sumset) :
    GMOReplacementAdmissible I Q := by
  classical
  constructor
  · exact hP.1.trans hsumset
  · intro c
    by_cases hcq : c = q
    · subst c
      rw [P.valueCell_eq_erase_of_moveOccurrence hiq hQcells]
      unfold eraseValue
      exact Finset.mem_erase.mpr ⟨hanchor, hP.2 q⟩
    · by_cases hcd : c = d
      · subst c
        rw [P.valueCell_eq_insert_of_moveOccurrence hqd hQcells]
        unfold insertValue
        exact Finset.mem_insert_of_mem (hP.2 d)
      · rw [P.valueCell_eq_of_moveOccurrence_of_ne hQcells hcq hcd]
        exact hP.2 c

omit [Fintype A] in
/-- Cross-support replacement remains in the literal source family once
the full sumset is monotone and the erased value is not the distinguished
anchor value of its source cell. -/
theorem GMOReplacementAdmissible.replaceUsedWithUnused
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q d : Fin n} {y x : Occurrence xs}
    (hP : GMOReplacementAdmissible I P)
    (hqd : q ≠ d)
    (hyq : y ∈ P.cells q)
    (hanchor : occurrenceValue xs (I.anchor q) ≠ occurrenceValue xs y)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c)
    (hsumset : P.sumset ⊆ Q.sumset) :
    GMOReplacementAdmissible I Q := by
  classical
  constructor
  · exact hP.1.trans hsumset
  · intro c
    by_cases hcq : c = q
    · subst c
      rw [P.valueCell_eq_erase_of_replaceUsedWithUnused hyq hQcells]
      unfold eraseValue
      exact Finset.mem_erase.mpr ⟨hanchor, hP.2 q⟩
    · by_cases hcd : c = d
      · subst c
        rw [P.valueCell_eq_insert_of_replaceUsedWithUnused hqd hQcells]
        unfold insertValue
        exact Finset.mem_insert_of_mem (hP.2 d)
      · rw [P.valueCell_eq_of_replaceUsedWithUnused_of_ne hQcells hcq hcd]
        exact hP.2 c

omit [Fintype A] in
/-- Literal source admissibility for same-cell cross-support replacement.
The anchor condition is stated at the exact resulting value set, allowing
the erased anchor value to be restored by the inserted occurrence. -/
theorem GMOReplacementAdmissible.replaceUsedWithUnusedSameCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q : Fin n} {y x : Occurrence xs}
    (hP : GMOReplacementAdmissible I P)
    (hyq : y ∈ P.cells q)
    (hanchor : occurrenceValue xs (I.anchor q) ∈
      insertValue (occurrenceValue xs x)
        (eraseValue (P.valueCell q) (occurrenceValue xs y)))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c)
    (hsumset : P.sumset ⊆ Q.sumset) :
    GMOReplacementAdmissible I Q := by
  classical
  constructor
  · exact hP.1.trans hsumset
  · intro c
    by_cases hcq : c = q
    · subst c
      rw [P.valueCell_eq_insert_erase_of_replaceSameCell hyq hQcells]
      exact hanchor
    · rw [P.valueCell_eq_of_replaceSameCell_of_ne hQcells hcq]
      exact hP.2 c

omit [Fintype A] in
/-- Quotient-image form of the source-cell erase wrapper. -/
theorem quotientLayer_eraseValue_eq_of_duplicate
    (H : AddSubgroup A) (C : Finset A) {x y : A}
    (hy : y ∈ C) (hxy : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x) :
    quotientLayer H (eraseValue C x) = quotientLayer H C := by
  classical
  unfold eraseValue
  exact quotientLayer_erase_eq_of_duplicate H C hy hxy hquot

omit [Fintype A] in
/-- Quotient-cardinality form of the target-cell insert wrapper. -/
theorem card_quotientLayer_insertValue_of_not_mem
    (H : AddSubgroup A) (C : Finset A) (x : A)
    (hx : QuotientAddGroup.mk' H x ∉ quotientLayer H C) :
    (quotientLayer H (insertValue x C)).card =
      (quotientLayer H C).card + 1 := by
  classical
  unfold insertValue
  exact card_quotientLayer_insert_of_not_mem H C x hx

omit [Fintype A] in
/-- The exchange forced by a doubled exception raises Definition 1's first
positive-stage objective by exactly one: the source cell loses no quotient
class, the exception cell gains one, and every other cell is unchanged. -/
theorem Theorem21SetPartition.quotientIncidenceAt_move_eq_add_one
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    (H : AddSubgroup A) {q d : Fin n} {i : Occurrence xs} {x : A}
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell H q x)
    (hmissing : QuotientAddGroup.mk' H x ∉
      quotientLayer H (P.valueCell d))
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c) :
    Q.quotientIncidenceAt H = P.quotientIncidenceAt H + 1 := by
  classical
  rcases hdouble with ⟨hxq, y, hyq, hyx, hyquot⟩
  have hsource : quotientLayer H (Q.valueCell q) =
      quotientLayer H (P.valueCell q) := by
    rw [Theorem21SetPartition.valueCell_eq_erase_of_moveOccurrence
      (P := P) (Q := Q) (q := q) (d := d) (i := i) hiq hQcells]
    apply quotientLayer_eraseValue_eq_of_duplicate H (P.valueCell q) hyq
    · simpa [hix] using hyx
    · simpa [hix] using hyquot
  have htarget : (quotientLayer H (Q.valueCell d)).card =
      (quotientLayer H (P.valueCell d)).card + 1 := by
    rw [Theorem21SetPartition.valueCell_eq_insert_of_moveOccurrence
      (P := P) (Q := Q) (q := q) (d := d) (i := i) hqd hQcells]
    simpa [hix] using card_quotientLayer_insertValue_of_not_mem
      H (P.valueCell d) x hmissing
  have hcell (c : Fin n) :
      (quotientLayer H (Q.valueCell c)).card =
        (quotientLayer H (P.valueCell c)).card + if c = d then 1 else 0 := by
    by_cases hcq : c = q
    · subst c
      rw [hsource]
      simp [hqd]
    · by_cases hcd : c = d
      · subst c
        simpa using htarget
      · rw [Theorem21SetPartition.valueCell_eq_of_moveOccurrence_of_ne
          (P := P) (Q := Q) (q := q) (d := d) (i := i) hQcells hcq hcd]
        simp [hcd]
  unfold Theorem21SetPartition.quotientIncidenceAt
  simp_rw [hcell]
  rw [Finset.sum_add_distrib]
  simp

omit [Fintype A] in
/-- If the erased occurrence has another representative in its source
quotient class and the inserted occurrence enters a missing target class,
cross-support replacement raises the quotient-incidence objective by
exactly one. -/
theorem Theorem21SetPartition.quotientIncidenceAt_replace_eq_add_one
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    (H : AddSubgroup A) {q d : Fin n} {y x : Occurrence xs}
    (hqd : q ≠ d) (hyq : y ∈ P.cells q)
    (hduplicate :
      ∃ z ∈ P.valueCell q,
        z ≠ occurrenceValue xs y ∧
        QuotientAddGroup.mk' H z =
          QuotientAddGroup.mk' H (occurrenceValue xs y))
    (hmissing : QuotientAddGroup.mk' H (occurrenceValue xs x) ∉
      quotientLayer H (P.valueCell d))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c) :
    Q.quotientIncidenceAt H = P.quotientIncidenceAt H + 1 := by
  classical
  rcases hduplicate with ⟨z, hzq, hzy, hzquot⟩
  have hsource : quotientLayer H (Q.valueCell q) =
      quotientLayer H (P.valueCell q) := by
    rw [Theorem21SetPartition.valueCell_eq_erase_of_replaceUsedWithUnused
      (P := P) (Q := Q) hyq hQcells]
    exact quotientLayer_eraseValue_eq_of_duplicate H (P.valueCell q)
      hzq hzy hzquot
  have htarget : (quotientLayer H (Q.valueCell d)).card =
      (quotientLayer H (P.valueCell d)).card + 1 := by
    rw [Theorem21SetPartition.valueCell_eq_insert_of_replaceUsedWithUnused
      (P := P) (Q := Q) hqd hQcells]
    exact card_quotientLayer_insertValue_of_not_mem H (P.valueCell d)
      (occurrenceValue xs x) hmissing
  have hcell (c : Fin n) :
      (quotientLayer H (Q.valueCell c)).card =
        (quotientLayer H (P.valueCell c)).card + if c = d then 1 else 0 := by
    by_cases hcq : c = q
    · subst c
      rw [hsource]
      simp [hqd]
    · by_cases hcd : c = d
      · subst c
        simpa using htarget
      · rw [Theorem21SetPartition.valueCell_eq_of_replaceUsedWithUnused_of_ne
          (P := P) (Q := Q) hQcells hcq hcd]
        simp [hcd]
  unfold Theorem21SetPartition.quotientIncidenceAt
  simp_rw [hcell]
  rw [Finset.sum_add_distrib]
  simp

omit [Fintype A] in
/-- Same-cell cross-support replacement raises quotient incidence by one
when the erased class is duplicated and the inserted class was absent. -/
theorem Theorem21SetPartition.quotientIncidenceAt_replaceSameCell_eq_add_one
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    (H : AddSubgroup A) {q : Fin n} {y x : Occurrence xs}
    (hyq : y ∈ P.cells q)
    (hduplicate :
      ∃ z ∈ P.valueCell q,
        z ≠ occurrenceValue xs y ∧
        QuotientAddGroup.mk' H z =
          QuotientAddGroup.mk' H (occurrenceValue xs y))
    (hmissing : QuotientAddGroup.mk' H (occurrenceValue xs x) ∉
      quotientLayer H (P.valueCell q))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c) :
    Q.quotientIncidenceAt H = P.quotientIncidenceAt H + 1 := by
  classical
  rcases hduplicate with ⟨z, hzq, hzy, hzquot⟩
  have hchanged :
      (quotientLayer H (Q.valueCell q)).card =
        (quotientLayer H (P.valueCell q)).card + 1 := by
    rw [P.valueCell_eq_insert_erase_of_replaceSameCell hyq hQcells]
    have herase : quotientLayer H
        (eraseValue (P.valueCell q) (occurrenceValue xs y)) =
          quotientLayer H (P.valueCell q) :=
      quotientLayer_eraseValue_eq_of_duplicate H (P.valueCell q)
        hzq hzy hzquot
    rw [card_quotientLayer_insertValue_of_not_mem H
      (eraseValue (P.valueCell q) (occurrenceValue xs y))
      (occurrenceValue xs x)]
    · rw [herase]
    · simpa [herase] using hmissing
  have hcell (c : Fin n) :
      (quotientLayer H (Q.valueCell c)).card =
        (quotientLayer H (P.valueCell c)).card + if c = q then 1 else 0 := by
    by_cases hcq : c = q
    · subst c
      simpa using hchanged
    · rw [P.valueCell_eq_of_replaceSameCell_of_ne hQcells hcq]
      simp [hcq]
  unfold Theorem21SetPartition.quotientIncidenceAt
  simp_rw [hcell]
  rw [Finset.sum_add_distrib]
  simp

omit [Fintype A] in
/-- Quotient equality modulo a smaller subgroup remains quotient equality
modulo every larger subgroup. -/
theorem quotient_eq_of_subgroup_le
    {H K : AddSubgroup A} (hHK : H ≤ K) {x y : A}
    (hxy : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) :
    QuotientAddGroup.mk' K x = QuotientAddGroup.mk' K y := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact hHK (QuotientAddGroup.eq_iff_sub_mem.mp hxy)

omit [Fintype A] in
/-- Moving one representative of a quotient-duplicated source class cannot
delete any cellwise quotient image for a larger subgroup.  The source image
is unchanged, the target image only grows, and all other images are fixed.
This is the quotient-image half of the repeated (3.1) admissibility check. -/
theorem Theorem21SetPartition.quotientImagesIncluded_moveOccurrence_of_mono
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {H K : AddSubgroup A} (hHK : H ≤ K)
    {q d : Fin n} {i : Occurrence xs} {x : A}
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell H q x)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c) :
    P.quotientImagesIncluded Q K := by
  classical
  rcases hdouble with ⟨_hxq, y, hyq, hyx, hyquot⟩
  have hyquotK : QuotientAddGroup.mk' K y =
      QuotientAddGroup.mk' K (occurrenceValue xs i) := by
    apply quotient_eq_of_subgroup_le hHK
    simpa [hix] using hyquot
  intro c
  by_cases hcq : c = q
  · subst c
    rw [Theorem21SetPartition.valueCell_eq_erase_of_moveOccurrence
      (P := P) (Q := Q) (q := q) (d := d) (i := i) hiq hQcells]
    rw [quotientLayer_eraseValue_eq_of_duplicate K (P.valueCell q) hyq
      (by simpa [hix] using hyx) hyquotK]
  · by_cases hcd : c = d
    · subst c
      rw [Theorem21SetPartition.valueCell_eq_insert_of_moveOccurrence
        (P := P) (Q := Q) (q := q) (d := d) (i := i) hqd hQcells]
      intro z hz
      obtain ⟨a, ha, haz⟩ :=
        (mem_quotientLayer_iff K (P.valueCell d) z).1 hz
      apply (mem_quotientLayer_iff K
        (insertValue (occurrenceValue xs i) (P.valueCell d)) z).2
      refine ⟨a, ?_, haz⟩
      unfold insertValue
      exact Finset.mem_insert_of_mem ha
    · rw [Theorem21SetPartition.valueCell_eq_of_moveOccurrence_of_ne
        (P := P) (Q := Q) (q := q) (d := d) (i := i) hQcells hcq hcd]

omit [Fintype A] in
/-- A cross-support replacement whose erased source class is duplicated
preserves every old cellwise quotient image modulo every larger subgroup. -/
theorem Theorem21SetPartition.quotientImagesIncluded_replace_of_mono
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {H K : AddSubgroup A} (hHK : H ≤ K)
    {q d : Fin n} {y x : Occurrence xs}
    (hqd : q ≠ d) (hyq : y ∈ P.cells q)
    (hduplicate :
      ∃ z ∈ P.valueCell q,
        z ≠ occurrenceValue xs y ∧
        QuotientAddGroup.mk' H z =
          QuotientAddGroup.mk' H (occurrenceValue xs y))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c) :
    P.quotientImagesIncluded Q K := by
  classical
  rcases hduplicate with ⟨z, hzq, hzy, hzquot⟩
  have hzquotK : QuotientAddGroup.mk' K z =
      QuotientAddGroup.mk' K (occurrenceValue xs y) :=
    quotient_eq_of_subgroup_le hHK hzquot
  intro c
  by_cases hcq : c = q
  · subst c
    rw [Theorem21SetPartition.valueCell_eq_erase_of_replaceUsedWithUnused
      (P := P) (Q := Q) hyq hQcells]
    rw [quotientLayer_eraseValue_eq_of_duplicate K (P.valueCell q)
      hzq hzy hzquotK]
  · by_cases hcd : c = d
    · subst c
      rw [Theorem21SetPartition.valueCell_eq_insert_of_replaceUsedWithUnused
        (P := P) (Q := Q) hqd hQcells]
      intro u hu
      obtain ⟨a, ha, hau⟩ :=
        (mem_quotientLayer_iff K (P.valueCell d) u).1 hu
      apply (mem_quotientLayer_iff K
        (insertValue (occurrenceValue xs x) (P.valueCell d)) u).2
      refine ⟨a, ?_, hau⟩
      unfold insertValue
      exact Finset.mem_insert_of_mem ha
    · rw [Theorem21SetPartition.valueCell_eq_of_replaceUsedWithUnused_of_ne
        (P := P) (Q := Q) hQcells hcq hcd]

omit [Fintype A] in
/-- Same-cell replacement also preserves every old quotient image modulo
all larger subgroups when the erased source class is duplicated. -/
theorem Theorem21SetPartition.quotientImagesIncluded_replaceSameCell_of_mono
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {H K : AddSubgroup A} (hHK : H ≤ K)
    {q : Fin n} {y x : Occurrence xs}
    (hyq : y ∈ P.cells q)
    (hduplicate :
      ∃ z ∈ P.valueCell q,
        z ≠ occurrenceValue xs y ∧
        QuotientAddGroup.mk' H z =
          QuotientAddGroup.mk' H (occurrenceValue xs y))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c) :
    P.quotientImagesIncluded Q K := by
  classical
  rcases hduplicate with ⟨z, hzq, hzy, hzquot⟩
  have hzquotK : QuotientAddGroup.mk' K z =
      QuotientAddGroup.mk' K (occurrenceValue xs y) :=
    quotient_eq_of_subgroup_le hHK hzquot
  intro c
  by_cases hcq : c = q
  · subst c
    rw [P.valueCell_eq_insert_erase_of_replaceSameCell hyq hQcells]
    have herase : quotientLayer K
        (eraseValue (P.valueCell q) (occurrenceValue xs y)) =
          quotientLayer K (P.valueCell q) :=
      quotientLayer_eraseValue_eq_of_duplicate K (P.valueCell q)
        hzq hzy hzquotK
    intro u hu
    rw [← herase] at hu
    obtain ⟨a, ha, hau⟩ := (mem_quotientLayer_iff K
      (eraseValue (P.valueCell q) (occurrenceValue xs y)) u).1 hu
    apply (mem_quotientLayer_iff K
      (insertValue (occurrenceValue xs x)
        (eraseValue (P.valueCell q) (occurrenceValue xs y))) u).2
    refine ⟨a, ?_, hau⟩
    unfold insertValue
    exact Finset.mem_insert_of_mem ha
  · rw [P.valueCell_eq_of_replaceSameCell_of_ne hQcells hcq]

omit [Fintype A] in
/-- Cellwise quotient-image inclusion is transitive. -/
theorem Theorem21SetPartition.quotientImagesIncluded_trans
    {xs : List A} {n m : ℕ} {P Q R : Theorem21SetPartition xs n m}
    {H : AddSubgroup A}
    (hPQ : P.quotientImagesIncluded Q H)
    (hQR : Q.quotientImagesIncluded R H) :
    P.quotientImagesIncluded R H := by
  intro c
  exact (hPQ c).trans (hQR c)

omit [Fintype A] in
/-- A doubled exception therefore produces an honest replacement with the
same labelled support and strictly larger quotient-incidence objective. -/
theorem Theorem21SetPartition.exists_moveOccurrence_quotientIncidenceAt_eq_add_one
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) {x : A} (hx : P.IsHDoubledException H x) :
    ∃ Q : Theorem21SetPartition xs n m,
      Q.support = P.support ∧
      Q.quotientIncidenceAt H = P.quotientIncidenceAt H + 1 := by
  classical
  rcases hx with ⟨⟨d, hdMissing⟩, q, hxq, y, hyq, hyx, hyquot⟩
  rcases Finset.mem_image.mp hxq with ⟨i, hiq, hix⟩
  rcases Finset.mem_image.mp hyq with ⟨j, hjq, hjy⟩
  have hqd : q ≠ d := by
    intro hqd
    subst d
    apply hdMissing
    exact (mem_quotientLayer_iff H (P.valueCell q) _).2 ⟨x, hxq, rfl⟩
  have hji : j ≠ i := by
    intro hji
    subst j
    apply hyx
    rw [← hix, ← hjy]
  have htarget : ∀ k ∈ P.cells d,
      occurrenceValue xs k ≠ occurrenceValue xs i := by
    intro k hkd hkvalue
    apply hdMissing
    apply (mem_quotientLayer_iff H (P.valueCell d) _).2
    refine ⟨occurrenceValue xs k, Finset.mem_image.mpr ⟨k, hkd, rfl⟩, ?_⟩
    simp [hkvalue, hix]
  obtain ⟨Q, hQcells, hQsupport⟩ := P.exists_moveOccurrence
    hqd hiq ⟨j, hjq, hji⟩ htarget
  refine ⟨Q, hQsupport, ?_⟩
  exact P.quotientIncidenceAt_move_eq_add_one H hqd hiq hix
    ⟨hxq, y, hyq, hyx, hyquot⟩ hdMissing hQcells

omit [Fintype A] in
/-- The incidence-maximality clause in one Definition 1 transition forbids
any admissible fixed-tail candidate from increasing the objective by one.
This is the exact contradiction consumed after the exchange has been shown
to remain in the recursively defined candidate family. -/
theorem Definition1Transition.not_exists_incidence_add_one
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous next F)
    {P : Theorem21SetPartition xs n seed.card}
    (hPincidence : P.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)) =
      F.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A))) :
    ¬ ∃ Q : Theorem21SetPartition xs n seed.card,
      Q ∈ previous.upsilon ∧
      Q.tailSumset r = previous.chosen.tailSumset r ∧
      Q.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) =
      P.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) + 1 := by
  rintro ⟨Q, hQmem, hQtail, hQinc⟩
  have hQmax := step.incidence_maximal Q hQmem hQtail
  rw [hQinc, hPincidence] at hQmax
  omega

omit [Fintype A] in
/-- Base-stage monotone closure used in the proof of dissertation Lemma 1:
if an already maximal full sumset is included in another replacement sumset,
then the latter is maximal as well and belongs to `Υ₀`. -/
theorem Definition1InitialValid.mem_of_sumset_subset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {state : Definition1ExtremalState xs seed n}
    (valid : Definition1InitialValid state)
    {P Q : Theorem21SetPartition xs n seed.card}
    (hPmem : P ∈ state.upsilon) (hsubset : P.sumset ⊆ Q.sumset) :
    Q ∈ state.upsilon := by
  have hPcard : P.sumset.card = state.chosen.sumset.card :=
    (valid.mem_upsilon_iff P).1 hPmem
  have hPQcard : P.sumset.card ≤ Q.sumset.card :=
    Finset.card_le_card hsubset
  have hQmax := valid.maximal Q
  apply (valid.mem_upsilon_iff Q).2
  omega

omit [Fintype A] in
/-- Source-family base-stage monotone closure.  In addition to full-sumset
inclusion, the replacement must remain literally `Lambda_0`-admissible. -/
theorem Definition1InitialValidUnder.mem_of_sumset_subset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (valid : Definition1InitialValidUnder I state)
    {P Q : Theorem21SetPartition xs n seed.card}
    (hPmem : P ∈ state.upsilon)
    (hQadmissible : GMOReplacementAdmissible I Q)
    (hsubset : P.sumset ⊆ Q.sumset) :
    Q ∈ state.upsilon := by
  have hPdata := (valid.mem_upsilon_iff P).1 hPmem
  have hPQcard : P.sumset.card ≤ Q.sumset.card :=
    Finset.card_le_card hsubset
  have hQmax := valid.maximal Q hQadmissible
  apply (valid.mem_upsilon_iff Q).2
  exact ⟨hQadmissible, by omega⟩

omit [Fintype A] in
/-- Successor-stage monotone closure from the recursive Definition 1 data.
The four hypotheses are exactly the checks made in the paper's "simple
inductive argument": the replacement survived the previous stage, fixes the
current tail, contains every required quotient image, and enlarges the next
tail of an already maximal member.  Both maximized cardinalities are then
forced to equality, so the replacement belongs to the next `Υ`. -/
theorem Definition1Transition.mem_next_of_monotone
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous next F)
    {P Q : Theorem21SetPartition xs n seed.card}
    (hPnext : P ∈ next.upsilon)
    (hQprevious : Q ∈ previous.upsilon)
    (hQtail : Q.tailSumset r = previous.chosen.tailSumset r)
    (hFimagesQ : F.quotientImagesIncluded Q
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)))
    (hPtailSubsetQ : P.tailSumset (r + 1) ⊆ Q.tailSumset (r + 1)) :
    Q ∈ next.upsilon := by
  classical
  let H : AddSubgroup A := AddAction.stabilizer A
    (previous.chosen.tailSumset r : Set A)
  have hQincLe : Q.quotientIncidenceAt H ≤ F.quotientIncidenceAt H :=
    step.incidence_maximal Q hQprevious hQtail
  have hFincLe : F.quotientIncidenceAt H ≤ Q.quotientIncidenceAt H := by
    unfold Theorem21SetPartition.quotientIncidenceAt
    apply Finset.sum_le_sum
    intro c _
    exact Finset.card_le_card (hFimagesQ c)
  have hQinc : Q.quotientIncidenceAt H = F.quotientIncidenceAt H :=
    Nat.le_antisymm hQincLe hFincLe
  have hQtailLe : (Q.tailSumset (r + 1)).card ≤
      (next.chosen.tailSumset (r + 1)).card :=
    step.tail_maximal Q hQprevious hQtail hQinc hFimagesQ
  have hPdata := (step.mem_next_upsilon_iff P).1 hPnext
  have hPcard : (P.tailSumset (r + 1)).card =
      (next.chosen.tailSumset (r + 1)).card := hPdata.2.2.2.2
  have hPcardLeQ : (P.tailSumset (r + 1)).card ≤
      (Q.tailSumset (r + 1)).card := Finset.card_le_card hPtailSubsetQ
  have hQcard : (Q.tailSumset (r + 1)).card =
      (next.chosen.tailSumset (r + 1)).card := by
    omega
  apply (step.mem_next_upsilon_iff Q).2
  exact ⟨hQprevious, hQtail, hQinc, hFimagesQ, hQcard⟩

/-- Recursive admissibility certificate for the paper's exchange argument
along an actual Definition 1 chain.  It records only the monotone inclusions
and fixed-tail facts used at each stage, not membership conclusions. -/
inductive Definition1ExtremalChain.MonotoneReplacement
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P Q : Theorem21SetPartition xs n seed.card) :
    {r : ℕ} → {state : Definition1ExtremalState xs seed n} →
      Definition1ExtremalChain xs seed n r state → Prop
  | initial (state : Definition1ExtremalState xs seed n)
      (valid : Definition1InitialValid state)
      (hPmem : P ∈ state.upsilon) (hsubset : P.sumset ⊆ Q.sumset) :
      MonotoneReplacement P Q
        (Definition1ExtremalChain.initial state valid)
  | next {r : ℕ} {previous : Definition1ExtremalState xs seed n}
      (prior : Definition1ExtremalChain xs seed n r previous)
      (state : Definition1ExtremalState xs seed n)
      (F : Theorem21SetPartition xs n seed.card)
      (step : Definition1Transition r previous state F)
      (hprior : MonotoneReplacement P Q prior)
      (hPnext : P ∈ state.upsilon)
      (hQtail : Q.tailSumset r = previous.chosen.tailSumset r)
      (hFimagesQ : F.quotientImagesIncluded Q
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)))
      (hPtailSubsetQ : P.tailSumset (r + 1) ⊆ Q.tailSumset (r + 1)) :
      MonotoneReplacement P Q
        (Definition1ExtremalChain.next prior state F step)

omit [Fintype A] in
/-- The recursively recorded monotone exchange really remains in the final
maximal partition family.  This formalizes the entire abstract induction
behind the paragraph following equations (3.1)--(3.2) in Lemma 1. -/
theorem Definition1ExtremalChain.mem_final_of_monotoneReplacement
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {r : ℕ} {state : Definition1ExtremalState xs seed n}
    {P Q : Theorem21SetPartition xs n seed.card}
    (chain : Definition1ExtremalChain xs seed n r state)
    (hmono : Definition1ExtremalChain.MonotoneReplacement P Q chain) :
    Q ∈ state.upsilon := by
  induction hmono with
  | initial state valid hPmem hsubset =>
      exact valid.mem_of_sumset_subset hPmem hsubset
  | next prior state F step hprior hPnext hQtail hFimagesQ
      hPtailSubsetQ ih =>
      exact step.mem_next_of_monotone hPnext ih hQtail hFimagesQ
        hPtailSubsetQ

omit [Fintype A] in
/-- Membership in a stage fixes the cardinality of the tail whose index is
that stage.  At stage zero this is full-sumset maximality; at a successor it
is the final cardinality equality stored by the preceding transition. -/
theorem Definition1ExtremalChain.tail_card_eq_chosen_of_mem
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {r : ℕ} {state : Definition1ExtremalState xs seed n}
    (chain : Definition1ExtremalChain xs seed n r state)
    {Q : Theorem21SetPartition xs n seed.card}
    (hQ : Q ∈ state.upsilon) :
    (Q.tailSumset r).card = (state.chosen.tailSumset r).card := by
  cases chain with
  | initial state valid =>
      have hcard := (valid.mem_upsilon_iff Q).1 hQ
      simpa [Theorem21SetPartition.tailSumset,
        Theorem21SetPartition.tailValueCells,
        Theorem21SetPartition.sumset] using hcard
  | @next r previous prior state F step =>
      exact (step.mem_next_upsilon_iff Q).1 hQ |>.2.2.2.2

omit [Fintype A] in
/-- Practical successor constructor for the recursive exchange certificate.
The paper supplies inclusions (3.1), not an a priori equality for the current
tail.  Previous-stage membership fixes the relevant cardinality, so current
tail inclusion forces equality and supplies the `hQtail` field automatically.
-/
theorem Definition1ExtremalChain.MonotoneReplacement.next_of_tail_subsets
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous : Definition1ExtremalState xs seed n}
    {prior : Definition1ExtremalChain xs seed n r previous}
    {state : Definition1ExtremalState xs seed n}
    {F P Q : Theorem21SetPartition xs n seed.card}
    {step : Definition1Transition r previous state F}
    (hprior : MonotoneReplacement P Q prior)
    (hPnext : P ∈ state.upsilon)
    (hPtailSubsetQ : P.tailSumset r ⊆ Q.tailSumset r)
    (hFimagesQ : F.quotientImagesIncluded Q
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)))
    (hPnextTailSubsetQ : P.tailSumset (r + 1) ⊆
      Q.tailSumset (r + 1)) :
    MonotoneReplacement P Q
      (Definition1ExtremalChain.next prior state F step) := by
  have hQprevious := prior.mem_final_of_monotoneReplacement hprior
  have hQcard := prior.tail_card_eq_chosen_of_mem hQprevious
  have hPdata := (step.mem_next_upsilon_iff P).1 hPnext
  have hPtail : P.tailSumset r = previous.chosen.tailSumset r :=
    hPdata.2.1
  have hQtail : Q.tailSumset r = previous.chosen.tailSumset r := by
    exact (Finset.eq_of_subset_of_card_le
      (hPtail ▸ hPtailSubsetQ) (by rw [hQcard])).symm
  exact MonotoneReplacement.next prior state F step hprior hPnext hQtail
    hFimagesQ hPnextTailSubsetQ

/-- Recursive exchange certificate for the literal source chain.  Its base
case additionally records that the replacement remains in `Lambda_0`. -/
inductive Definition1SourceChain.MonotoneReplacement
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (P Q : Theorem21SetPartition xs n seed.card) :
    {r : ℕ} → {state : Definition1ExtremalState xs seed n} →
      Definition1SourceChain I r state → Prop
  | initial (state : Definition1ExtremalState xs seed n)
      (valid : Definition1InitialValidUnder I state)
      (hPmem : P ∈ state.upsilon)
      (hQadmissible : GMOReplacementAdmissible I Q)
      (hsubset : P.sumset ⊆ Q.sumset) :
      MonotoneReplacement P Q
        (Definition1SourceChain.initial state valid)
  | next {r : ℕ} {previous : Definition1ExtremalState xs seed n}
      (prior : Definition1SourceChain I r previous)
      (state : Definition1ExtremalState xs seed n)
      (F : Theorem21SetPartition xs n seed.card)
      (step : Definition1Transition r previous state F)
      (hprior : MonotoneReplacement P Q prior)
      (hPnext : P ∈ state.upsilon)
      (hQtail : Q.tailSumset r = previous.chosen.tailSumset r)
      (hFimagesQ : F.quotientImagesIncluded Q
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)))
      (hPtailSubsetQ : P.tailSumset (r + 1) ⊆ Q.tailSumset (r + 1)) :
      MonotoneReplacement P Q
        (Definition1SourceChain.next prior state F step)

omit [Fintype A] in
/-- A recorded source-chain exchange belongs to the final `Upsilon`. -/
theorem Definition1SourceChain.mem_final_of_monotoneReplacement
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    {P Q : Theorem21SetPartition xs n seed.card}
    (chain : Definition1SourceChain I r state)
    (hmono : Definition1SourceChain.MonotoneReplacement P Q chain) :
    Q ∈ state.upsilon := by
  induction hmono with
  | initial state valid hPmem hQadmissible hsubset =>
      exact valid.mem_of_sumset_subset hPmem hQadmissible hsubset
  | next prior state F step hprior hPnext hQtail hFimagesQ
      hPtailSubsetQ ih =>
      exact step.mem_next_of_monotone hPnext ih hQtail hFimagesQ
        hPtailSubsetQ

omit [Fintype A] in
/-- Stage membership fixes the relevant tail cardinality also for the
source-admissible chain. -/
theorem Definition1SourceChain.tail_card_eq_chosen_of_mem
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (chain : Definition1SourceChain I r state)
    {Q : Theorem21SetPartition xs n seed.card}
    (hQ : Q ∈ state.upsilon) :
    (Q.tailSumset r).card = (state.chosen.tailSumset r).card := by
  cases chain with
  | initial state valid =>
      have hcard := (valid.mem_upsilon_iff Q).1 hQ |>.2
      simpa [Theorem21SetPartition.tailSumset,
        Theorem21SetPartition.tailValueCells,
        Theorem21SetPartition.sumset] using hcard
  | @next r previous prior state F step =>
      exact (step.mem_next_upsilon_iff Q).1 hQ |>.2.2.2.2

omit [Fintype A] in
/-- Practical successor constructor for a literal source-chain exchange. -/
theorem Definition1SourceChain.MonotoneReplacement.next_of_tail_subsets
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {previous : Definition1ExtremalState xs seed n}
    {prior : Definition1SourceChain I r previous}
    {state : Definition1ExtremalState xs seed n}
    {F P Q : Theorem21SetPartition xs n seed.card}
    {step : Definition1Transition r previous state F}
    (hprior : MonotoneReplacement P Q prior)
    (hPnext : P ∈ state.upsilon)
    (hPtailSubsetQ : P.tailSumset r ⊆ Q.tailSumset r)
    (hFimagesQ : F.quotientImagesIncluded Q
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)))
    (hPnextTailSubsetQ : P.tailSumset (r + 1) ⊆
      Q.tailSumset (r + 1)) :
    MonotoneReplacement P Q
      (Definition1SourceChain.next prior state F step) := by
  have hQprevious := prior.mem_final_of_monotoneReplacement hprior
  have hQcard := prior.tail_card_eq_chosen_of_mem hQprevious
  have hPdata := (step.mem_next_upsilon_iff P).1 hPnext
  have hPtail : P.tailSumset r = previous.chosen.tailSumset r :=
    hPdata.2.1
  have hQtail : Q.tailSumset r = previous.chosen.tailSumset r := by
    exact (Finset.eq_of_subset_of_card_le
      (hPtail ▸ hPtailSubsetQ) (by rw [hQcard])).symm
  exact MonotoneReplacement.next prior state F step hprior hPnext hQtail
    hFimagesQ hPnextTailSubsetQ

omit [Fintype A] in
/-- Full-layer sumsets are monotone under layerwise inclusion. -/
theorem fullLayerSumSpectrum_mono
    [DecidableEq A]
    {P Q : List (Finset A)} (hPQ : List.Forall₂ (· ⊆ ·) P Q) :
    fullLayerSumSpectrum P ⊆ fullLayerSumSpectrum Q := by
  induction hPQ with
  | nil => exact Finset.Subset.rfl
  | @cons B C P Q hBC hPQ ih =>
      rw [fullLayerSumSpectrum_cons, fullLayerSumSpectrum_cons]
      intro z hz
      rcases Finset.mem_add.mp hz with ⟨b, hb, s, hs, rfl⟩
      exact Finset.mem_add.mpr ⟨b, hBC hb, s, ih hs, rfl⟩

omit [Fintype A] in
/-- Instance-independent cardinality wrapper for a full-layer sumset. -/
noncomputable def fullLayerCard (L : List (Finset A)) : ℕ := by
  classical
  exact (fullLayerSumSpectrum L).card

omit [Fintype A] in
/-- A global strict deficit for a full-layer sumset must already occur at
one genuine adjacent tail step.  The returned suffix is nonempty, so the
step is strictly before the last layer. -/
theorem exists_local_fullLayer_deficit
    (L : List (Finset A))
    (hL : IsNonemptySetPartition L) (hlen : 2 ≤ L.length)
    (hdeficit :
      fullLayerCard L <
        (L.map Finset.card).sum - L.length + 1) :
    ∃ pre B tail,
      L = pre ++ B :: tail ∧ tail ≠ [] ∧
        fullLayerCard (B :: tail) <
          fullLayerCard tail + B.card - 1 := by
  classical
  unfold fullLayerCard at *
  induction L with
  | nil => simp at hlen
  | cons B R ih =>
      have hB : B.Nonempty := hL B (by simp)
      have hR : IsNonemptySetPartition R := by
        intro C hC
        exact hL C (by simp [hC])
      have hRne : R ≠ [] := by
        intro hnil
        subst R
        simp at hlen
      by_cases hlocal :
          (fullLayerSumSpectrum (B :: R)).card <
            (fullLayerSumSpectrum R).card + B.card - 1
      · exact ⟨[], B, R, rfl, hRne, hlocal⟩
      · have hlocalLe :
            (fullLayerSumSpectrum R).card + B.card - 1 ≤
              (fullLayerSumSpectrum (B :: R)).card :=
          Nat.le_of_not_gt hlocal
        have hBcard : 1 ≤ B.card := Finset.card_pos.mpr hB
        have hRguard : R.length ≤ (R.map Finset.card).sum :=
          length_le_sum_layer_card R hR
        have hRdeficit :
            (fullLayerSumSpectrum R).card <
              (R.map Finset.card).sum - R.length + 1 := by
          by_contra hnot
          have hRlower :
              (R.map Finset.card).sum - R.length + 1 ≤
                (fullLayerSumSpectrum R).card :=
            Nat.le_of_not_gt hnot
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hdeficit
          omega
        by_cases hRlen : 2 ≤ R.length
        · obtain ⟨pre, C, tail, hsplit, htail, hstep⟩ :=
            ih hR hRlen hRdeficit
          refine ⟨B :: pre, C, tail, ?_, htail, hstep⟩
          simp [hsplit]
        · have hRlenOne : R.length = 1 := by
            have hpos : 0 < R.length := List.length_pos_iff.mpr hRne
            omega
          obtain ⟨C, rfl⟩ := List.length_eq_one_iff.mp hRlenOne
          have hCcard : 1 ≤ C.card :=
            Finset.card_pos.mpr (hR C (by simp))
          simp [fullLayerSumSpectrum_cons] at hRdeficit
          omega

omit [Fintype A] in
/-- Condition (III) of a factor form yields the exact local strict tail
step used in Lemma 5, before choosing a labelled occurrence from that cell.
-/
theorem FactorForm.exists_local_tail_deficit_decomposition
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n} (F : FactorForm I rho) :
    ∃ pre B tail,
      F.partition.tailValueCells rho = pre ++ B :: tail ∧
        tail ≠ [] ∧
        fullLayerCard (B :: tail) <
          fullLayerCard tail + B.card - 1 := by
  classical
  apply exists_local_fullLayer_deficit
  · intro B hB
    exact F.partition.valueCells_nonempty B (List.mem_of_mem_drop hB)
  · simp only [Theorem21SetPartition.tailValueCells, List.length_drop,
      F.partition.length_valueCells]
    have := F.range
    omega
  · have hdef := F.tail_deficit
    unfold Theorem21SetPartition.tailSumset at hdef
    unfold fullLayerCard
    rw [F.partition.sum_card_tailValueCells_eq_tailIndices]
    simp only [Theorem21SetPartition.tailValueCells, List.length_drop,
      F.partition.length_valueCells]
    exact hdef

omit [Fintype A] in
/-- Indexed form of the local deficit: the witness is a genuine tail cell
and is strictly before the last cell. -/
theorem FactorForm.exists_local_tail_deficit
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n} (F : FactorForm I rho) :
    ∃ q : Fin n,
      rho ≤ q.val ∧ q.val + 1 < n ∧
        (F.partition.tailSumset q.val).card <
          (F.partition.tailSumset (q.val + 1)).card +
            (F.partition.valueCell q).card - 1 := by
  classical
  obtain ⟨pre, B, tail, hsplit, htail, hdef⟩ :=
    F.exists_local_tail_deficit_decomposition
  have hlen := congrArg List.length hsplit
  have htailPos : 0 < tail.length := List.length_pos_iff.mpr htail
  have htailLength :
      (F.partition.tailValueCells rho).length = n - rho := by
    simp [Theorem21SetPartition.tailValueCells,
      F.partition.length_valueCells]
  rw [htailLength] at hlen
  simp only [List.length_append, List.length_cons] at hlen
  have hjlt : pre.length < n - rho := by omega
  let j : Fin (n - rho) := ⟨pre.length, hjlt⟩
  let q : Fin n := tailIndex n rho j
  have hqval : q.val = rho + pre.length := by simp [q, j]
  have hqnext : q.val + 1 < n := by
    rw [hqval]
    omega
  unfold Theorem21SetPartition.tailValueCells at hsplit
  have htailAt :
      F.partition.tailValueCells q.val = B :: tail := by
    unfold Theorem21SetPartition.tailValueCells
    rw [hqval, ← List.drop_drop, hsplit]
    simp
  have htailNext :
      F.partition.tailValueCells (q.val + 1) = tail := by
    unfold Theorem21SetPartition.tailValueCells
    rw [hqval]
    have hsum :
        rho + pre.length + 1 = rho + (pre.length + 1) := by omega
    rw [hsum, ← List.drop_drop, hsplit]
    simp
  have hB : B = F.partition.valueCell q := by
    have hget := congrArg
      (fun L : List (Finset A) ↦ L[0]?) htailAt
    simp only [List.getElem?_cons_zero] at hget
    unfold Theorem21SetPartition.tailValueCells
      Theorem21SetPartition.valueCells at hget
    simp only [List.getElem?_drop, List.getElem?_ofFn] at hget
    simp only [dif_pos (by omega : q.val + 0 < n)] at hget
    let c : Fin n := ⟨q.val + 0, by omega⟩
    change some (F.partition.valueCell c) = some B at hget
    have hc : c = q := by
      apply Fin.ext
      simp [c]
    rw [hc] at hget
    have hv : F.partition.valueCell q = B := by
      exact Option.some.inj hget
    exact hv.symm
  refine ⟨q, ?_, hqnext, ?_⟩
  · rw [hqval]
    exact Nat.le_add_right _ _
  · change fullLayerCard (F.partition.tailValueCells q.val) <
      fullLayerCard (F.partition.tailValueCells (q.val + 1)) +
        (F.partition.valueCell q).card - 1
    rw [htailAt, htailNext, ← hB]
    exact hdef

omit [AddCommGroup A] [Fintype A] in
/-- Pointwise relations on `Fin n` functions induce `Forall₂` on their
ordered `List.ofFn` realizations. -/
theorem forall₂_ofFn {X Y : Type*} {R : X → Y → Prop} {n : ℕ}
    {f : Fin n → X} {g : Fin n → Y} (h : ∀ i, R (f i) (g i)) :
    List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      exact List.Forall₂.cons (h 0) (ih (fun i ↦ h i.succ))

/-- Value-cell list after deleting only the moved value from its source cell.
It need not itself be a setpartition because the source cell might become
empty; it is the intermediate reduced sumset in Lemma 1. -/
noncomputable def Theorem21SetPartition.valueCellsAfterErase
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) : List (Finset A) := by
  classical
  exact List.ofFn fun c : Fin n ↦
    if c = q then eraseValue (P.valueCell c) x else P.valueCell c

/-- Tail of the intermediate reduced value-cell list. -/
noncomputable def Theorem21SetPartition.tailValueCellsAfterErase
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) (r : ℕ) : List (Finset A) :=
  (P.valueCellsAfterErase q x).drop r

/-- Full-layer sumset of an intermediate reduced tail. -/
noncomputable def Theorem21SetPartition.tailSumsetAfterErase
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) (r : ℕ) : Finset A := by
  classical
  exact fullLayerSumSpectrum (P.tailValueCellsAfterErase q x r)

/-- The tail value-cell list with one entire indexed cell omitted.  When
`r ≤ q`, the local zero-based position of cell `q` in the tail is
`q.val - r`.  This is the literal `\sum_{i ≠ q} Y_i` layer list in
dissertation Lemma 2. -/
noncomputable def Theorem21SetPartition.tailValueCellsWithoutCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (r : ℕ) : List (Finset A) :=
  (P.tailValueCells r).eraseIdx (q.val - r)

/-- Full-layer sumset of a tail after omitting the whole cell `q`. -/
noncomputable def Theorem21SetPartition.tailSumsetWithoutCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (r : ℕ) : Finset A := by
  classical
  exact fullLayerSumSpectrum (P.tailValueCellsWithoutCell q r)

omit [AddCommGroup A] [Fintype A] in
/-- The local index of a tail cell is in range. -/
theorem Theorem21SetPartition.sub_lt_length_tailValueCells
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : r ≤ q.val) :
    q.val - r < (P.tailValueCells r).length := by
  simp only [Theorem21SetPartition.tailValueCells, List.length_drop,
    P.length_valueCells]
  omega

omit [AddCommGroup A] [Fintype A] in
/-- Looking up the local position `q-r` in the tail recovers cell `q`. -/
theorem Theorem21SetPartition.getElem_tailValueCells_sub
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : r ≤ q.val) :
    (P.tailValueCells r)[q.val - r]'(P.sub_lt_length_tailValueCells q hrq) =
      P.valueCell q := by
  classical
  simp only [Theorem21SetPartition.tailValueCells,
    Theorem21SetPartition.valueCells, List.getElem_drop, List.getElem_ofFn]
  congr
  omega

omit [AddCommGroup A] [Fintype A] in
/-- Deleting local tail index `q-r` leaves the prefix before `q` and the
suffix after `q`. -/
theorem Theorem21SetPartition.tailValueCellsWithoutCell_eq
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : r ≤ q.val) :
    P.tailValueCellsWithoutCell q r =
      (P.valueCells.drop r).take (q.val - r) ++
        P.valueCells.drop (q.val + 1) := by
  unfold Theorem21SetPartition.tailValueCellsWithoutCell
    Theorem21SetPartition.tailValueCells
  rw [List.eraseIdx_eq_take_drop_succ, List.drop_drop]
  congr 2
  omega

omit [AddCommGroup A] [Fintype A] in
/-- Membership in an `eraseIdx` list came from the original list. -/
theorem List.mem_of_mem_eraseIdx' {X : Type*} {a : X}
    {L : List X} {i : ℕ} (ha : a ∈ L.eraseIdx i) : a ∈ L := by
  induction L generalizing i with
  | nil => simp at ha
  | cons b L ih =>
      cases i with
      | zero =>
          simp only [List.eraseIdx] at ha
          simpa only [List.mem_cons] using
            (Or.inr ha : a = b ∨ a ∈ L)
      | succ i =>
          simp only [List.eraseIdx, List.mem_cons] at ha ⊢
          exact ha.imp_right fun h ↦ ih h

omit [AddCommGroup A] [Fintype A] in
/-- Erasing a list position cannot create an empty layer. -/
theorem IsNonemptySetPartition.eraseIdx {X : Type*}
    {L : List (Finset X)} (hL : IsNonemptySetPartition L) (i : ℕ) :
    IsNonemptySetPartition (L.eraseIdx i) := by
  intro B hB
  exact hL B (List.mem_of_mem_eraseIdx' hB)

omit [AddCommGroup A] [Fintype A] in
/-- The omitted tail has exactly one fewer layer. -/
theorem Theorem21SetPartition.length_tailValueCellsWithoutCell
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : r ≤ q.val) :
    (P.tailValueCellsWithoutCell q r).length = n - r - 1 := by
  unfold Theorem21SetPartition.tailValueCellsWithoutCell
  have htail : (P.tailValueCells r).length = n - r := by
    simp only [Theorem21SetPartition.tailValueCells, List.length_drop,
      P.length_valueCells]
  have hlen := List.length_eraseIdx_add_one
    (P.sub_lt_length_tailValueCells q hrq)
  rw [htail] at hlen
  omega

omit [AddCommGroup A] [Fintype A] in
/-- Every retained layer of the omitted tail remains nonempty. -/
theorem Theorem21SetPartition.tailValueCellsWithoutCell_nonempty
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) :
    IsNonemptySetPartition (P.tailValueCellsWithoutCell q r) := by
  unfold Theorem21SetPartition.tailValueCellsWithoutCell
  exact (by
    apply IsNonemptySetPartition.eraseIdx
    intro B hB
    exact P.valueCells_nonempty B
      (List.mem_of_mem_drop hB) :
    IsNonemptySetPartition ((P.tailValueCells r).eraseIdx (q.val - r)))

omit [Fintype A] in
/-- Removing one layer from a full-layer list extracts that layer as one
pointwise summand. -/
theorem fullLayerSumSpectrum_eraseIdx_add_getElem
    [DecidableEq A] (L : List (Finset A)) (i : ℕ) (hi : i < L.length) :
    fullLayerSumSpectrum L =
      fullLayerSumSpectrum (L.eraseIdx i) + L[i] := by
  induction L generalizing i with
  | nil => simp at hi
  | cons B L ih =>
      cases i with
      | zero =>
          simp only [List.eraseIdx, List.getElem_cons_zero,
            fullLayerSumSpectrum_cons]
          exact add_comm B (fullLayerSumSpectrum L)
      | succ i =>
          have hiL : i < L.length := by simpa using hi
          simp only [List.eraseIdx, List.getElem_cons_succ,
            fullLayerSumSpectrum_cons, ih i hiL]
          ac_rfl

omit [Fintype A] in
/-- Membership form of the preceding decomposition; unlike a raw finset
equality it is insensitive to which extensionally equal decidable-equality
instance is used by a surrounding noncomputable definition. -/
theorem mem_fullLayerSumSpectrum_eraseIdx_iff
    [DecidableEq A] (L : List (Finset A)) (i : ℕ) (hi : i < L.length)
    (a : A) :
    a ∈ fullLayerSumSpectrum L ↔
      ∃ b ∈ fullLayerSumSpectrum (L.eraseIdx i),
        ∃ c ∈ L[i], b + c = a := by
  rw [fullLayerSumSpectrum_eraseIdx_add_getElem L i hi]
  simp only [Finset.mem_add]

omit [Fintype A] in
/-- Exact two-summand decomposition of a tail into the omitted-cell sumset
and cell `q`. -/
theorem Theorem21SetPartition.tailSumset_eq_withoutCell_add
    [DecidableEq A] {xs : List A} {n m r : ℕ}
    (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : r ≤ q.val) :
    P.tailSumset r = P.tailSumsetWithoutCell q r + P.valueCell q := by
  classical
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailSumsetWithoutCell
    Theorem21SetPartition.tailValueCellsWithoutCell
  apply Finset.ext
  intro a
  simpa only [Finset.mem_add, P.getElem_tailValueCells_sub q hrq] using
    (@mem_fullLayerSumSpectrum_eraseIdx_iff A _ (Classical.decEq A)
      (P.tailValueCells r) (q.val - r)
      (P.sub_lt_length_tailValueCells q hrq) a)

omit [AddCommGroup A] [Fintype A] in
/-- The reduced cell list is layerwise contained in the honest moved
partition: source is equal after erase, target only gains the moved value,
and all other cells are unchanged. -/
theorem Theorem21SetPartition.forall₂_valueCellsAfterErase_moveOccurrence
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs} (hqd : q ≠ d)
    (hiq : i ∈ P.cells q)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c) :
    List.Forall₂ (· ⊆ ·)
      (P.valueCellsAfterErase q (occurrenceValue xs i)) Q.valueCells := by
  classical
  unfold Theorem21SetPartition.valueCellsAfterErase
    Theorem21SetPartition.valueCells
  apply forall₂_ofFn
  intro c
  by_cases hcq : c = q
  · subst c
    rw [Theorem21SetPartition.valueCell_eq_erase_of_moveOccurrence
      (P := P) (Q := Q) (q := q) (d := d) (i := i) hiq hQcells]
    simp
  · by_cases hcd : c = d
    · subst c
      simp only [if_neg hqd.symm]
      rw [Theorem21SetPartition.valueCell_eq_insert_of_moveOccurrence
        (P := P) (Q := Q) (q := q) (d := d) (i := i) hqd hQcells]
      exact Finset.subset_insert _ _
    · simp only [if_neg hcq]
      rw [Theorem21SetPartition.valueCell_eq_of_moveOccurrence_of_ne
        (P := P) (Q := Q) (q := q) (d := d) (i := i) hQcells hcq hcd]

omit [AddCommGroup A] [Fintype A] in
/-- Every tail of the reduced cell list is likewise layerwise contained in
the corresponding tail of the moved partition. -/
theorem Theorem21SetPartition.forall₂_tailValueCellsAfterErase_moveOccurrence
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs} (hqd : q ≠ d)
    (hiq : i ∈ P.cells q)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (r : ℕ) :
    List.Forall₂ (· ⊆ ·) (P.tailValueCellsAfterErase q
      (occurrenceValue xs i) r) (Q.tailValueCells r) := by
  unfold Theorem21SetPartition.tailValueCellsAfterErase
    Theorem21SetPartition.tailValueCells
  exact List.forall₂_drop r
    (P.forall₂_valueCellsAfterErase_moveOccurrence hqd hiq hQcells)

omit [AddCommGroup A] [Fintype A] in
/-- The cell list with the used value erased is layerwise contained in the
honest cross-support replacement; the target insertion can only enlarge its
layer. -/
theorem Theorem21SetPartition.forall₂_valueCellsAfterErase_replaceUsedWithUnused
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {y x : Occurrence xs} (hqd : q ≠ d)
    (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c) :
    List.Forall₂ (· ⊆ ·)
      (P.valueCellsAfterErase q (occurrenceValue xs y)) Q.valueCells := by
  classical
  unfold Theorem21SetPartition.valueCellsAfterErase
    Theorem21SetPartition.valueCells
  apply forall₂_ofFn
  intro c
  by_cases hcq : c = q
  · subst c
    rw [Theorem21SetPartition.valueCell_eq_erase_of_replaceUsedWithUnused
      (P := P) (Q := Q) hyq hQcells]
    simp
  · by_cases hcd : c = d
    · subst c
      simp only [if_neg hqd.symm]
      rw [Theorem21SetPartition.valueCell_eq_insert_of_replaceUsedWithUnused
        (P := P) (Q := Q) hqd hQcells]
      exact Finset.subset_insert _ _
    · simp only [if_neg hcq]
      rw [Theorem21SetPartition.valueCell_eq_of_replaceUsedWithUnused_of_ne
        (P := P) (Q := Q) hQcells hcq hcd]

omit [AddCommGroup A] [Fintype A] in
/-- Every tail of the erased intermediate cell list is layerwise contained
in the corresponding tail of the cross-support replacement. -/
theorem Theorem21SetPartition.forall₂_tailValueCellsAfterErase_replaceUsedWithUnused
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {y x : Occurrence xs} (hqd : q ≠ d)
    (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c)
    (r : ℕ) :
    List.Forall₂ (· ⊆ ·) (P.tailValueCellsAfterErase q
      (occurrenceValue xs y) r) (Q.tailValueCells r) := by
  unfold Theorem21SetPartition.tailValueCellsAfterErase
    Theorem21SetPartition.tailValueCells
  exact List.forall₂_drop r
    (P.forall₂_valueCellsAfterErase_replaceUsedWithUnused
      hqd hyq hQcells)

omit [AddCommGroup A] [Fintype A] in
/-- The erased intermediate list is layerwise contained in a same-cell
cross-support replacement. -/
theorem Theorem21SetPartition.forall₂_valueCellsAfterErase_replaceSameCell
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q : Fin n} {y x : Occurrence xs} (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c) :
    List.Forall₂ (· ⊆ ·)
      (P.valueCellsAfterErase q (occurrenceValue xs y)) Q.valueCells := by
  classical
  unfold Theorem21SetPartition.valueCellsAfterErase
    Theorem21SetPartition.valueCells
  apply forall₂_ofFn
  intro c
  by_cases hcq : c = q
  · subst c
    rw [P.valueCell_eq_insert_erase_of_replaceSameCell hyq hQcells]
    simp only [if_pos]
    unfold insertValue
    intro a ha
    exact Finset.mem_insert_of_mem ha
  · simp only [if_neg hcq]
    rw [P.valueCell_eq_of_replaceSameCell_of_ne hQcells hcq]

omit [AddCommGroup A] [Fintype A] in
theorem Theorem21SetPartition.forall₂_tailValueCellsAfterErase_replaceSameCell
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q : Fin n} {y x : Occurrence xs} (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c)
    (r : ℕ) :
    List.Forall₂ (· ⊆ ·)
      (P.tailValueCellsAfterErase q (occurrenceValue xs y) r)
      (Q.tailValueCells r) := by
  unfold Theorem21SetPartition.tailValueCellsAfterErase
    Theorem21SetPartition.tailValueCells
  exact List.forall₂_drop r
    (P.forall₂_valueCellsAfterErase_replaceSameCell hyq hQcells)

omit [Fintype A] in
/-- Concrete tail-inclusion consequence used for equation (3.1): whenever
deleting the doubled representative does not change an old tail sumset, that
old tail is contained in the corresponding tail of the honest moved
partition. -/
theorem Theorem21SetPartition.tailSumset_subset_moveOccurrence_of_erase_eq
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs} (hqd : q ≠ d)
    (hiq : i ∈ P.cells q)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (r : ℕ)
    (herase : P.tailSumset r = P.tailSumsetAfterErase q
      (occurrenceValue xs i) r) :
    P.tailSumset r ⊆ Q.tailSumset r := by
  classical
  rw [herase]
  unfold Theorem21SetPartition.tailSumsetAfterErase
    Theorem21SetPartition.tailSumset
  exact fullLayerSumSpectrum_mono
    (P.forall₂_tailValueCellsAfterErase_moveOccurrence hqd hiq hQcells r)

omit [Fintype A] in
/-- If deleting the used occurrence's value leaves an old tail sumset
unchanged, that tail is contained in the corresponding tail of the honest
cross-support replacement. -/
theorem Theorem21SetPartition.tailSumset_subset_replaceUsedWithUnused_of_erase_eq
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {y x : Occurrence xs} (hqd : q ≠ d)
    (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c)
    (r : ℕ)
    (herase : P.tailSumset r = P.tailSumsetAfterErase q
      (occurrenceValue xs y) r) :
    P.tailSumset r ⊆ Q.tailSumset r := by
  classical
  rw [herase]
  unfold Theorem21SetPartition.tailSumsetAfterErase
    Theorem21SetPartition.tailSumset
  exact fullLayerSumSpectrum_mono
    (P.forall₂_tailValueCellsAfterErase_replaceUsedWithUnused
      hqd hyq hQcells r)

omit [Fintype A] in
theorem Theorem21SetPartition.tailSumset_subset_replaceSameCell_of_erase_eq
    {xs : List A} {n m : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q : Fin n} {y x : Occurrence xs} (hyq : y ∈ P.cells q)
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c)
    (r : ℕ)
    (herase : P.tailSumset r = P.tailSumsetAfterErase q
      (occurrenceValue xs y) r) :
    P.tailSumset r ⊆ Q.tailSumset r := by
  classical
  rw [herase]
  unfold Theorem21SetPartition.tailSumsetAfterErase
    Theorem21SetPartition.tailSumset
  exact fullLayerSumSpectrum_mono
    (P.forall₂_tailValueCellsAfterErase_replaceSameCell hyq hQcells r)

omit [AddCommGroup A] [Fintype A] in
/-- Replacing a valid list position and then dropping an earlier prefix gives
the unchanged intermediate prefix, the replacement, and the old suffix.
This is the list bookkeeping behind the paper's removal of `x` from cell
`q` in every tail beginning no later than `q`. -/
theorem List.drop_set_eq_take_append_cons_drop
    {X : Type*} (L : List X) (x : X) {r q : ℕ}
    (hrq : r ≤ q) (hq : q < L.length) :
    (L.set q x).drop r =
      (L.drop r).take (q - r) ++ x :: L.drop (q + 1) := by
  induction r generalizing L q with
  | zero =>
      induction L generalizing q with
      | nil => simp at hq
      | cons a L ih =>
          cases q with
          | zero => simp
          | succ q =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff] at hq
              simpa using ih (q := q) (Nat.zero_le q) hq
  | succ r ih =>
      cases L with
      | nil => simp at hq
      | cons a L =>
          cases q with
          | zero => omega
          | succ q =>
              have hrq' : r ≤ q := by omega
              have hq' : q < L.length := by simpa using hq
              simpa using ih (L := L) (q := q) hrq' hq'

omit [AddCommGroup A] [Fintype A] in
/-- Updating a position strictly before the dropped prefix has no effect on
the resulting suffix. -/
theorem List.drop_set_eq_of_lt
    {X : Type*} (L : List X) (x : X) {q r : ℕ} (hqr : q < r) :
    (L.set q x).drop r = L.drop r := by
  induction r generalizing L q with
  | zero => omega
  | succ r ih =>
      cases L with
      | nil => simp
      | cons a L =>
          cases q with
          | zero => simp
          | succ q =>
              simp only [List.set, List.drop_succ_cons]
              exact ih (L := L) (q := q) (by omega)

omit [AddCommGroup A] [Fintype A] in
/-- Updating one coordinate of a finite tuple and converting it to a list is
the same as converting first and using `List.set`. -/
theorem List.ofFn_ite_eq_set {X : Type*} {n : ℕ}
    (f : Fin n → X) (q : Fin n) (x : X) :
    List.ofFn (fun c ↦ if c = q then x else f c) =
      (List.ofFn f).set q.val x := by
  induction n with
  | zero => exact Fin.elim0 q
  | succ n ih =>
      refine Fin.cases ?_ (fun q ↦ ?_) q
      · simp [List.ofFn_succ]
      · have hzero : (0 : Fin (n + 1)) ≠ q.succ := by
          intro h
          have := congrArg Fin.val h
          simp at this
        simp [List.ofFn_succ, hzero, ih]

omit [AddCommGroup A] [Fintype A] in
/-- The conditional `List.ofFn` definition of the erased value-cell list is
literally a single valid `List.set`. -/
theorem Theorem21SetPartition.valueCellsAfterErase_eq_set
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) :
    P.valueCellsAfterErase q x =
      P.valueCells.set q.val (eraseValue (P.valueCell q) x) := by
  classical
  unfold Theorem21SetPartition.valueCellsAfterErase
    Theorem21SetPartition.valueCells
  have hfun :
      (fun c : Fin n ↦
        if c = q then eraseValue (P.valueCell c) x else P.valueCell c) =
      (fun c : Fin n ↦
        if c = q then eraseValue (P.valueCell q) x else P.valueCell c) := by
    funext c
    by_cases hcq : c = q
    · subst c
      simp
    · simp [hcq]
  rw [hfun]
  simpa using List.ofFn_ite_eq_set
    (fun c : Fin n ↦ P.valueCell c) q (eraseValue (P.valueCell q) x)

omit [AddCommGroup A] [Fintype A] in
/-- Erasing a cell before a tail does not alter that tail's layer list. -/
theorem Theorem21SetPartition.tailValueCellsAfterErase_eq_of_source_lt
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) (hqr : q.val < r) :
    P.tailValueCellsAfterErase q x r = P.tailValueCells r := by
  unfold Theorem21SetPartition.tailValueCellsAfterErase
    Theorem21SetPartition.tailValueCells
  rw [P.valueCellsAfterErase_eq_set]
  exact List.drop_set_eq_of_lt P.valueCells
    (eraseValue (P.valueCell q) x) hqr

omit [AddCommGroup A] [Fintype A] in
/-- Exact decomposition of the erased tail around its modified cell. -/
theorem Theorem21SetPartition.tailValueCellsAfterErase_decompose
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) (hrq : r ≤ q.val) :
    P.tailValueCellsAfterErase q x r =
      (P.valueCells.drop r).take (q.val - r) ++
        eraseValue (P.valueCell q) x :: P.valueCells.drop (q.val + 1) := by
  classical
  unfold Theorem21SetPartition.tailValueCellsAfterErase
  rw [P.valueCellsAfterErase_eq_set]
  exact List.drop_set_eq_take_append_cons_drop P.valueCells
    (eraseValue (P.valueCell q) x) hrq (by
      rw [P.length_valueCells]
      exact q.isLt)

omit [AddCommGroup A] [Fintype A] in
/-- Exact decomposition of the unmodified tail around the same cell. -/
theorem Theorem21SetPartition.tailValueCells_decompose
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (hrq : r ≤ q.val) :
    P.tailValueCells r =
      (P.valueCells.drop r).take (q.val - r) ++
        P.valueCell q :: P.valueCells.drop (q.val + 1) := by
  classical
  unfold Theorem21SetPartition.tailValueCells
  calc
    P.valueCells.drop r =
        (P.valueCells.drop r).take (q.val - r) ++
          P.valueCells.drop (r + (q.val - r)) :=
      (List.drop_take_append_drop P.valueCells r (q.val - r)).symm
    _ = (P.valueCells.drop r).take (q.val - r) ++
        P.valueCell q :: P.valueCells.drop (q.val + 1) := by
      have hqLength : q.val < P.valueCells.length := by
        rw [P.length_valueCells]
        exact q.isLt
      have hdropq : P.valueCells.drop q.val =
          P.valueCells[q.val] :: P.valueCells.drop (q.val + 1) :=
        List.drop_eq_getElem_cons hqLength
      have hget : P.valueCells[q.val] = P.valueCell q := by
        simp [Theorem21SetPartition.valueCells]
      rw [Nat.add_sub_of_le hrq, hdropq, hget]

omit [Fintype A] in
/-- A quotient-duplicated source cell remains nonempty after erasing the
moved value, so the entire intermediate erased list is still a genuine
nonempty-layer setpartition. -/
theorem Theorem21SetPartition.valueCellsAfterErase_nonempty_of_doubled
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (q : Fin n) (x : A)
    (hdouble : P.IsHDoubledInCell H q x) :
    IsNonemptySetPartition (P.valueCellsAfterErase q x) := by
  classical
  rcases hdouble with ⟨_hxq, y, hyq, hyx, _hyquot⟩
  intro B hB
  simp only [Theorem21SetPartition.valueCellsAfterErase,
    List.mem_ofFn] at hB
  obtain ⟨c, rfl⟩ := hB
  by_cases hcq : c = q
  · subst c
    simp only [if_pos]
    unfold eraseValue
    exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyq⟩⟩
  · simp only [if_neg hcq]
    exact P.valueCells_nonempty (P.valueCell c) (by
      simp [Theorem21SetPartition.valueCells])

omit [AddCommGroup A] [Fintype A] in
/-- If the target cell lies strictly before a tail and the source cell lies
inside it, then the honest occurrence move changes that tail exactly by
erasing the source value: the target insertion has already been dropped. -/
theorem Theorem21SetPartition.tailValueCells_move_eq_afterErase_of_target_lt
    {xs : List A} {n m r : ℕ} {P Q : Theorem21SetPartition xs n m}
    {q d : Fin n} {i : Occurrence xs}
    (hdk : d.val < r) (hiq : i ∈ P.cells q)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c) :
    Q.tailValueCells r =
      P.tailValueCellsAfterErase q (occurrenceValue xs i) r := by
  classical
  have hlenQ : (Q.tailValueCells r).length = n - r := by
    simp [Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.valueCells]
  have hlenP : (P.tailValueCellsAfterErase q
      (occurrenceValue xs i) r).length = n - r := by
    simp [Theorem21SetPartition.tailValueCellsAfterErase,
      Theorem21SetPartition.valueCellsAfterErase]
  apply List.ext_get (hlenQ.trans hlenP.symm)
  intro j hjQ hjP
  have hj : r + j < n := by
    have hj' : j < n - r := by
      rw [hlenQ] at hjQ
      exact hjQ
    omega
  let c : Fin n := ⟨r + j, hj⟩
  simp only [Theorem21SetPartition.tailValueCells,
    Theorem21SetPartition.tailValueCellsAfterErase,
    Theorem21SetPartition.valueCells,
    Theorem21SetPartition.valueCellsAfterErase,
    List.get_eq_getElem, List.getElem_drop, List.getElem_ofFn]
  change Q.valueCell c =
    if c = q then eraseValue (P.valueCell c) (occurrenceValue xs i)
    else P.valueCell c
  by_cases hcq : c = q
  · rw [hcq]
    rw [if_pos rfl]
    exact P.valueCell_eq_erase_of_moveOccurrence hiq hQcells
  · simp only [if_neg hcq]
    have hcd : c ≠ d := by
      intro hcd
      have hcval : r ≤ c.val := by simp [c]
      rw [hcd] at hcval
      omega
    exact P.valueCell_eq_of_moveOccurrence_of_ne hQcells hcq hcd

omit [Fintype A] in
/-- Full-layer sumsets turn list concatenation into pointwise finite-set
addition. -/
theorem fullLayerSumSpectrum_append [DecidableEq A]
    (L R : List (Finset A)) :
    fullLayerSumSpectrum (L ++ R) =
      fullLayerSumSpectrum L + fullLayerSumSpectrum R := by
  induction L with
  | nil =>
      change fullLayerSumSpectrum R =
        (0 : Finset A) + fullLayerSumSpectrum R
      exact (zero_add _).symm
  | cons C L ih =>
      simp only [List.cons_append, fullLayerSumSpectrum_cons, ih]
      exact (add_assoc _ _ _).symm

omit [Fintype A] in
/-- Literal erased-tail decomposition used before Scherk's Proposition 1.3:
the omitted-cell sumset plus the erased cell. -/
theorem Theorem21SetPartition.mem_tailSumsetAfterErase_iff_withoutCell
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x a : A) (hrq : r ≤ q.val) :
    a ∈ P.tailSumsetAfterErase q x r ↔
      ∃ b ∈ P.tailSumsetWithoutCell q r,
        ∃ c ∈ eraseValue (P.valueCell q) x, b + c = a := by
  classical
  unfold Theorem21SetPartition.tailSumsetAfterErase
    Theorem21SetPartition.tailSumsetWithoutCell
  rw [P.tailValueCellsAfterErase_decompose q x hrq,
    P.tailValueCellsWithoutCell_eq q hrq,
    fullLayerSumSpectrum_append, fullLayerSumSpectrum_cons,
    fullLayerSumSpectrum_append]
  simp only [Finset.mem_add]
  constructor
  · rintro ⟨p, hp, u, ⟨c, hc, s, hs, rfl⟩, rfl⟩
    exact ⟨p + s, ⟨p, hp, s, hs, rfl⟩, c, hc, by ac_rfl⟩
  · rintro ⟨u, ⟨p, hp, s, hs, rfl⟩, c, hc, rfl⟩
    exact ⟨p, hp, c + s, ⟨c, hc, s, hs, rfl⟩, by ac_rfl⟩

omit [Fintype A] in
/-- Finset equality form of the erased-tail decomposition. -/
theorem Theorem21SetPartition.tailSumsetAfterErase_eq_withoutCell_add
    [DecidableEq A] {xs : List A} {n m r : ℕ}
    (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) (hrq : r ≤ q.val) :
    P.tailSumsetAfterErase q x r =
      P.tailSumsetWithoutCell q r + eraseValue (P.valueCell q) x := by
  classical
  apply Finset.ext
  intro a
  simpa only [Finset.mem_add] using
    P.mem_tailSumsetAfterErase_iff_withoutCell q x a hrq

omit [Fintype A] in
/-- If the erased tail is not periodic by the actual old tail stabilizer,
it cannot equal the old tail. -/
theorem Theorem21SetPartition.tailSumsetAfterErase_ne_tail_of_not_periodic
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A)
    (hnot : ¬ P.tailPeriod r ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x r : Set A)) :
    P.tailSumsetAfterErase q x r ≠ P.tailSumset r := by
  intro heq
  apply hnot
  unfold Theorem21SetPartition.tailPeriod
  rw [heq]

omit [Fintype A] in
/-- Therefore the common omitted-cell sumset distinguishes the full cell
from its one-value erasure.  This is the exact strict-change input to
Scherk's Proposition 1.3 in Lemma 2. -/
theorem Theorem21SetPartition.withoutCell_add_ne_add_erase
    [DecidableEq A] {xs : List A} {n m r : ℕ}
    (P : Theorem21SetPartition xs n m)
    (q : Fin n) (x : A) (hrq : r ≤ q.val)
    (hnot : ¬ P.tailPeriod r ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x r : Set A)) :
    P.tailSumsetWithoutCell q r + P.valueCell q ≠
      P.tailSumsetWithoutCell q r + eraseValue (P.valueCell q) x := by
  have hne := P.tailSumsetAfterErase_ne_tail_of_not_periodic q x hnot
  rw [P.tailSumsetAfterErase_eq_withoutCell_add q x hrq,
    P.tailSumset_eq_withoutCell_add q hrq] at hne
  exact hne.symm

omit [Fintype A] in
/-- A full-layer sumset of nonempty layers is nonempty.  This elementary
fact is recorded explicitly because the stabilizer propagation used in
Definition 1 passes through `Finset.addStab`, whose coercion theorem requires
a nonempty finite set. -/
theorem fullLayerSumSpectrum_nonempty_of_nonemptySetPartition
    [DecidableEq A] (L : List (Finset A))
    (hL : IsNonemptySetPartition L) :
    (fullLayerSumSpectrum L).Nonempty := by
  unfold fullLayerSumSpectrum
  exact layerSubsumSpectrum_nonempty L hL L.length le_rfl

omit [Fintype A] in
/-- The sumset after omitting one tail cell is nonempty.  In the degenerate
zero-layer case the full-layer convention gives `{0}`; in Lemma 2 the range
guard in fact leaves at least one genuine layer. -/
theorem Theorem21SetPartition.tailSumsetWithoutCell_nonempty
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (q : Fin n) :
    (P.tailSumsetWithoutCell q r).Nonempty := by
  classical
  unfold Theorem21SetPartition.tailSumsetWithoutCell
  exact fullLayerSumSpectrum_nonempty_of_nonemptySetPartition
    (P.tailValueCellsWithoutCell q r)
    (P.tailValueCellsWithoutCell_nonempty q)

omit [Fintype A] in
/-- Every ordinary tail full-layer sumset is nonempty. -/
theorem Theorem21SetPartition.tailSumset_nonempty
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (r : ℕ) : (P.tailSumset r).Nonempty := by
  classical
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailValueCells
  exact fullLayerSumSpectrum_nonempty_of_nonemptySetPartition
    (P.valueCells.drop r) (by
      intro B hB
      exact P.valueCells_nonempty B (List.mem_of_mem_drop hB))

omit [Fintype A] in
/-- Translation symmetries of the right summand remain symmetries after
adding a nonempty left summand.  This is the finite-set form of the
stabilizer nesting used for successive tails in dissertation Definition 1.
-/
theorem stabilizer_add_right_mono [DecidableEq A]
    (B T : Finset A) (hB : B.Nonempty) (hT : T.Nonempty) :
    AddAction.stabilizer A (T : Set A) ≤
      AddAction.stabilizer A ((B + T : Finset A) : Set A) := by
  intro a ha
  have haFin : a ∈ T.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hT]
    exact ha
  have haSum : a ∈ (B + T).addStab :=
    Finset.subset_addStab_add_right hB haFin
  rw [← Finset.mem_coe, Finset.coe_addStab (hB.add hT)] at haSum
  exact haSum

omit [Fintype A] in
/-- Consequently, the stabilizer of a nonempty suffix full-layer sumset is
contained in the stabilizer after adjoining a nonempty prefix. -/
theorem stabilizer_fullLayer_append_right_mono [DecidableEq A]
    (L R : List (Finset A))
    (hL : IsNonemptySetPartition L)
    (hR : IsNonemptySetPartition R) :
    AddAction.stabilizer A
        ((fullLayerSumSpectrum R : Finset A) : Set A) ≤
      AddAction.stabilizer A
        ((fullLayerSumSpectrum (L ++ R) : Finset A) : Set A) := by
  rw [fullLayerSumSpectrum_append]
  exact stabilizer_add_right_mono
    (fullLayerSumSpectrum L) (fullLayerSumSpectrum R)
    (fullLayerSumSpectrum_nonempty_of_nonemptySetPartition L hL)
    (fullLayerSumSpectrum_nonempty_of_nonemptySetPartition R hR)

omit [AddCommGroup A] [Fintype A] in
/-- Taking a prefix preserves the nonempty-layer condition. -/
theorem IsNonemptySetPartition.take {X : Type*}
    {L : List (Finset X)} (hL : IsNonemptySetPartition L) (r : ℕ) :
    IsNonemptySetPartition (L.take r) := by
  intro B hB
  exact hL B (List.mem_of_mem_take hB)

omit [AddCommGroup A] [Fintype A] in
/-- Taking a suffix preserves the nonempty-layer condition. -/
theorem IsNonemptySetPartition.drop {X : Type*}
    {L : List (Finset X)} (hL : IsNonemptySetPartition L) (r : ℕ) :
    IsNonemptySetPartition (L.drop r) := by
  intro B hB
  exact hL B (List.mem_of_mem_drop hB)

omit [Fintype A] in
/-- Generic stabilizer nesting for suffix full-layer sumsets of a nonempty
setpartition. -/
theorem stabilizer_fullLayer_drop_antitone [DecidableEq A]
    (L : List (Finset A)) (hL : IsNonemptySetPartition L)
    {j k : ℕ} (hjk : j ≤ k) :
    AddAction.stabilizer A
        ((fullLayerSumSpectrum (L.drop k) : Finset A) : Set A) ≤
      AddAction.stabilizer A
        ((fullLayerSumSpectrum (L.drop j) : Finset A) : Set A) := by
  let pre := (L.drop j).take (k - j)
  have hdrop : (L.drop j).drop (k - j) = L.drop k := by
    rw [List.drop_drop, Nat.add_sub_of_le hjk]
  have hsplit : pre ++ L.drop k = L.drop j := by
    rw [← hdrop]
    exact List.take_append_drop (k - j) (L.drop j)
  rw [← hsplit]
  exact stabilizer_fullLayer_append_right_mono pre (L.drop k)
    ((hL.drop j).take (k - j)) (hL.drop k)

omit [Fintype A] in
/-- Stabilizers of Definition 1 tails are nested in the source direction:
discarding more initial cells can only decrease the stabilizer.  This is the
precise ordinary specialization of the relation `H_k ≤ H_{k_j}` used in
equation (3.1) of dissertation Lemma 1. -/
theorem Theorem21SetPartition.stabilizer_tailSumset_antitone
    {xs : List A} {n m j k : ℕ} (P : Theorem21SetPartition xs n m)
    (hjk : j ≤ k) :
    AddAction.stabilizer A (P.tailSumset k : Set A) ≤
      AddAction.stabilizer A (P.tailSumset j : Set A) := by
  classical
  let pre := (P.valueCells.drop j).take (k - j)
  have hdrop : (P.valueCells.drop j).drop (k - j) =
      P.valueCells.drop k := by
    rw [List.drop_drop, Nat.add_sub_of_le hjk]
  have hsplit : pre ++ P.valueCells.drop k = P.valueCells.drop j := by
    rw [← hdrop]
    exact List.take_append_drop (k - j) (P.valueCells.drop j)
  have hprefix : IsNonemptySetPartition pre :=
    (P.valueCells_nonempty.drop j).take (k - j)
  have hsuffix : IsNonemptySetPartition (P.valueCells.drop k) :=
    P.valueCells_nonempty.drop k
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailValueCells
  rw [← hsplit]
  exact stabilizer_fullLayer_append_right_mono pre
    (P.valueCells.drop k) hprefix hsuffix

omit [Fintype A] in
/-- Concrete successor step for the Lemma 1 exchange.  If the moved value is
duplicated modulo the later tail stabilizer `H_k`, then stabilizer nesting
upgrades that duplication to the current `H_{k_j}`.  Hence the move preserves
all quotient images required by Definition 1; only the two tail inclusions
from equation (3.1) remain to be supplied. -/
theorem Definition1ExtremalChain.MonotoneReplacement.next_of_moveOccurrence
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {previous : Definition1ExtremalState xs seed n}
    {prior : Definition1ExtremalChain xs seed n r previous}
    {state : Definition1ExtremalState xs seed n}
    {F P Q : Theorem21SetPartition xs n seed.card}
    {step : Definition1Transition r previous state F}
    {q d : Fin n} {i : Occurrence xs} {x : A}
    (hprior : MonotoneReplacement P Q prior)
    (hPnext : P ∈ state.upsilon)
    (hrk : r ≤ k)
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell
      (AddAction.stabilizer A (P.tailSumset k : Set A)) q x)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (hPtailSubsetQ : P.tailSumset r ⊆ Q.tailSumset r)
    (hPnextTailSubsetQ : P.tailSumset (r + 1) ⊆
      Q.tailSumset (r + 1)) :
    MonotoneReplacement P Q
      (Definition1ExtremalChain.next prior state F step) := by
  have hPdata := (step.mem_next_upsilon_iff P).1 hPnext
  have hPtail : P.tailSumset r = previous.chosen.tailSumset r :=
    hPdata.2.1
  have hHK : AddAction.stabilizer A (P.tailSumset k : Set A) ≤
      AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A) := by
    rw [← hPtail]
    exact P.stabilizer_tailSumset_antitone hrk
  have hPimagesQ : P.quotientImagesIncluded Q
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)) :=
    P.quotientImagesIncluded_moveOccurrence_of_mono hHK hqd hiq hix
      hdouble hQcells
  have hFimagesQ : F.quotientImagesIncluded Q
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)) :=
    Theorem21SetPartition.quotientImagesIncluded_trans
      (P := F) (Q := P) (R := Q) hPdata.2.2.2.1 hPimagesQ
  exact MonotoneReplacement.next_of_tail_subsets hprior hPnext
    hPtailSubsetQ hFimagesQ hPnextTailSubsetQ

omit [Fintype A] in
/-- Same successor step with equation (3.1) discharged from the two concrete
periodic-removal equalities.  These equalities say that erasing the moved
representative leaves the current and next old tails unchanged; the honest
move then contains each intermediate erased tail layerwise. -/
theorem Definition1ExtremalChain.MonotoneReplacement.next_of_moveOccurrence_of_erase_eq
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {previous : Definition1ExtremalState xs seed n}
    {prior : Definition1ExtremalChain xs seed n r previous}
    {state : Definition1ExtremalState xs seed n}
    {F P Q : Theorem21SetPartition xs n seed.card}
    {step : Definition1Transition r previous state F}
    {q d : Fin n} {i : Occurrence xs} {x : A}
    (hprior : MonotoneReplacement P Q prior)
    (hPnext : P ∈ state.upsilon)
    (hrk : r ≤ k)
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell
      (AddAction.stabilizer A (P.tailSumset k : Set A)) q x)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (heraseCurrent : P.tailSumset r = P.tailSumsetAfterErase q x r)
    (heraseNext : P.tailSumset (r + 1) =
      P.tailSumsetAfterErase q x (r + 1)) :
    MonotoneReplacement P Q
      (Definition1ExtremalChain.next prior state F step) := by
  have hcurrent : P.tailSumset r ⊆ Q.tailSumset r :=
    P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells r
      (by simpa [hix] using heraseCurrent)
  have hnext : P.tailSumset (r + 1) ⊆ Q.tailSumset (r + 1) :=
    P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells (r + 1)
      (by simpa [hix] using heraseNext)
  exact MonotoneReplacement.next_of_moveOccurrence hprior hPnext hrk hqd
    hiq hix hdouble hQcells hcurrent hnext

omit [Fintype A] in
/-- List-level periodic-removal lemma in the exact form used on every tail in
dissertation Lemma 1.  The distinguished cell may occur between arbitrary
prefix and suffix lists.  If its reduced full-layer sumset remains
`H`-periodic and it contains a second representative of the erased quotient
class, then erasing the first representative leaves the sumset unchanged. -/
theorem fullLayerSumSpectrum_erase_middle_eq_of_periodic_of_quotient_eq
    [DecidableEq A] (H : AddSubgroup A) (L R : List (Finset A))
    (C : Finset A) {x y : A} (hy : y ∈ C) (hxy : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x)
    (hperiodic : H ≤ AddAction.stabilizer A
      ((fullLayerSumSpectrum
        (L ++ C.erase x :: R) : Finset A) : Set A)) :
    fullLayerSumSpectrum (L ++ C :: R) =
      fullLayerSumSpectrum (L ++ C.erase x :: R) := by
  have hold : fullLayerSumSpectrum (L ++ C :: R) =
      (fullLayerSumSpectrum L + fullLayerSumSpectrum R) + C := by
    rw [fullLayerSumSpectrum_append, fullLayerSumSpectrum_cons]
    ac_rfl
  have herased : fullLayerSumSpectrum (L ++ C.erase x :: R) =
      (fullLayerSumSpectrum L + fullLayerSumSpectrum R) + C.erase x := by
    rw [fullLayerSumSpectrum_append, fullLayerSumSpectrum_cons]
    ac_rfl
  rw [hold, herased]
  apply add_erase_eq_of_periodic_of_quotient_eq
    H (fullLayerSumSpectrum L + fullLayerSumSpectrum R) C hy hxy hquot
  simpa only [herased] using hperiodic

omit [Fintype A] in
/-- Tail-level periodic-removal equality in the exact occurrence partition.
When the source cell lies in the tail, a second representative of the same
`H`-class and `H`-periodicity of the erased tail force the old and erased
tail sumsets to coincide. -/
theorem Theorem21SetPartition.tailSumset_eq_afterErase_of_periodic
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (q : Fin n) {x y : A}
    (hrq : r ≤ q.val) (hy : y ∈ P.valueCell q) (hyx : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x)
    (hperiodic : H ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x r : Set A)) :
    P.tailSumset r = P.tailSumsetAfterErase q x r := by
  classical
  unfold Theorem21SetPartition.tailSumsetAfterErase at hperiodic
  rw [P.tailValueCellsAfterErase_decompose q x hrq] at hperiodic
  unfold eraseValue at hperiodic
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailSumsetAfterErase
  rw [P.tailValueCells_decompose q hrq,
    P.tailValueCellsAfterErase_decompose q x hrq]
  unfold eraseValue
  exact fullLayerSumSpectrum_erase_middle_eq_of_periodic_of_quotient_eq
    H ((P.valueCells.drop r).take (q.val - r))
      (P.valueCells.drop (q.val + 1)) (P.valueCell q)
      hy hyx hquot hperiodic

omit [Fintype A] in
/-- Contrapositive removal criterion from dissertation Lemma 1: if erasing
the doubled representative really changes the tail sumset, then the erased
tail cannot retain the proposed period. -/
theorem Theorem21SetPartition.not_periodic_tailSumsetAfterErase_of_ne
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (q : Fin n) {x y : A}
    (hrq : r ≤ q.val) (hy : y ∈ P.valueCell q) (hyx : y ≠ x)
    (hquot : QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x)
    (hne : P.tailSumset r ≠ P.tailSumsetAfterErase q x r) :
    ¬ H ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x r : Set A) := by
  intro hperiodic
  exact hne (P.tailSumset_eq_afterErase_of_periodic H q hrq hy hyx
    hquot hperiodic)

omit [Fintype A] in
/-- Stabilizer nesting also holds for all intermediate erased tails, because
the doubled representative keeps the erased source layer nonempty. -/
theorem Theorem21SetPartition.stabilizer_tailSumsetAfterErase_antitone
    {xs : List A} {n m j k : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (q : Fin n) (x : A)
    (hdouble : P.IsHDoubledInCell H q x) (hjk : j ≤ k) :
    AddAction.stabilizer A (P.tailSumsetAfterErase q x k : Set A) ≤
      AddAction.stabilizer A
        (P.tailSumsetAfterErase q x j : Set A) := by
  classical
  unfold Theorem21SetPartition.tailSumsetAfterErase
    Theorem21SetPartition.tailValueCellsAfterErase
  exact stabilizer_fullLayer_drop_antitone
    (P.valueCellsAfterErase q x)
    (P.valueCellsAfterErase_nonempty_of_doubled H q x hdouble) hjk

omit [Fintype A] in
/-- A period retained by one later erased tail propagates to every earlier
erased tail.  Combining this with the duplicate representative gives the
old-equals-erased equality needed at every Definition 1 stage before `k`. -/
theorem Theorem21SetPartition.tailSumset_eq_afterErase_of_later_periodic
    {xs : List A} {n m r k : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (q : Fin n) {x : A}
    (hrk : r ≤ k) (hrq : r ≤ q.val)
    (hdouble : P.IsHDoubledInCell H q x)
    (hperiodicLater : H ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x k : Set A)) :
    P.tailSumset r = P.tailSumsetAfterErase q x r := by
  rcases hdouble with ⟨hxq, y, hyq, hyx, hyquot⟩
  apply P.tailSumset_eq_afterErase_of_periodic H q hrq hyq hyx hyquot
  exact hperiodicLater.trans
    (P.stabilizer_tailSumsetAfterErase_antitone H q x
      ⟨hxq, y, hyq, hyx, hyquot⟩ hrk)

omit [Fintype A] in
/-- If the erased tail at `min k q` is `H`-periodic, then every old tail up
to stage `k` is contained in the honest moved partition: before the source
cell this follows by periodic removal, and after the source cell erasure has
already disappeared from the suffix.  This is the exact `l = min k q`
bookkeeping missing from the index-aligned subcase. -/
theorem Theorem21SetPartition.tailSumset_eq_afterErase_of_min_periodic
    {xs : List A} {n m r k : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (q : Fin n) {x : A}
    (hrk : r ≤ k)
    (hdouble : P.IsHDoubledInCell H q x)
    (hperiodicMin : H ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x (min k q.val) : Set A)) :
    P.tailSumset r = P.tailSumsetAfterErase q x r := by
  by_cases hrq : r ≤ q.val
  · have hrmin : r ≤ min k q.val := Nat.le_min.mpr ⟨hrk, hrq⟩
    exact P.tailSumset_eq_afterErase_of_later_periodic H q hrmin hrq
      hdouble hperiodicMin
  · have hqr : q.val < r := by omega
    unfold Theorem21SetPartition.tailSumset
      Theorem21SetPartition.tailSumsetAfterErase
    rw [P.tailValueCellsAfterErase_eq_of_source_lt q x hqr]

omit [Fintype A] in
/-- Full recursive admissibility half of dissertation Lemma 1.  A single
honest occurrence move from a class doubled modulo the later tail stabilizer
survives every Definition 1 extremal stage up to that tail, provided erasing
the representative retains that later stabilizer.  The proof recursively
derives all quotient-image and tail inclusions; no fixed partition is reused
across stages. -/
theorem Definition1ExtremalChain.MonotoneReplacement.of_moveOccurrence_of_later_periodic
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {state : Definition1ExtremalState xs seed n}
    {chain : Definition1ExtremalChain xs seed n r state}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q d : Fin n} {i : Occurrence xs} {x : A}
    (hP : P ∈ state.upsilon) (hrk : r ≤ k) (hkq : k ≤ q.val)
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell
      (AddAction.stabilizer A (P.tailSumset k : Set A)) q x)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (hperiodicLater : AddAction.stabilizer A
        (P.tailSumset k : Set A) ≤
      AddAction.stabilizer A
        (P.tailSumsetAfterErase q x k : Set A)) :
    MonotoneReplacement P Q chain := by
  induction chain with
  | initial state valid =>
      have herase0 := P.tailSumset_eq_afterErase_of_later_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (Nat.zero_le k) (Nat.zero_le q.val) hdouble hperiodicLater
      have htail : P.tailSumset 0 ⊆ Q.tailSumset 0 :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells 0
          (by simpa [hix] using herase0)
      have hsum : P.sumset ⊆ Q.sumset := by
        simpa [Theorem21SetPartition.tailSumset,
          Theorem21SetPartition.tailValueCells,
          Theorem21SetPartition.sumset] using htail
      exact MonotoneReplacement.initial state valid hP hsum
  | @next r previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hprior : MonotoneReplacement P Q prior :=
        ih hPdata.1 (by omega)
      have heraseCurrent := P.tailSumset_eq_afterErase_of_later_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (by omega : r ≤ k) (by omega : r ≤ q.val) hdouble hperiodicLater
      have heraseNext := P.tailSumset_eq_afterErase_of_later_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (by omega : r + 1 ≤ k) (by omega : r + 1 ≤ q.val)
        hdouble hperiodicLater
      exact MonotoneReplacement.next_of_moveOccurrence_of_erase_eq
        hprior hP (by omega) hqd hiq hix hdouble hQcells
        heraseCurrent heraseNext

omit [Fintype A] in
/-- Source-chain counterpart of the recursive Lemma 1 exchange.  Literal
`Lambda_0` admissibility of `Q` is consumed only at the base stage; all later
steps are the genuine Definition 1 transitions. -/
theorem Definition1SourceChain.MonotoneReplacement.of_moveOccurrence_of_later_periodic
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    {chain : Definition1SourceChain I r state}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q d : Fin n} {i : Occurrence xs} {x : A}
    (hP : P ∈ state.upsilon) (hrk : r ≤ k) (hkq : k ≤ q.val)
    (hQadmissible : GMOReplacementAdmissible I Q)
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell
      (AddAction.stabilizer A (P.tailSumset k : Set A)) q x)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (hperiodicLater : AddAction.stabilizer A
        (P.tailSumset k : Set A) ≤
      AddAction.stabilizer A
        (P.tailSumsetAfterErase q x k : Set A)) :
    MonotoneReplacement P Q chain := by
  induction chain with
  | initial state valid =>
      have herase0 := P.tailSumset_eq_afterErase_of_later_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (Nat.zero_le k) (Nat.zero_le q.val) hdouble hperiodicLater
      have htail : P.tailSumset 0 ⊆ Q.tailSumset 0 :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells 0
          (by simpa [hix] using herase0)
      have hsum : P.sumset ⊆ Q.sumset := by
        simpa [Theorem21SetPartition.tailSumset,
          Theorem21SetPartition.tailValueCells,
          Theorem21SetPartition.sumset] using htail
      exact MonotoneReplacement.initial state valid hP hQadmissible hsum
  | @next r previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hprior : MonotoneReplacement P Q prior :=
        ih hPdata.1 (by omega)
      have heraseCurrent := P.tailSumset_eq_afterErase_of_later_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (by omega : r ≤ k) (by omega : r ≤ q.val) hdouble hperiodicLater
      have heraseNext := P.tailSumset_eq_afterErase_of_later_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (by omega : r + 1 ≤ k) (by omega : r + 1 ≤ q.val)
        hdouble hperiodicLater
      have hcurrent : P.tailSumset r ⊆ Q.tailSumset r :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells r
          (by simpa [hix] using heraseCurrent)
      have hnext : P.tailSumset (r + 1) ⊆ Q.tailSumset (r + 1) :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells
          (r + 1) (by simpa [hix] using heraseNext)
      have hPtail : P.tailSumset r = previous.chosen.tailSumset r :=
        hPdata.2.1
      have hHK : AddAction.stabilizer A (P.tailSumset k : Set A) ≤
          AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A) := by
        rw [← hPtail]
        exact P.stabilizer_tailSumset_antitone (by omega)
      have hPimagesQ : P.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) :=
        P.quotientImagesIncluded_moveOccurrence_of_mono hHK hqd hiq hix
          hdouble hQcells
      have hFimagesQ : F.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) :=
        Theorem21SetPartition.quotientImagesIncluded_trans
          (P := F) (Q := P) (R := Q) hPdata.2.2.2.1 hPimagesQ
      exact MonotoneReplacement.next_of_tail_subsets hprior hP hcurrent
        hFimagesQ hnext

omit [Fintype A] in
/-- Full `l = min k q` recursive exchange along the literal source chain. -/
theorem Definition1SourceChain.MonotoneReplacement.of_moveOccurrence_of_min_periodic
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    {chain : Definition1SourceChain I r state}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q d : Fin n} {i : Occurrence xs} {x : A}
    (hP : P ∈ state.upsilon) (hrk : r ≤ k)
    (hQadmissible : GMOReplacementAdmissible I Q)
    (hqd : q ≠ d) (hiq : i ∈ P.cells q)
    (hix : occurrenceValue xs i = x)
    (hdouble : P.IsHDoubledInCell
      (AddAction.stabilizer A (P.tailSumset k : Set A)) q x)
    (hQcells : ∀ c, Q.cells c = P.moveOccurrenceCells q d i c)
    (hperiodicMin : AddAction.stabilizer A
        (P.tailSumset k : Set A) ≤
      AddAction.stabilizer A
        (P.tailSumsetAfterErase q x (min k q.val) : Set A)) :
    MonotoneReplacement P Q chain := by
  induction chain with
  | initial state valid =>
      have herase0 := P.tailSumset_eq_afterErase_of_min_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (Nat.zero_le k) hdouble hperiodicMin
      have htail : P.tailSumset 0 ⊆ Q.tailSumset 0 :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells 0
          (by simpa [hix] using herase0)
      have hsum : P.sumset ⊆ Q.sumset := by
        simpa [Theorem21SetPartition.tailSumset,
          Theorem21SetPartition.tailValueCells,
          Theorem21SetPartition.sumset] using htail
      exact MonotoneReplacement.initial state valid hP hQadmissible hsum
  | @next r previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hprior : MonotoneReplacement P Q prior :=
        ih hPdata.1 (by omega)
      have heraseCurrent := P.tailSumset_eq_afterErase_of_min_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (by omega : r ≤ k) hdouble hperiodicMin
      have heraseNext := P.tailSumset_eq_afterErase_of_min_periodic
        (AddAction.stabilizer A (P.tailSumset k : Set A)) q
        (by omega : r + 1 ≤ k) hdouble hperiodicMin
      have hcurrent : P.tailSumset r ⊆ Q.tailSumset r :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells r
          (by simpa [hix] using heraseCurrent)
      have hnext : P.tailSumset (r + 1) ⊆ Q.tailSumset (r + 1) :=
        P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells
          (r + 1) (by simpa [hix] using heraseNext)
      have hPtail : P.tailSumset r = previous.chosen.tailSumset r :=
        hPdata.2.1
      have hHK : AddAction.stabilizer A (P.tailSumset k : Set A) ≤
          AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A) := by
        rw [← hPtail]
        exact P.stabilizer_tailSumset_antitone (by omega)
      have hPimagesQ : P.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) :=
        P.quotientImagesIncluded_moveOccurrence_of_mono hHK hqd hiq hix
          hdouble hQcells
      have hFimagesQ : F.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) :=
        Theorem21SetPartition.quotientImagesIncluded_trans
          (P := F) (Q := P) (R := Q) hPdata.2.2.2.1 hPimagesQ
      exact MonotoneReplacement.next_of_tail_subsets hprior hP hcurrent
        hFimagesQ hnext

omit [Fintype A] in
/-- A cross-support replacement survives every genuine source-chain prefix
when erasing the used value preserves all old tails.  Quotient-image
preservation is checked at each prefix's own stabilizer and transition. -/
theorem Definition1SourceChain.MonotoneReplacement.of_replaceUsedWithUnused_of_erase_eq
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    {chain : Definition1SourceChain I r state}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q d : Fin n} {y x : Occurrence xs}
    (hP : P ∈ state.upsilon) (hrk : r ≤ k)
    (hQadmissible : GMOReplacementAdmissible I Q)
    (hqd : q ≠ d) (hyq : y ∈ P.cells q)
    (hduplicate :
      ∃ z ∈ P.valueCell q,
        z ≠ occurrenceValue xs y ∧
        QuotientAddGroup.mk' (P.tailPeriod k) z =
          QuotientAddGroup.mk' (P.tailPeriod k) (occurrenceValue xs y))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedCells q d y x c)
    (herase : ∀ s, s ≤ r →
      P.tailSumset s =
        P.tailSumsetAfterErase q (occurrenceValue xs y) s) :
    Definition1SourceChain.MonotoneReplacement P Q chain := by
  induction chain with
  | initial state valid =>
      have htail : P.tailSumset 0 ⊆ Q.tailSumset 0 :=
        P.tailSumset_subset_replaceUsedWithUnused_of_erase_eq
          hqd hyq hQcells 0 (herase 0 le_rfl)
      have hsum : P.sumset ⊆ Q.sumset := by
        simpa [Theorem21SetPartition.tailSumset,
          Theorem21SetPartition.tailValueCells,
          Theorem21SetPartition.sumset] using htail
      exact MonotoneReplacement.initial state valid hP hQadmissible hsum
  | @next j previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hprior : MonotoneReplacement P Q prior :=
        ih hPdata.1 (by omega) (fun s hs ↦ herase s (by omega))
      have hcurrent : P.tailSumset j ⊆ Q.tailSumset j :=
        P.tailSumset_subset_replaceUsedWithUnused_of_erase_eq
          hqd hyq hQcells j (herase j (by omega))
      have hnext : P.tailSumset (j + 1) ⊆ Q.tailSumset (j + 1) :=
        P.tailSumset_subset_replaceUsedWithUnused_of_erase_eq
          hqd hyq hQcells (j + 1) (herase (j + 1) (by omega))
      have hPtail : P.tailSumset j = previous.chosen.tailSumset j :=
        hPdata.2.1
      have hHK : P.tailPeriod k ≤
          AddAction.stabilizer A
            (previous.chosen.tailSumset j : Set A) := by
        rw [← hPtail]
        exact P.stabilizer_tailSumset_antitone (by omega)
      have hPimagesQ : P.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset j : Set A)) :=
        P.quotientImagesIncluded_replace_of_mono hHK hqd hyq
          hduplicate hQcells
      have hFimagesQ : F.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset j : Set A)) :=
        Theorem21SetPartition.quotientImagesIncluded_trans
          (P := F) (Q := P) (R := Q) hPdata.2.2.2.1 hPimagesQ
      exact MonotoneReplacement.next_of_tail_subsets hprior hP hcurrent
        hFimagesQ hnext

omit [Fintype A] in
/-- Same recursive preservation theorem for the case where the removed and
inserted occurrences belong to the same indexed cell. -/
theorem Definition1SourceChain.MonotoneReplacement.of_replaceSameCell_of_erase_eq
    {xs : List A} {seed : Selection xs} {n r k : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    {chain : Definition1SourceChain I r state}
    {P Q : Theorem21SetPartition xs n seed.card}
    {q : Fin n} {y x : Occurrence xs}
    (hP : P ∈ state.upsilon) (hrk : r ≤ k)
    (hQadmissible : GMOReplacementAdmissible I Q)
    (hyq : y ∈ P.cells q)
    (hduplicate :
      ∃ z ∈ P.valueCell q,
        z ≠ occurrenceValue xs y ∧
        QuotientAddGroup.mk' (P.tailPeriod k) z =
          QuotientAddGroup.mk' (P.tailPeriod k) (occurrenceValue xs y))
    (hQcells : ∀ c,
      Q.cells c = P.replaceUsedWithUnusedSameCell q y x c)
    (herase : ∀ s, s ≤ r →
      P.tailSumset s =
        P.tailSumsetAfterErase q (occurrenceValue xs y) s) :
    Definition1SourceChain.MonotoneReplacement P Q chain := by
  induction chain with
  | initial state valid =>
      have htail : P.tailSumset 0 ⊆ Q.tailSumset 0 :=
        P.tailSumset_subset_replaceSameCell_of_erase_eq
          hyq hQcells 0 (herase 0 le_rfl)
      have hsum : P.sumset ⊆ Q.sumset := by
        simpa [Theorem21SetPartition.tailSumset,
          Theorem21SetPartition.tailValueCells,
          Theorem21SetPartition.sumset] using htail
      exact MonotoneReplacement.initial state valid hP hQadmissible hsum
  | @next j previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hprior : MonotoneReplacement P Q prior :=
        ih hPdata.1 (by omega) (fun s hs ↦ herase s (by omega))
      have hcurrent : P.tailSumset j ⊆ Q.tailSumset j :=
        P.tailSumset_subset_replaceSameCell_of_erase_eq
          hyq hQcells j (herase j (by omega))
      have hnext : P.tailSumset (j + 1) ⊆ Q.tailSumset (j + 1) :=
        P.tailSumset_subset_replaceSameCell_of_erase_eq
          hyq hQcells (j + 1) (herase (j + 1) (by omega))
      have hPtail : P.tailSumset j = previous.chosen.tailSumset j :=
        hPdata.2.1
      have hHK : P.tailPeriod k ≤
          AddAction.stabilizer A
            (previous.chosen.tailSumset j : Set A) := by
        rw [← hPtail]
        exact P.stabilizer_tailSumset_antitone (by omega)
      have hPimagesQ : P.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset j : Set A)) :=
        P.quotientImagesIncluded_replaceSameCell_of_mono hHK hyq
          hduplicate hQcells
      have hFimagesQ : F.quotientImagesIncluded Q
          (AddAction.stabilizer A
            (previous.chosen.tailSumset j : Set A)) :=
        Theorem21SetPartition.quotientImagesIncluded_trans
          (P := F) (Q := P) (R := Q) hPdata.2.2.2.1 hPimagesQ
      exact MonotoneReplacement.next_of_tail_subsets hprior hP hcurrent
        hFimagesQ hnext

omit [Fintype A] in
/-- The genuine l = min rho q maximal-exchange contradiction for a weak
factor form, with the source paper's anchor-value convention explicit. -/
theorem WeakFactorForm.lemma1_minTail_of_anchor_ne
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (q : Fin n) (x : A)
    (hexception : W.partition.IsHException
      (W.partition.tailPeriod rho) x)
    (hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod rho) q x)
    (hanchor : occurrenceValue xs (I.anchor q) ≠ x) :
    ¬ W.partition.tailPeriod rho ≤
      AddAction.stabilizer A
        (W.partition.tailSumsetAfterErase q x (min rho q.val) : Set A) := by
  classical
  intro hperiodic
  rcases hexception with ⟨d, hmissing⟩
  rcases hdouble with ⟨hxq, y, hyq, hyx, hyquot⟩
  rcases Finset.mem_image.mp hxq with ⟨i, hiq, hix⟩
  rcases Finset.mem_image.mp hyq with ⟨j, hjq, hjy⟩
  have hqd : q ≠ d := by
    intro hqd
    subst d
    apply hmissing
    exact (mem_quotientLayer_iff (W.partition.tailPeriod rho)
      (W.partition.valueCell q) _).2 ⟨x, hxq, rfl⟩
  have hji : j ≠ i := by
    intro hji
    subst j
    apply hyx
    rw [← hix, ← hjy]
  have htarget : ∀ z ∈ W.partition.cells d,
      occurrenceValue xs z ≠ occurrenceValue xs i := by
    intro z hzd hzvalue
    apply hmissing
    apply (mem_quotientLayer_iff (W.partition.tailPeriod rho)
      (W.partition.valueCell d) _).2
    refine ⟨occurrenceValue xs z,
      Finset.mem_image.mpr ⟨z, hzd, rfl⟩, ?_⟩
    simp [hzvalue, hix]
  obtain ⟨Q, hQcells, _hQsupport⟩ := W.partition.exists_moveOccurrence
    hqd hiq ⟨j, hjq, hji⟩ htarget
  have herase0 := W.partition.tailSumset_eq_afterErase_of_min_periodic
    (W.partition.tailPeriod rho) q (Nat.zero_le rho)
    ⟨hxq, y, hyq, hyx, hyquot⟩ hperiodic
  have hsum : W.partition.sumset ⊆ Q.sumset := by
    have htail : W.partition.tailSumset 0 ⊆ Q.tailSumset 0 :=
      W.partition.tailSumset_subset_moveOccurrence_of_erase_eq
        hqd hiq hQcells 0 (by simpa [hix] using herase0)
    simpa [Theorem21SetPartition.tailSumset,
      Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.sumset] using htail
  have hQadmissible : GMOReplacementAdmissible I Q :=
    W.admissible.moveOccurrence hqd hiq (by simpa [hix] using hanchor)
      hQcells hsum
  have hdoubleStab : W.partition.IsHDoubledInCell
      (AddAction.stabilizer A
        (W.partition.tailSumset rho : Set A)) q x := by
    simpa [Theorem21SetPartition.tailPeriod] using
      (show W.partition.IsHDoubledInCell
        (W.partition.tailPeriod rho) q x from
        ⟨hxq, y, hyq, hyx, hyquot⟩)
  have hperiodicStab : AddAction.stabilizer A
        (W.partition.tailSumset rho : Set A) ≤
      AddAction.stabilizer A
        (W.partition.tailSumsetAfterErase q x (min rho q.val) : Set A) := by
    simpa [Theorem21SetPartition.tailPeriod] using hperiodic
  have hmono : Definition1SourceChain.MonotoneReplacement
      W.partition Q W.chain :=
    Definition1SourceChain.MonotoneReplacement.of_moveOccurrence_of_min_periodic
      W.inLambda.1 le_rfl hQadmissible hqd hiq hix hdoubleStab hQcells
      hperiodicStab
  have hQprevious : Q ∈ W.previous.upsilon :=
    W.chain.mem_final_of_monotoneReplacement hmono
  have heraseRho := W.partition.tailSumset_eq_afterErase_of_min_periodic
    (W.partition.tailPeriod rho) q le_rfl
    ⟨hxq, y, hyq, hyx, hyquot⟩ hperiodic
  have hPsubsetQ : W.partition.tailSumset rho ⊆ Q.tailSumset rho :=
    W.partition.tailSumset_subset_moveOccurrence_of_erase_eq
      hqd hiq hQcells rho (by simpa [hix] using heraseRho)
  have hQcard : (Q.tailSumset rho).card =
      (W.previous.chosen.tailSumset rho).card :=
    W.chain.tail_card_eq_chosen_of_mem hQprevious
  have hPtail : W.partition.tailSumset rho =
      W.previous.chosen.tailSumset rho := W.inLambda.2.1
  have hQeqP : Q.tailSumset rho = W.partition.tailSumset rho :=
    (Finset.eq_of_subset_of_card_le hPsubsetQ (by
      rw [hQcard, hPtail])).symm
  have hQtail : Q.tailSumset rho =
      W.previous.chosen.tailSumset rho := hQeqP.trans hPtail
  have hQinc : Q.quotientIncidenceAt (W.partition.tailPeriod rho) =
      W.partition.quotientIncidenceAt (W.partition.tailPeriod rho) + 1 :=
    W.partition.quotientIncidenceAt_move_eq_add_one
      (W.partition.tailPeriod rho) hqd hiq hix
      ⟨hxq, y, hyq, hyx, hyquot⟩ hmissing hQcells
  have hH : W.partition.tailPeriod rho = AddAction.stabilizer A
      (W.previous.chosen.tailSumset rho : Set A) := by
    unfold Theorem21SetPartition.tailPeriod
    rw [hPtail]
  have hQmax := W.transition.incidence_maximal Q hQprevious hQtail
  have hPinc := W.inLambda.2.2
  rw [← hH] at hQmax hPinc
  rw [hQinc, hPinc] at hQmax
  omega

omit [Fintype A] in
/-- Anchor-safe `l = min rho q` form with the paper's “without loss of
generality `x ≠ a_q`” made constructive.  If the named representative is the
anchor value, the other representative in its doubled quotient class is
chosen instead; it is still a doubled exception in the same class. -/
theorem WeakFactorForm.exists_lemma1_minTail_representative
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (q : Fin n) (x : A)
    (hexception : W.partition.IsHException
      (W.partition.tailPeriod rho) x)
    (hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod rho) q x) :
    ∃ z : A,
      QuotientAddGroup.mk' (W.partition.tailPeriod rho) z =
        QuotientAddGroup.mk' (W.partition.tailPeriod rho) x ∧
      W.partition.IsHException (W.partition.tailPeriod rho) z ∧
      W.partition.IsHDoubledInCell (W.partition.tailPeriod rho) q z ∧
      occurrenceValue xs (I.anchor q) ≠ z ∧
      ¬ W.partition.tailPeriod rho ≤
        AddAction.stabilizer A
          (W.partition.tailSumsetAfterErase q z (min rho q.val) : Set A) := by
  rcases hdouble with ⟨hxq, y, hyq, hyx, hyquot⟩
  by_cases hanchor : occurrenceValue xs (I.anchor q) ≠ x
  · refine ⟨x, rfl, hexception,
      ⟨hxq, y, hyq, hyx, hyquot⟩, hanchor, ?_⟩
    exact W.lemma1_minTail_of_anchor_ne q x hexception
      ⟨hxq, y, hyq, hyx, hyquot⟩ hanchor
  · have hanchorEq : occurrenceValue xs (I.anchor q) = x :=
      Classical.not_not.mp hanchor
    have hyException : W.partition.IsHException
        (W.partition.tailPeriod rho) y := by
      rcases hexception with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      intro hyMem
      apply hd
      simpa [hyquot] using hyMem
    have hyDouble : W.partition.IsHDoubledInCell
        (W.partition.tailPeriod rho) q y :=
      ⟨hyq, x, hxq, fun hxy ↦ hyx hxy.symm, hyquot.symm⟩
    have hyAnchor : occurrenceValue xs (I.anchor q) ≠ y := by
      rw [hanchorEq]
      exact fun hxy ↦ hyx hxy.symm
    refine ⟨y, hyquot, hyException, hyDouble, hyAnchor, ?_⟩
    exact W.lemma1_minTail_of_anchor_ne q y hyException hyDouble hyAnchor

omit [Fintype A] in
/-- Condition (I) closes the `q < rho` branch of Lemma 1.  The suffix after
cell `q` has period `tailPeriod (q+1)`, which contains `tailPeriod rho` by
stabilizer nesting.  Adding the nonempty erased `q`-cell on the left therefore
leaves the erased `q`-tail `tailPeriod rho`-periodic. -/
theorem WeakFactorForm.periodic_tailSumsetAfterErase_of_source_lt
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (q : Fin n) (x : A)
    (hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod rho) q x)
    (hqrho : q.val < rho) :
    W.partition.tailPeriod rho ≤
      AddAction.stabilizer A
        (W.partition.tailSumsetAfterErase q x q.val : Set A) := by
  classical
  rcases hdouble with ⟨hxq, y, hyq, hyx, hyquot⟩
  have hsucc : q.val + 1 ≤ rho := by omega
  have hperiodNest : W.partition.tailPeriod rho ≤
      W.partition.tailPeriod (q.val + 1) := by
    unfold Theorem21SetPartition.tailPeriod
    exact W.partition.stabilizer_tailSumset_antitone hsucc
  have hleft : IsNonemptySetPartition
      [eraseValue (W.partition.valueCell q) x] := by
    intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    subst B
    unfold eraseValue
    exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyq⟩⟩
  have hright : IsNonemptySetPartition
      (W.partition.valueCells.drop (q.val + 1)) :=
    W.partition.valueCells_nonempty.drop (q.val + 1)
  have happend : W.partition.tailPeriod (q.val + 1) ≤
      AddAction.stabilizer A
        (W.partition.tailSumsetAfterErase q x q.val : Set A) := by
    unfold Theorem21SetPartition.tailPeriod
      Theorem21SetPartition.tailSumset
      Theorem21SetPartition.tailSumsetAfterErase
      Theorem21SetPartition.tailValueCells
    rw [W.partition.tailValueCellsAfterErase_decompose q x le_rfl]
    simp only [Nat.sub_self, List.take_zero, List.nil_append]
    exact stabilizer_fullLayer_append_right_mono
      [eraseValue (W.partition.valueCell q) x]
      (W.partition.valueCells.drop (q.val + 1)) hleft hright
  exact hperiodNest.trans happend

omit [Fintype A] in
/-- The same earlier-source periodicity argument only needs the erased cell
to remain nonempty.  This form is used in Lemma 4, where duplication is known
modulo the earlier period `H_{k_j}` rather than modulo the final `H_k`. -/
theorem WeakFactorForm.periodic_tailSumsetAfterErase_of_source_lt_of_duplicate
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (q : Fin n) (x y : A)
    (hy : y ∈ W.partition.valueCell q) (hyx : y ≠ x)
    (hqrho : q.val < rho) :
    W.partition.tailPeriod rho ≤
      AddAction.stabilizer A
        (W.partition.tailSumsetAfterErase q x q.val : Set A) := by
  classical
  have hsucc : q.val + 1 ≤ rho := by omega
  have hperiodNest : W.partition.tailPeriod rho ≤
      W.partition.tailPeriod (q.val + 1) :=
    W.partition.stabilizer_tailSumset_antitone hsucc
  have hleft : IsNonemptySetPartition
      [eraseValue (W.partition.valueCell q) x] := by
    intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    subst B
    unfold eraseValue
    exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hy⟩⟩
  have hright : IsNonemptySetPartition
      (W.partition.valueCells.drop (q.val + 1)) :=
    W.partition.valueCells_nonempty.drop (q.val + 1)
  have happend : W.partition.tailPeriod (q.val + 1) ≤
      AddAction.stabilizer A
        (W.partition.tailSumsetAfterErase q x q.val : Set A) := by
    unfold Theorem21SetPartition.tailPeriod
      Theorem21SetPartition.tailSumset
      Theorem21SetPartition.tailSumsetAfterErase
      Theorem21SetPartition.tailValueCells
    rw [W.partition.tailValueCellsAfterErase_decompose q x le_rfl]
    simp only [Nat.sub_self, List.take_zero, List.nil_append]
    exact stabilizer_fullLayer_append_right_mono
      [eraseValue (W.partition.valueCell q) x]
      (W.partition.valueCells.drop (q.val + 1)) hleft hright
  exact hperiodNest.trans happend

omit [Fintype A] in
/-- Full constructive form of dissertation Lemma 1.  It implements the
source's harmless renaming of a doubled representative away from the anchor,
then proves both `rho ≤ q` and nonperiodicity of the erased `rho`-tail. -/
theorem WeakFactorForm.exists_lemma1_representative
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (q : Fin n) (x : A)
    (hexception : W.partition.IsHException
      (W.partition.tailPeriod rho) x)
    (hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod rho) q x) :
    ∃ z : A,
      QuotientAddGroup.mk' (W.partition.tailPeriod rho) z =
        QuotientAddGroup.mk' (W.partition.tailPeriod rho) x ∧
      W.partition.IsHException (W.partition.tailPeriod rho) z ∧
      W.partition.IsHDoubledInCell (W.partition.tailPeriod rho) q z ∧
      occurrenceValue xs (I.anchor q) ≠ z ∧
      rho ≤ q.val ∧
      ¬ W.partition.tailPeriod rho ≤
        AddAction.stabilizer A
          (W.partition.tailSumsetAfterErase q z rho : Set A) := by
  obtain ⟨z, hzquot, hzException, hzDouble, hzAnchor, hzMin⟩ :=
    W.exists_lemma1_minTail_representative q x hexception hdouble
  have hrhoq : rho ≤ q.val := by
    by_contra hnot
    have hqrho : q.val < rho := by omega
    have hperiod := W.periodic_tailSumsetAfterErase_of_source_lt
      q z hzDouble hqrho
    apply hzMin
    simpa [Nat.min_eq_right (Nat.le_of_lt hqrho)] using hperiod
  refine ⟨z, hzquot, hzException, hzDouble, hzAnchor, hrhoq, ?_⟩
  simpa [Nat.min_eq_left hrhoq] using hzMin

omit [Fintype A] in
/-- `q`-in-tail maximality contradiction used inside dissertation Lemma 1.
For literal membership in `Lambda_{k+1}`, the missing target cell may be
anywhere: even when the insertion enlarges the `k`-tail, prior-stage
maximality forces equality of the two tail sumsets before quotient incidence
can increase.  This is still the `k ≤ q` branch; the full source lemma first
works at `l = min k q` and then derives this inequality. -/
theorem Definition1Transition.not_periodic_tailAfterErase_of_doubledException
    {xs : List A} {seed : Selection xs} {n k : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {prior : Definition1ExtremalChain xs seed n k previous}
    {F P : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition k previous next F)
    (hP : step.InLambda P)
    (H : AddSubgroup A)
    (hH : H = AddAction.stabilizer A
      (previous.chosen.tailSumset k : Set A))
    (q d : Fin n) (x : A) (hkq : k ≤ q.val)
    (hmissing : QuotientAddGroup.mk' H x ∉
      quotientLayer H (P.valueCell d))
    (hdouble : P.IsHDoubledInCell H q x) :
    ¬ H ≤ AddAction.stabilizer A
      (P.tailSumsetAfterErase q x k : Set A) := by
  classical
  subst H
  intro hperiodic
  rcases hdouble with ⟨hxq, y, hyq, hyx, hyquot⟩
  rcases Finset.mem_image.mp hxq with ⟨i, hiq, hix⟩
  rcases Finset.mem_image.mp hyq with ⟨j, hjq, hjy⟩
  have hqd : q ≠ d := by
    intro hqd
    subst d
    apply hmissing
    exact (mem_quotientLayer_iff
      (AddAction.stabilizer A
        (previous.chosen.tailSumset k : Set A))
      (P.valueCell q) _).2 ⟨x, hxq, rfl⟩
  have hji : j ≠ i := by
    intro hji
    subst j
    apply hyx
    rw [← hix, ← hjy]
  have htarget : ∀ z ∈ P.cells d,
      occurrenceValue xs z ≠ occurrenceValue xs i := by
    intro z hzd hzvalue
    apply hmissing
    apply (mem_quotientLayer_iff
      (AddAction.stabilizer A
        (previous.chosen.tailSumset k : Set A))
      (P.valueCell d) _).2
    refine ⟨occurrenceValue xs z,
      Finset.mem_image.mpr ⟨z, hzd, rfl⟩, ?_⟩
    simp [hzvalue, hix]
  obtain ⟨Q, hQcells, _hQsupport⟩ := P.exists_moveOccurrence
    hqd hiq ⟨j, hjq, hji⟩ htarget
  have hPtail : P.tailSumset k = previous.chosen.tailSumset k := hP.2.1
  have hdoubleP : P.IsHDoubledInCell
      (AddAction.stabilizer A (P.tailSumset k : Set A)) q x := by
    simpa [hPtail] using
      (show P.IsHDoubledInCell
        (AddAction.stabilizer A
          (previous.chosen.tailSumset k : Set A)) q x from
        ⟨hxq, y, hyq, hyx, hyquot⟩)
  have hperiodicP : AddAction.stabilizer A
        (P.tailSumset k : Set A) ≤
      AddAction.stabilizer A
        (P.tailSumsetAfterErase q x k : Set A) := by
    simpa [hPtail] using hperiodic
  have hmono :
      Definition1ExtremalChain.MonotoneReplacement P Q prior :=
    Definition1ExtremalChain.MonotoneReplacement.of_moveOccurrence_of_later_periodic
      hP.1 le_rfl hkq hqd hiq hix hdoubleP hQcells hperiodicP
  have hQprevious : Q ∈ previous.upsilon :=
    prior.mem_final_of_monotoneReplacement hmono
  have hPerase : P.tailSumset k = P.tailSumsetAfterErase q x k :=
    P.tailSumset_eq_afterErase_of_periodic
      (AddAction.stabilizer A
        (previous.chosen.tailSumset k : Set A)) q hkq hyq hyx hyquot
      hperiodic
  have hPsubsetQ : P.tailSumset k ⊆ Q.tailSumset k :=
    P.tailSumset_subset_moveOccurrence_of_erase_eq hqd hiq hQcells k
      (by simpa [hix] using hPerase)
  have hQcard : (Q.tailSumset k).card =
      (previous.chosen.tailSumset k).card :=
    prior.tail_card_eq_chosen_of_mem hQprevious
  have hQeqP : Q.tailSumset k = P.tailSumset k := by
    exact (Finset.eq_of_subset_of_card_le hPsubsetQ (by
      rw [hQcard, hPtail])).symm
  have hQtail : Q.tailSumset k = previous.chosen.tailSumset k := by
    rw [hQeqP, hPtail]
  have hQinc : Q.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset k : Set A)) =
      P.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset k : Set A)) + 1 :=
    P.quotientIncidenceAt_move_eq_add_one
      (AddAction.stabilizer A
        (previous.chosen.tailSumset k : Set A))
      hqd hiq hix ⟨hxq, y, hyq, hyx, hyquot⟩ hmissing hQcells
  have hQmax := step.incidence_maximal Q hQprevious hQtail
  have hPinc := hP.2.2
  rw [hQinc, hPinc] at hQmax
  omega

omit [AddCommGroup A] [Fintype A] in
/-- Natural-number closing step of dissertation Lemma 2.  Here `k = n-ρ`,
`total = Σ|Y_i|`, `other = Σ_{i≠q}|Y_i|`, `cell = |Y_q|`,
`wholeCard` is the full tail sumset cardinality, and `removedCard` is the
sumset cardinality with the `q`-th cell removed.  The nonempty-cell and
`ρ ≤ n-2` facts are retained as `1 ≤ cell` and `2 ≤ k`. -/
theorem lemma2_nat_closing
    {total other cell k wholeCard removedCard : ℕ}
    (htotal : total = other + cell) (hcell : 1 ≤ cell) (hk : 2 ≤ k)
    (hIII : wholeCard < total - k + 1)
    (h33 : removedCard + cell - 1 ≤ wholeCard) :
    removedCard < other - (k - 1) + 1 := by
  omega

omit [Fintype A] in
/-- All index and truncated-subtraction bookkeeping in dissertation Lemma 2,
once equation (3.3) has been established.  This lemma assumes only the weak
factor form and condition (III); condition (II) is intentionally absent. -/
theorem WeakFactorForm.lemma2_of_equation33
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (hIII : (W.partition.tailSumset rho).card <
      (∑ c ∈ tailIndices n rho, (W.partition.valueCell c).card) -
        (n - rho) + 1)
    (q : Fin n) (hrhoq : rho ≤ q.val)
    (h33 : (W.partition.tailSumsetWithoutCell q rho).card +
        (W.partition.valueCell q).card - 1 ≤
      (W.partition.tailSumset rho).card) :
    (W.partition.tailSumsetWithoutCell q rho).card <
      (∑ c ∈ (tailIndices n rho).erase q,
        (W.partition.valueCell c).card) - ((n - rho) - 1) + 1 := by
  have htotal := W.partition.sum_tailIndices_erase_add q hrhoq
  have hcell : 1 ≤ (W.partition.valueCell q).card :=
    Finset.card_pos.mpr (W.partition.valueCells_nonempty
      (W.partition.valueCell q) (by
        classical
        simp [Theorem21SetPartition.valueCells]))
  have hk : 2 ≤ n - rho :=
    Nat.le_sub_of_add_le (by
      have hrange := W.range
      omega : 2 + rho ≤ n)
  exact lemma2_nat_closing htotal.symm hcell hk hIII h33

omit [Fintype A] in
/-- Dissertation Lemma 2 in its complete ordinary, zero-based form.  Lemma
1 first chooses an anchor-safe representative of the doubled exceptional
quotient class and proves that its cell lies in the tail.  Scherk's
Proposition 1.3 then gives equation (3.3), and the preceding arithmetic lemma
closes condition (III) without any use of condition (II). -/
theorem WeakFactorForm.lemma2
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (hIII : (W.partition.tailSumset rho).card <
      (∑ c ∈ tailIndices n rho, (W.partition.valueCell c).card) -
        (n - rho) + 1)
    (q : Fin n) (x : A)
    (hexception : W.partition.IsHException
      (W.partition.tailPeriod rho) x)
    (hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod rho) q x) :
    (W.partition.tailSumsetWithoutCell q rho).card <
      (∑ c ∈ (tailIndices n rho).erase q,
        (W.partition.valueCell c).card) - ((n - rho) - 1) + 1 := by
  classical
  obtain ⟨z, _hzquot, _hzException, hzDouble, _hzAnchor,
      hrhoq, hzNotPeriodic⟩ :=
    W.exists_lemma1_representative q x hexception hdouble
  have hzmem : z ∈ W.partition.valueCell q := hzDouble.1
  have hother : (W.partition.tailSumsetWithoutCell q rho).Nonempty :=
    W.partition.tailSumsetWithoutCell_nonempty q
  have hne := W.partition.withoutCell_add_ne_add_erase
    q z hrhoq hzNotPeriodic
  unfold eraseValue at hne
  have h33 := card_add_sub_one_le_of_add_ne_add_erase
    (W.partition.tailSumsetWithoutCell q rho)
    (W.partition.valueCell q) hother hzmem hne
  have hwhole := W.partition.tailSumset_eq_withoutCell_add q hrhoq
  rw [← hwhole] at h33
  exact W.lemma2_of_equation33 hIII q hrhoq h33

omit [Fintype A] in
/-- Condition (II)'s subtraction by `rho+1` is nontruncating: the tail
quotient contributes at least one class and each leading cell contributes at
least one. -/
theorem WeakFactorForm.quotient_growth_base_le
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) :
    rho + 1 ≤
      (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset rho)).card +
        ∑ c ∈ leadingIndices n rho,
          (quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c)).card := by
  classical
  have hrhon : rho ≤ n := by
    have hrange := W.range
    omega
  have htail : 1 ≤
      (quotientLayer (W.partition.tailPeriod rho)
        (W.partition.tailSumset rho)).card :=
    Finset.card_pos.mpr (quotientLayer_nonempty _ _
      (W.partition.tailSumset_nonempty rho))
  have hleading : rho ≤
      ∑ c ∈ leadingIndices n rho,
        (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.valueCell c)).card := by
    calc
      rho = (leadingIndices n rho).card := (card_leadingIndices hrhon).symm
      _ =
          ∑ c ∈ leadingIndices n rho, 1 := by simp
      _ ≤ ∑ c ∈ leadingIndices n rho,
          (quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c)).card := by
        exact Finset.sum_le_sum fun c _ ↦
          Finset.card_pos.mpr (quotientLayer_nonempty _ _
            (W.partition.valueCells_nonempty
              (W.partition.valueCell c) (by
                simp [Theorem21SetPartition.valueCells])))
  omega

omit [Fintype A] in
/-- Exceptions descend along subgroup inclusion: if a quotient class is
missing modulo the larger subgroup, it was already missing modulo the
smaller subgroup. -/
theorem Theorem21SetPartition.isHException_of_le
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {H K : AddSubgroup A} (hHK : H ≤ K) {x : A}
    (hx : P.IsHException K x) : P.IsHException H x := by
  classical
  rcases hx with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro hxH
  obtain ⟨y, hy, hyx⟩ :=
    (mem_quotientLayer_iff H (P.valueCell c) _).1 hxH
  apply hc
  exact (mem_quotientLayer_iff K (P.valueCell c) _).2
    ⟨y, hy, quotient_eq_of_subgroup_le hHK hyx⟩

omit [Fintype A] in
/-- Every leading cell in a weak factor form contains a representative whose
class modulo the final tail period occurs exactly once in that cell.  This
is the precise consequence of condition (IV) and dissertation Lemma 1 used
in the holes count of Lemma 3. -/
theorem WeakFactorForm.exists_unique_tailPeriod_representative_of_leading
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) (c : Fin n) (hc : c.val < rho) :
    ∃ x ∈ W.partition.valueCell c,
      ∀ y ∈ W.partition.valueCell c,
        QuotientAddGroup.mk' (W.partition.tailPeriod rho) y =
          QuotientAddGroup.mk' (W.partition.tailPeriod rho) x →
        y = x := by
  obtain ⟨x, hx, hxException⟩ := W.leading_exception c hc
  have hperiodLe : W.partition.tailPeriod rho ≤
      W.partition.tailPeriod c.val :=
    W.partition.stabilizer_tailSumset_antitone (Nat.le_of_lt hc)
  have hxFinal : W.partition.IsHException
      (W.partition.tailPeriod rho) x :=
    W.partition.isHException_of_le hperiodLe hxException
  refine ⟨x, hx, ?_⟩
  intro y hy hyquot
  by_contra hyx
  have hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod rho) c x :=
    ⟨hx, y, hy, hyx, hyquot⟩
  obtain ⟨_z, _hzquot, _hzException, _hzDouble, _hzAnchor,
      hrhoc, _hzNotPeriodic⟩ :=
    W.exists_lemma1_representative c x hxFinal hdouble
  omega

omit [Fintype A] in
/-- Erasing the unique representative of one quotient class erases exactly
that class from the quotient image. -/
theorem quotientLayer_erase_eq_erase_of_unique
    [DecidableEq A] (H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (C : Finset A) {x : A}
    (hunique : ∀ y ∈ C,
      QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x → y = x) :
    quotientLayer H (C.erase x) =
      (quotientLayer H C).erase (QuotientAddGroup.mk' H x) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨y, hy, hyq⟩ :=
      (mem_quotientLayer_iff H (C.erase x) q).1 hq
    have hyData := Finset.mem_erase.mp hy
    apply Finset.mem_erase.mpr
    refine ⟨?_, (mem_quotientLayer_iff H C q).2 ⟨y, hyData.2, hyq⟩⟩
    intro hqx
    have hyx : QuotientAddGroup.mk' H y =
        QuotientAddGroup.mk' H x := hyq.trans hqx
    exact hyData.1 (hunique y hyData.2 hyx)
  · intro hq
    have hqData := Finset.mem_erase.mp hq
    obtain ⟨y, hy, hyq⟩ :=
      (mem_quotientLayer_iff H C q).1 hqData.2
    apply (mem_quotientLayer_iff H (C.erase x) q).2
    refine ⟨y, Finset.mem_erase.mpr ⟨?_, hy⟩, hyq⟩
    intro hyx
    subst y
    exact hqData.1 hyq.symm

/-- An `H`-periodic finite set is the disjoint union of the full `H`-cosets
met by it, so its cardinality is exactly `|H|` times its quotient image. -/
theorem card_eq_natCard_mul_card_quotientLayer_of_le_stabilizer
    (H : AddSubgroup A) (B : Finset A)
    (hperiodic : H ≤ AddAction.stabilizer A (B : Set A)) :
    B.card = Nat.card H * (quotientLayer H B).card := by
  classical
  have hsaturate : B + dgmSubgroupFinset H = B := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨b, hb, h, hh, rfl⟩ := Finset.mem_add.mp hz
      have hstab := hperiodic ((mem_dgmSubgroupFinset_iff H h).1 hh)
      rw [AddAction.mem_stabilizer_set] at hstab
      have := (hstab b).2 hb
      simpa [add_comm] using this
    · intro b hb
      exact Finset.mem_add.mpr
        ⟨b, hb, 0, (mem_dgmSubgroupFinset_iff H 0).2 H.zero_mem,
          add_zero b⟩
  calc
    B.card = (B + dgmSubgroupFinset H).card := by rw [hsaturate]
    _ = Nat.card H * (quotientLayer H B).card :=
      card_add_dgmSubgroupFinset_eq H B

omit [Fintype A] in
/-- In an `H`-periodic finite set, meeting the quotient image is equivalent
to literal membership: the entire represented `H`-coset is present. -/
theorem mem_quotientLayer_iff_of_le_stabilizer
    [DecidableEq A] (H : AddSubgroup A) (B : Finset A)
    (hperiodic : H ≤ AddAction.stabilizer A (B : Set A)) (z : A) :
    QuotientAddGroup.mk' H z ∈ quotientLayer H B ↔ z ∈ B := by
  constructor
  · intro hz
    obtain ⟨b, hb, hbz⟩ :=
      (mem_quotientLayer_iff H B _).1 hz
    have hbzH : b - z ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hbz
    have hzbH : z - b ∈ H := by
      simpa only [neg_sub] using H.neg_mem hbzH
    have hstab := hperiodic hzbH
    rw [AddAction.mem_stabilizer_set] at hstab
    have htranslated := (hstab b).2 hb
    change (z - b) + b ∈ B at htranslated
    simpa [sub_eq_add_neg, add_assoc] using htranslated
  · intro hz
    exact (mem_quotientLayer_iff H B _).2 ⟨z, hz, rfl⟩

omit [Fintype A] in
/-- A translation stabilizing the quotient image of an `H`-periodic set
lifts to a literal translation stabilizing the original set. -/
theorem sub_mem_stabilizer_of_quotient_sub_mem_stabilizer
    [DecidableEq A] (H : AddSubgroup A) (B : Finset A)
    (hperiodic : H ≤ AddAction.stabilizer A (B : Set A))
    {x y : A}
    (hxy : QuotientAddGroup.mk' H y - QuotientAddGroup.mk' H x ∈
      AddAction.stabilizer (A ⧸ H) (quotientLayer H B : Set (A ⧸ H))) :
    y - x ∈ AddAction.stabilizer A (B : Set A) := by
  rw [AddAction.mem_stabilizer_set]
  intro z
  change (y - x) + z ∈ B ↔ z ∈ B
  rw [← mem_quotientLayer_iff_of_le_stabilizer H B hperiodic
      ((y - x) + z),
    ← mem_quotientLayer_iff_of_le_stabilizer H B hperiodic z]
  have hstab := hxy
  rw [AddAction.mem_stabilizer_set] at hstab
  have hz := hstab (QuotientAddGroup.mk' H z)
  change ((QuotientAddGroup.mk' H y - QuotientAddGroup.mk' H x) +
      QuotientAddGroup.mk' H z ∈ quotientLayer H B ↔
    QuotientAddGroup.mk' H z ∈ quotientLayer H B)
  exact hz

omit [Fintype A] in
/-- The final tail period also stabilizes the full factor-form sumset. -/
theorem WeakFactorForm.tailPeriod_le_sumset_stabilizer
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) :
    W.partition.tailPeriod rho ≤
      AddAction.stabilizer A (W.partition.sumset : Set A) := by
  have hmono := W.partition.stabilizer_tailSumset_antitone
    (show 0 ≤ rho from Nat.zero_le rho)
  simpa [Theorem21SetPartition.tailPeriod,
    Theorem21SetPartition.tailSumset,
    Theorem21SetPartition.tailValueCells,
    Theorem21SetPartition.sumset] using hmono

omit [Fintype A] in
/-- Quotient projection commutes exactly with finite sumsets. -/
theorem quotientLayer_add [DecidableEq A]
    (H : AddSubgroup A) [DecidableEq (A ⧸ H)] (B C : Finset A) :
    quotientLayer H (B + C) = quotientLayer H B + quotientLayer H C := by
  ext q
  constructor
  · intro hq
    obtain ⟨z, hz, hzq⟩ := (mem_quotientLayer_iff H (B + C) q).1 hq
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp hz
    apply Finset.mem_add.mpr
    refine ⟨QuotientAddGroup.mk' H b,
      (mem_quotientLayer_iff H B _).2 ⟨b, hb, rfl⟩,
      QuotientAddGroup.mk' H c,
      (mem_quotientLayer_iff H C _).2 ⟨c, hc, rfl⟩, ?_⟩
    exact hzq
  · intro hq
    obtain ⟨qb, hqb, qc, hqc, rfl⟩ := Finset.mem_add.mp hq
    obtain ⟨b, hb, hbq⟩ := (mem_quotientLayer_iff H B qb).1 hqb
    obtain ⟨c, hc, hcq⟩ := (mem_quotientLayer_iff H C qc).1 hqc
    apply (mem_quotientLayer_iff H (B + C) (qb + qc)).2
    refine ⟨b + c, Finset.mem_add.mpr ⟨b, hb, c, hc, rfl⟩, ?_⟩
    change QuotientAddGroup.mk' H b + QuotientAddGroup.mk' H c = qb + qc
    simpa only [QuotientAddGroup.mk'_apply] using
      congrArg₂ (fun u v : A ⧸ H ↦ u + v) hbq hcq

omit [Fintype A] in
/-- A tail sumset splits into its first cell and the following tail. -/
theorem Theorem21SetPartition.tailSumset_eq_valueCell_add_succ
    [DecidableEq A] {xs : List A} {n m : ℕ}
    (P : Theorem21SetPartition xs n m) (j : Fin n) :
    P.tailSumset j.val = P.valueCell j + P.tailSumset (j.val + 1) := by
  have hdecomp := P.tailValueCells_decompose j (r := j.val) le_rfl
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailValueCells at hdecomp ⊢
  rw [hdecomp]
  simp only [Nat.sub_self, List.take_zero, List.nil_append,
    fullLayerSumSpectrum_cons]
  apply Finset.ext
  intro x
  simp only [Finset.mem_add]

omit [Fintype A] in
/-- The tail beginning at an erased cell splits into that erased cell and
the unchanged following tail. -/
theorem Theorem21SetPartition.tailSumsetAfterErase_eq_eraseValue_add_succ
    [DecidableEq A] {xs : List A} {n m : ℕ}
    (P : Theorem21SetPartition xs n m) (q : Fin n) (x : A) :
    P.tailSumsetAfterErase q x q.val =
      eraseValue (P.valueCell q) x + P.tailSumset (q.val + 1) := by
  have hdecomp := P.tailValueCellsAfterErase_decompose q x
    (r := q.val) le_rfl
  unfold Theorem21SetPartition.tailSumsetAfterErase
  rw [hdecomp]
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailValueCells
  simp only [Nat.sub_self, List.take_zero, List.nil_append,
    fullLayerSumSpectrum_cons]
  apply Finset.ext
  intro z
  simp only [Finset.mem_add]

omit [Fintype A] in
/-- The local strict deficit in dissertation Lemma 5 is exactly the
contrapositive of Scherk's one-erasure bound: deleting any chosen value from
the current cell leaves the corresponding tail sumset unchanged. -/
theorem Theorem21SetPartition.tailSumset_eq_afterErase_of_local_deficit
    {xs : List A} {n m : ℕ}
    (P : Theorem21SetPartition xs n m) (q : Fin n) {z : A}
    (hz : z ∈ P.valueCell q)
    (hdeficit :
      (P.tailSumset q.val).card <
        (P.tailSumset (q.val + 1)).card + (P.valueCell q).card - 1) :
    P.tailSumset q.val = P.tailSumsetAfterErase q z q.val := by
  classical
  by_contra hne
  have hsumne :
      P.tailSumset (q.val + 1) + P.valueCell q ≠
        P.tailSumset (q.val + 1) + (P.valueCell q).erase z := by
    intro heq
    apply hne
    rw [P.tailSumset_eq_valueCell_add_succ q,
      P.tailSumsetAfterErase_eq_eraseValue_add_succ q z]
    simpa [eraseValue, add_comm] using heq
  have hscherk := card_add_sub_one_le_of_add_ne_add_erase
    (P.tailSumset (q.val + 1)) (P.valueCell q)
    (P.tailSumset_nonempty (q.val + 1)) hz hsumne
  have hbound :
      (P.tailSumset (q.val + 1)).card + (P.valueCell q).card - 1 ≤
        (P.tailSumset q.val).card := by
    simpa [P.tailSumset_eq_valueCell_add_succ q, add_comm] using hscherk
  omega

omit [Fintype A] in
/-- Once deletion is invisible at its own cell, it is invisible in every
earlier tail as well: the earlier cells contribute the same left summand. -/
theorem Theorem21SetPartition.tailSumset_eq_afterErase_of_le
    {xs : List A} {n m r : ℕ}
    (P : Theorem21SetPartition xs n m) (q : Fin n) (z : A)
    (hrq : r ≤ q.val)
    (hlocal : P.tailSumset q.val =
      P.tailSumsetAfterErase q z q.val) :
    P.tailSumset r = P.tailSumsetAfterErase q z r := by
  classical
  have hmiddle :
      P.valueCell q + P.tailSumset (q.val + 1) =
        eraseValue (P.valueCell q) z + P.tailSumset (q.val + 1) := by
    simpa [P.tailSumset_eq_valueCell_add_succ q,
      P.tailSumsetAfterErase_eq_eraseValue_add_succ q z] using hlocal
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailSumsetAfterErase
  rw [P.tailValueCells_decompose q hrq,
    P.tailValueCellsAfterErase_decompose q z hrq,
    fullLayerSumSpectrum_append, fullLayerSumSpectrum_append,
    fullLayerSumSpectrum_cons, fullLayerSumSpectrum_cons]
  unfold Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailValueCells at hmiddle
  rw [hmiddle]

omit [Fintype A] in
/-- Lemma 5's condition (III) supplies a nonterminal tail cell from which
every chosen value may be erased without changing any Definition 1 tail up
to the current factor stage. -/
theorem FactorForm.exists_local_tail_erasure
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n} (F : FactorForm I rho) :
    ∃ q : Fin n,
      rho ≤ q.val ∧ q.val + 1 < n ∧
        ∀ z ∈ F.partition.valueCell q, ∀ s, s ≤ rho →
          F.partition.tailSumset s =
            F.partition.tailSumsetAfterErase q z s := by
  classical
  obtain ⟨q, hrhoq, hqLast, hdeficit⟩ := F.exists_local_tail_deficit
  refine ⟨q, hrhoq, hqLast, ?_⟩
  intro z hz s hsrho
  apply F.partition.tailSumset_eq_afterErase_of_le q z
    (hsrho.trans hrhoq)
  exact F.partition.tailSumset_eq_afterErase_of_local_deficit q hz hdeficit

omit [Fintype A] in
/-- The preceding tail recursion after projection to an arbitrary quotient.
-/
theorem Theorem21SetPartition.quotientLayer_tailSumset_eq_add_succ
    [DecidableEq A] {xs : List A} {n m : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    [DecidableEq (A ⧸ H)] (j : Fin n) :
    quotientLayer H (P.tailSumset j.val) =
      quotientLayer H (P.valueCell j) +
        quotientLayer H (P.tailSumset (j.val + 1)) := by
  rw [P.tailSumset_eq_valueCell_add_succ j, quotientLayer_add]

omit [Fintype A] in
/-- Equation-(3.2) contradiction at one completed Definition 1 stage: two
members of the same next maximal family have the same incidence objective,
so one cannot exceed the other by one. -/
theorem Definition1Transition.not_incidence_add_one_of_mem_next
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F P Q : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous next F)
    (hP : P ∈ next.upsilon) (hQ : Q ∈ next.upsilon)
    (hinc : Q.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)) =
      P.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)) + 1) : False := by
  have hPdata := (step.mem_next_upsilon_iff P).1 hP
  have hQdata := (step.mem_next_upsilon_iff Q).1 hQ
  rw [hPdata.2.2.1, hQdata.2.2.1] at hinc
  omega

omit [Fintype A] in
/-- Exact final contradiction of the doubled-exception exchange, conditional
only on the still-concrete Lemma 1 obligation that every support-preserving
exchange with the computed `+1` incidence remains in the next recursively
maximal family.  This theorem is deliberately not labeled as the complete
Lemma 1: proving `hadmissible` from the tail and quotient inclusions is the
remaining source argument. -/
theorem Definition1Transition.not_isHDoubledException_of_move_admissible
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {previous next : Definition1ExtremalState xs seed n}
    {F P : Theorem21SetPartition xs n seed.card}
    (step : Definition1Transition r previous next F)
    (hP : P ∈ next.upsilon)
    (hadmissible : ∀ Q : Theorem21SetPartition xs n seed.card,
      Q.support = P.support →
      Q.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) =
        P.quotientIncidenceAt
          (AddAction.stabilizer A
            (previous.chosen.tailSumset r : Set A)) + 1 →
      Q ∈ next.upsilon)
    (x : A) :
    ¬ P.IsHDoubledException
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)) x := by
  intro hx
  obtain ⟨Q, hQsupport, hQinc⟩ :=
    P.exists_moveOccurrence_quotientIncidenceAt_eq_add_one
      (AddAction.stabilizer A
        (previous.chosen.tailSumset r : Set A)) hx
  exact step.not_incidence_add_one_of_mem_next hP
    (hadmissible Q hQsupport hQinc) hQinc

/-- Membership in `A_c + H` is exactly membership of the quotient class in
the projected cell. -/
theorem Theorem21SetPartition.mem_thickenedCell_iff_mem_quotientLayer
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (x : A) :
    x ∈ P.thickenedCell H c ↔
      QuotientAddGroup.mk' H x ∈ quotientLayer H (P.valueCell c) := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_add.mp hx with ⟨a, ha, h, hh, rfl⟩
    apply (mem_quotientLayer_iff H (P.valueCell c) _).2
    refine ⟨a, ha, ?_⟩
    change QuotientAddGroup.mk' H a = QuotientAddGroup.mk' H (a + h)
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq_iff_sub_mem]
    have hh' : h ∈ H := (mem_subgroupFinset H h).1 hh
    convert H.neg_mem hh' using 1
    abel
  · intro hx
    obtain ⟨a, ha, haquot⟩ :=
      (mem_quotientLayer_iff H (P.valueCell c) _).1 hx
    have hax : a - x ∈ H :=
      QuotientAddGroup.eq_iff_sub_mem.mp haquot
    have hxa : x - a ∈ H := by
      simpa only [neg_sub] using H.neg_mem hax
    apply Finset.mem_add.mpr
    refine ⟨a, ha, x - a, (mem_subgroupFinset H (x - a)).2 hxa, ?_⟩
    abel

/-- The dissertation's `H`-exception predicate is exactly failure to lie in
the common `H`-saturation of all cells. -/
theorem Theorem21SetPartition.isHException_iff_not_mem_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (x : A) :
    P.IsHException H x ↔ x ∉ P.commonCore H := by
  classical
  rw [P.mem_commonCore_iff H x]
  simp only [Theorem21SetPartition.IsHException, not_forall]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun hx ↦ hc
      ((P.mem_thickenedCell_iff_mem_quotientLayer H c x).1 hx)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun hx ↦ hc
      ((P.mem_thickenedCell_iff_mem_quotientLayer H c x).2 hx)⟩

/-- If doubled exceptions have been eliminated, quotient projection is
injective on the outside-common-core part of every cell.  This is the exact
counting property needed to turn `e` occurrences into `e` distinct quotient
classes in Theorem E. -/
theorem Theorem21SetPartition.quotient_injOn_outside_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A)
    (hno : ∀ x : A, ¬ P.IsHDoubledException H x)
    (c : Fin n) :
    Set.InjOn (QuotientAddGroup.mk' H)
      (P.valueCell c \ P.commonCore H : Set A) := by
  intro x hx y hy hquot
  by_contra hxy
  have hxException : P.IsHException H x :=
    (P.isHException_iff_not_mem_commonCore H x).2
      hx.2
  have hxDoubled : P.IsHDoubledInCell H c x := by
    refine ⟨hx.1, y, hy.1, ?_, hquot.symm⟩
    exact fun hyx ↦ hxy hyx.symm
  exact hno x ⟨hxException, c, hxDoubled⟩

/-- A finite set has at most `|H|` representatives in each quotient class,
hence its cardinality is at most `|H|` times the size of its quotient image.
-/
theorem card_le_natCard_mul_card_quotientLayer
    (H : AddSubgroup A) (B : Finset A) :
    B.card ≤ Nat.card H * (quotientLayer H B).card := by
  classical
  apply Finset.card_le_mul_card_image B (Nat.card H)
  intro q hq
  obtain ⟨x, hx, hxq⟩ := (mem_quotientLayer_iff H B q).1 hq
  have hmap : Set.MapsTo (fun a : A ↦ a - x)
      (B.filter fun a ↦ QuotientAddGroup.mk' H a = q : Set A)
      (subgroupFinset H : Set A) := by
    intro a ha
    have haq := (Finset.mem_filter.mp ha).2
    apply (mem_subgroupFinset H (a - x)).2
    exact QuotientAddGroup.eq_iff_sub_mem.mp (haq.trans hxq.symm)
  have hinj : Set.InjOn (fun a : A ↦ a - x)
      (B.filter fun a ↦ QuotientAddGroup.mk' H a = q : Set A) := by
    intro a _ b _ hab
    exact sub_left_injective hab
  have hfiber := Finset.card_le_card_of_injOn (fun a : A ↦ a - x)
    hmap hinj
  have hHcard : (subgroupFinset H).card = Nat.card H := by
    simpa [subgroupFinset, Nat.card_eq_fintype_card] using
      (Fintype.card_subtype (fun x : A ↦ x ∈ H)).symm
  simpa [hHcard] using hfiber

/-- A cell with a singleton quotient fiber has at least `|H|-1` holes in
its `H`-saturation.  The proof erases the singleton fiber and applies the
general fiber-cardinality bound to the remaining quotient classes. -/
theorem card_add_natCard_sub_one_le_mul_quotientLayer_of_unique
    (H : AddSubgroup A) (C : Finset A) {x : A}
    (hx : x ∈ C)
    (hunique : ∀ y ∈ C,
      QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x → y = x) :
    C.card + (Nat.card H - 1) ≤
      Nat.card H * (quotientLayer H C).card := by
  classical
  have hqmem : QuotientAddGroup.mk' H x ∈ quotientLayer H C :=
    (mem_quotientLayer_iff H C _).2 ⟨x, hx, rfl⟩
  have hqerase := quotientLayer_erase_eq_erase_of_unique H C hunique
  have hcardC : (C.erase x).card + 1 = C.card :=
    Finset.card_erase_add_one hx
  have hcardQ : (quotientLayer H (C.erase x)).card + 1 =
      (quotientLayer H C).card := by
    rw [hqerase]
    exact Finset.card_erase_add_one hqmem
  have herase := card_le_natCard_mul_card_quotientLayer H (C.erase x)
  have hplus : C.card + Nat.card H ≤
      Nat.card H * (quotientLayer H C).card + 1 := by
    calc
      C.card + Nat.card H =
          (C.erase x).card + Nat.card H + 1 := by omega
      _ ≤ Nat.card H * (quotientLayer H (C.erase x)).card +
          Nat.card H + 1 := by omega
      _ = Nat.card H * (quotientLayer H C).card + 1 := by
        rw [← hcardQ]
        simp [Nat.mul_add]
  have hHpos : 1 ≤ Nat.card H := Nat.card_pos
  omega

/-- Kneser's theorem with one singleton stabilizer fiber.  A single element
of `C` that is unique in its coset modulo the actual stabilizer of `B+C`
recovers the Cauchy--Davenport one-step bound.  This is the exact counting
engine in the non-doubled branch of dissertation Lemma 4. -/
theorem card_add_sub_one_le_of_unique_addStab_fiber
    [DecidableEq A] (B C : Finset A)
    (hB : B.Nonempty) (hC : C.Nonempty)
    {x : A} (hx : x ∈ C)
    (hunique : ∀ y ∈ C,
      y - x ∈ AddAction.stabilizer A ((B + C : Finset A) : Set A) →
        y = x) :
    B.card + C.card - 1 ≤ (B + C).card := by
  classical
  let K : AddSubgroup A :=
    AddAction.stabilizer A ((B + C : Finset A) : Set A)
  have hS : (B + C).Nonempty := hB.add hC
  have hKfin : (B + C).addStab = dgmSubgroupFinset K := by
    ext a
    rw [← Finset.mem_coe, Finset.coe_addStab hS]
    exact (mem_dgmSubgroupFinset_iff K a).symm
  have huniqueQ : ∀ y ∈ C,
      QuotientAddGroup.mk' K y = QuotientAddGroup.mk' K x → y = x := by
    intro y hy hyq
    exact hunique y hy (QuotientAddGroup.eq_iff_sub_mem.mp hyq)
  have hCholes :=
    card_add_natCard_sub_one_le_mul_quotientLayer_of_unique
      K C hx huniqueQ
  have hCsat : C.card + (Nat.card K - 1) ≤
      (C + dgmSubgroupFinset K).card := by
    simpa [card_add_dgmSubgroupFinset_eq] using hCholes
  have hBsat : B.card ≤ (B + dgmSubgroupFinset K).card := by
    apply Finset.card_le_card
    intro b hb
    exact Finset.mem_add.mpr
      ⟨b, hb, 0, (mem_dgmSubgroupFinset_iff K 0).2 K.zero_mem,
        add_zero b⟩
  have hkneser := Finset.add_kneser B C
  rw [hKfin] at hkneser
  rw [card_dgmSubgroupFinset] at hkneser
  have hKpos : 1 ≤ Nat.card K := Nat.card_pos
  omega

/-- Kneser's theorem at a strict local-deficit step: no value of the current
cell is alone modulo the actual stabilizer of that local tail. -/
theorem Theorem21SetPartition.exists_duplicate_tailPeriod_of_local_deficit
    {xs : List A} {n m : ℕ}
    (P : Theorem21SetPartition xs n m) (q : Fin n) {z : A}
    (hz : z ∈ P.valueCell q)
    (hdeficit :
      (P.tailSumset q.val).card <
        (P.tailSumset (q.val + 1)).card + (P.valueCell q).card - 1) :
    ∃ y ∈ P.valueCell q, y ≠ z ∧
      QuotientAddGroup.mk' (P.tailPeriod q.val) y =
        QuotientAddGroup.mk' (P.tailPeriod q.val) z := by
  classical
  by_contra hnone
  have hunique : ∀ y ∈ P.valueCell q,
      y - z ∈ AddAction.stabilizer A
        (((P.tailSumset (q.val + 1)) + P.valueCell q : Finset A) : Set A) →
      y = z := by
    intro y hy hyperiod
    by_contra hyz
    apply hnone
    refine ⟨y, hy, hyz, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    unfold Theorem21SetPartition.tailPeriod
    rw [P.tailSumset_eq_valueCell_add_succ q]
    simpa [add_comm] using hyperiod
  have hbound := card_add_sub_one_le_of_unique_addStab_fiber
    (P.tailSumset (q.val + 1)) (P.valueCell q)
    (P.tailSumset_nonempty (q.val + 1))
    (P.valueCells_nonempty (P.valueCell q) (by
      simp [Theorem21SetPartition.valueCells]))
    hz hunique
  have hbound' :
      (P.tailSumset (q.val + 1)).card + (P.valueCell q).card - 1 ≤
        (P.tailSumset q.val).card := by
    simpa [P.tailSumset_eq_valueCell_add_succ q, add_comm] using hbound
  omega

/-- The local-deficit cell contains a labelled occurrence whose value is
different from the fixed anchor, whose final-period quotient class survives
its deletion, and whose deletion is invisible in every tail already fixed by
the factor form.  The duplicate of the anchor value supplies the choice. -/
theorem FactorForm.exists_anchorSafe_local_tail_replacement
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n} (F : FactorForm I rho) :
    ∃ q : Fin n, ∃ y : Occurrence xs,
      rho ≤ q.val ∧ q.val + 1 < n ∧ y ∈ F.partition.cells q ∧
        occurrenceValue xs y ≠ occurrenceValue xs (I.anchor q) ∧
        (∃ z ∈ F.partition.valueCell q,
          z ≠ occurrenceValue xs y ∧
          QuotientAddGroup.mk' (F.partition.tailPeriod rho) z =
            QuotientAddGroup.mk' (F.partition.tailPeriod rho)
              (occurrenceValue xs y)) ∧
        ∀ s, s ≤ rho →
          F.partition.tailSumset s =
            F.partition.tailSumsetAfterErase q
              (occurrenceValue xs y) s := by
  classical
  obtain ⟨q, hrhoq, hqLast, hdeficit⟩ := F.exists_local_tail_deficit
  let a : A := occurrenceValue xs (I.anchor q)
  have ha : a ∈ F.partition.valueCell q := F.admissible.2 q
  obtain ⟨z, hz, hza, hzquotLocal⟩ :=
    F.partition.exists_duplicate_tailPeriod_of_local_deficit q ha hdeficit
  have hlocalFinal : F.partition.tailPeriod q.val ≤
      F.partition.tailPeriod rho :=
    F.partition.stabilizer_tailSumset_antitone hrhoq
  have hzquotFinal :
      QuotientAddGroup.mk' (F.partition.tailPeriod rho) z =
        QuotientAddGroup.mk' (F.partition.tailPeriod rho) a := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact hlocalFinal (QuotientAddGroup.eq_iff_sub_mem.mp hzquotLocal)
  have hzImage := hz
  unfold Theorem21SetPartition.valueCell at hzImage
  obtain ⟨y, hyCell, hyValue⟩ := Finset.mem_image.mp hzImage
  refine ⟨q, y, hrhoq, hqLast, hyCell, ?_, ?_, ?_⟩
  · simpa [a, hyValue] using hza
  · refine ⟨a, ha, ?_, ?_⟩
    · simpa [hyValue] using hza.symm
    · simpa [hyValue] using hzquotFinal.symm
  · intro s hsrho
    have hlocal :=
      F.partition.tailSumset_eq_afterErase_of_local_deficit q hz hdeficit
    simpa [hyValue] using
      F.partition.tailSumset_eq_afterErase_of_le q z
        (hsrho.trans hrhoq) hlocal

omit [Fintype A] in
/-- Any source-chain-preserving replacement that keeps the current factor
tail monotone cannot raise the current quotient-incidence objective: stage
membership fixes the tail cardinality, hence monotonicity fixes the tail
itself, and the literal transition maximality applies. -/
theorem WeakFactorForm.not_incidence_add_one_of_sourceMonotone
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n} (W : WeakFactorForm I rho)
    (Q : Theorem21SetPartition xs n seed.card)
    (hmono : Definition1SourceChain.MonotoneReplacement
      W.partition Q W.chain)
    (htail : W.partition.tailSumset rho ⊆ Q.tailSumset rho)
    (hinc : Q.quotientIncidenceAt (W.partition.tailPeriod rho) =
      W.partition.quotientIncidenceAt (W.partition.tailPeriod rho) + 1) :
    False := by
  have hQprevious : Q ∈ W.previous.upsilon :=
    W.chain.mem_final_of_monotoneReplacement hmono
  have hQcard : (Q.tailSumset rho).card =
      (W.previous.chosen.tailSumset rho).card :=
    W.chain.tail_card_eq_chosen_of_mem hQprevious
  have hPtail : W.partition.tailSumset rho =
      W.previous.chosen.tailSumset rho := W.inLambda.2.1
  have hQeqP : Q.tailSumset rho = W.partition.tailSumset rho :=
    (Finset.eq_of_subset_of_card_le htail (by
      rw [hQcard, hPtail])).symm
  have hQtail : Q.tailSumset rho =
      W.previous.chosen.tailSumset rho := hQeqP.trans hPtail
  have hH : W.partition.tailPeriod rho = AddAction.stabilizer A
      (W.previous.chosen.tailSumset rho : Set A) := by
    unfold Theorem21SetPartition.tailPeriod
    rw [hPtail]
  have hQmax := W.transition.incidence_maximal Q hQprevious hQtail
  have hPinc := W.inLambda.2.2
  rw [← hH] at hQmax hPinc
  rw [hinc, hPinc] at hQmax
  omega

/-- The non-doubled branch of equation (3.4).  It applies the preceding
singleton-fiber Kneser bound in `A/H_k`; quotient stabilizer membership is
lifted back to the actual earlier tail stabilizer `H_{k_j}`, where the
chosen representative is known to be unique. -/
theorem WeakFactorForm.lemma4_step_of_not_doubled
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) (c : Fin n) (hc : c.val < rho)
    (x : A) (hx : x ∈ W.partition.valueCell c)
    (hnot : ¬ W.partition.IsHDoubledInCell
      (W.partition.tailPeriod c.val) c x) :
    (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset (c.val + 1))).card +
        (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.valueCell c)).card - 1 ≤
      (quotientLayer (W.partition.tailPeriod rho)
        (W.partition.tailSumset c.val)).card := by
  classical
  let H : AddSubgroup A := W.partition.tailPeriod rho
  let K : AddSubgroup A := W.partition.tailPeriod c.val
  let Bq : Finset (A ⧸ H) :=
    quotientLayer H (W.partition.tailSumset (c.val + 1))
  let Cq : Finset (A ⧸ H) :=
    quotientLayer H (W.partition.valueCell c)
  have hHK : H ≤ K :=
    W.partition.stabilizer_tailSumset_antitone (Nat.le_of_lt hc)
  have hperiodic : H ≤ AddAction.stabilizer A
      (W.partition.tailSumset c.val : Set A) := by
    simpa [K, Theorem21SetPartition.tailPeriod] using hHK
  have hsumQ : Bq + Cq =
      quotientLayer H (W.partition.tailSumset c.val) := by
    rw [add_comm]
    simpa [Bq, Cq] using
      (W.partition.quotientLayer_tailSumset_eq_add_succ H c).symm
  have hBq : Bq.Nonempty :=
    quotientLayer_nonempty H _ (W.partition.tailSumset_nonempty (c.val + 1))
  have hCq : Cq.Nonempty :=
    quotientLayer_nonempty H _ (W.partition.valueCells_nonempty
      (W.partition.valueCell c) (by
        simp [Theorem21SetPartition.valueCells]))
  have hxq : QuotientAddGroup.mk' H x ∈ Cq := by
    exact (mem_quotientLayer_iff H (W.partition.valueCell c) _).2
      ⟨x, hx, rfl⟩
  have hunique : ∀ qy ∈ Cq,
      qy - QuotientAddGroup.mk' H x ∈
        AddAction.stabilizer (A ⧸ H) ((Bq + Cq : Finset (A ⧸ H)) : Set (A ⧸ H)) →
      qy = QuotientAddGroup.mk' H x := by
    intro qy hqy hqstab
    obtain ⟨y, hy, hyq⟩ :=
      (mem_quotientLayer_iff H (W.partition.valueCell c) qy).1 hqy
    have hqstab' : QuotientAddGroup.mk' H y -
        QuotientAddGroup.mk' H x ∈
        AddAction.stabilizer (A ⧸ H)
          (quotientLayer H (W.partition.tailSumset c.val) : Set (A ⧸ H)) := by
      simpa [hyq, hsumQ]
        using hqstab
    have hystab : y - x ∈ AddAction.stabilizer A
        (W.partition.tailSumset c.val : Set A) :=
      sub_mem_stabilizer_of_quotient_sub_mem_stabilizer H
        (W.partition.tailSumset c.val) hperiodic hqstab'
    have hyK : QuotientAddGroup.mk' K y = QuotientAddGroup.mk' K x := by
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      simpa [K, Theorem21SetPartition.tailPeriod] using hystab
    have hyx : y = x := by
      by_contra hyx
      exact hnot ⟨hx, y, hy, hyx, hyK⟩
    subst y
    exact hyq.symm
  have hstep := card_add_sub_one_le_of_unique_addStab_fiber
    Bq Cq hBq hCq hxq hunique
  rw [hsumQ] at hstep
  simpa [H, Bq, Cq] using hstep

omit [Fintype A] in
/-- In the doubled branch at an earlier stage `j`, equality after deleting
the final-quotient class would make the erased literal `j`-tail periodic by
`H_{k_j}`.  The true prefix transition and Lemma 1 rule this out.  The key
lifting step is valid because the unchanged final tail already makes the
erased sumset `H_k`-periodic. -/
theorem WeakFactorForm.quotient_erase_ne_of_doubled_at_prefix
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    [DecidableEq (A ⧸ W.partition.tailPeriod rho)]
    (c : Fin n) (hc : c.val < rho) (x : A)
    (hexception : W.partition.IsHException
      (W.partition.tailPeriod c.val) x)
    (hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod c.val) c x)
    (hanchor : occurrenceValue xs (I.anchor c) ≠ x) :
    quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset (c.val + 1)) +
          quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c) ≠
        quotientLayer (W.partition.tailPeriod rho)
            (W.partition.tailSumset (c.val + 1)) +
          (quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c)).erase
              (QuotientAddGroup.mk'
                (W.partition.tailPeriod rho) x) := by
  classical
  intro heq
  let H : AddSubgroup A := W.partition.tailPeriod rho
  let K : AddSubgroup A := W.partition.tailPeriod c.val
  have hHK : H ≤ K :=
    W.partition.stabilizer_tailSumset_antitone (Nat.le_of_lt hc)
  obtain ⟨Wc, hWc⟩ := W.exists_prefix hc
  have hexception' : Wc.partition.IsHException
      (Wc.partition.tailPeriod c.val) x := by
    simpa [hWc] using hexception
  have hdouble' : Wc.partition.IsHDoubledInCell
      (Wc.partition.tailPeriod c.val) c x := by
    simpa [hWc] using hdouble
  have hanchor' : occurrenceValue xs (I.anchor c) ≠ x := hanchor
  have hnotK := Wc.lemma1_minTail_of_anchor_ne c x
    hexception' hdouble' hanchor'
  have hnotPeriodic : ¬ K ≤ AddAction.stabilizer A
      (W.partition.tailSumsetAfterErase c x c.val : Set A) := by
    simpa [hWc, K, Nat.min_self] using hnotK
  have hexFinal : W.partition.IsHException H x :=
    W.partition.isHException_of_le hHK hexception
  have hnotFinalDouble : ¬ W.partition.IsHDoubledInCell H c x := by
    intro hd
    obtain ⟨_z, _hzquot, _hzException, _hzDouble, _hzAnchor,
        hrhoc, _hzNotPeriodic⟩ :=
      W.exists_lemma1_representative c x hexFinal hd
    omega
  have huniqueH : ∀ y ∈ W.partition.valueCell c,
      QuotientAddGroup.mk' H y = QuotientAddGroup.mk' H x → y = x := by
    intro y hy hyq
    by_contra hyx
    exact hnotFinalDouble ⟨hdouble.1, y, hy, hyx, hyq⟩
  have hqerase : quotientLayer H
        (eraseValue (W.partition.valueCell c) x) =
      (quotientLayer H (W.partition.valueCell c)).erase
        (QuotientAddGroup.mk' H x) := by
    unfold eraseValue
    exact quotientLayer_erase_eq_erase_of_unique H
      (W.partition.valueCell c) huniqueH
  obtain ⟨_hx, y, hy, hyx, _hyquot⟩ := hdouble
  have hperiodicErased : H ≤ AddAction.stabilizer A
      (W.partition.tailSumsetAfterErase c x c.val : Set A) :=
    W.periodic_tailSumsetAfterErase_of_source_lt_of_duplicate
      c x y hy hyx hc
  have hperiodicFull : H ≤ AddAction.stabilizer A
      (W.partition.tailSumset c.val : Set A) := by
    simpa [K, Theorem21SetPartition.tailPeriod] using hHK
  have hqE : quotientLayer H
        (W.partition.tailSumsetAfterErase c x c.val) =
      quotientLayer H (W.partition.tailSumset c.val) := by
    calc
      quotientLayer H
          (W.partition.tailSumsetAfterErase c x c.val) =
          quotientLayer H (eraseValue (W.partition.valueCell c) x) +
            quotientLayer H (W.partition.tailSumset (c.val + 1)) := by
              rw [W.partition.tailSumsetAfterErase_eq_eraseValue_add_succ,
                quotientLayer_add]
      _ = (quotientLayer H (W.partition.valueCell c)).erase
            (QuotientAddGroup.mk' H x) +
          quotientLayer H (W.partition.tailSumset (c.val + 1)) := by
            rw [hqerase]
      _ = quotientLayer H (W.partition.tailSumset (c.val + 1)) +
          (quotientLayer H (W.partition.valueCell c)).erase
            (QuotientAddGroup.mk' H x) := by rw [add_comm]
      _ = quotientLayer H (W.partition.tailSumset (c.val + 1)) +
          quotientLayer H (W.partition.valueCell c) := by
            simpa [H] using heq.symm
      _ = quotientLayer H (W.partition.valueCell c) +
          quotientLayer H (W.partition.tailSumset (c.val + 1)) := by
            rw [add_comm]
      _ = quotientLayer H (W.partition.tailSumset c.val) :=
        (W.partition.quotientLayer_tailSumset_eq_add_succ H c).symm
  have hactualEq : W.partition.tailSumsetAfterErase c x c.val =
      W.partition.tailSumset c.val := by
    ext z
    rw [← mem_quotientLayer_iff_of_le_stabilizer H
      (W.partition.tailSumsetAfterErase c x c.val) hperiodicErased z]
    rw [hqE]
    exact mem_quotientLayer_iff_of_le_stabilizer H
      (W.partition.tailSumset c.val) hperiodicFull z
  apply hnotPeriodic
  rw [hactualEq]
  exact le_rfl

omit [Fintype A] in
/-- The Scherk branch of equation (3.4): if deleting the distinguished
`H_k` quotient value changes the projected pair sumset, Proposition 1.3
gives the required one-step inequality immediately. -/
theorem WeakFactorForm.lemma4_step_of_quotient_erase_ne
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    [DecidableEq (A ⧸ W.partition.tailPeriod rho)] (c : Fin n)
    (x : A) (hx : x ∈ W.partition.valueCell c)
    (hne :
      quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset (c.val + 1)) +
          quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c) ≠
        quotientLayer (W.partition.tailPeriod rho)
            (W.partition.tailSumset (c.val + 1)) +
          (quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c)).erase
              (QuotientAddGroup.mk'
                (W.partition.tailPeriod rho) x)) :
    (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset (c.val + 1))).card +
        (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.valueCell c)).card - 1 ≤
      (quotientLayer (W.partition.tailPeriod rho)
        (W.partition.tailSumset c.val)).card := by
  classical
  let H : AddSubgroup A := W.partition.tailPeriod rho
  let Bq : Finset (A ⧸ H) :=
    quotientLayer H (W.partition.tailSumset (c.val + 1))
  let Cq : Finset (A ⧸ H) :=
    quotientLayer H (W.partition.valueCell c)
  have hBq : Bq.Nonempty :=
    quotientLayer_nonempty H _ (W.partition.tailSumset_nonempty (c.val + 1))
  have hxq : QuotientAddGroup.mk' H x ∈ Cq :=
    (mem_quotientLayer_iff H (W.partition.valueCell c) _).2
      ⟨x, hx, rfl⟩
  have hstep := card_add_sub_one_le_of_add_ne_add_erase
    Bq Cq hBq hxq (by simpa [H, Bq, Cq] using hne)
  have hsumQ : Bq + Cq =
      quotientLayer H (W.partition.tailSumset c.val) := by
    rw [add_comm]
    simpa [Bq, Cq] using
      (W.partition.quotientLayer_tailSumset_eq_add_succ H c).symm
  rw [hsumQ] at hstep
  simpa [H, Bq, Cq] using hstep

/-- Complete one-cell equation (3.4) for every leading cell.  Condition (IV)
supplies an earlier-period exception.  The non-doubled case is Kneser in the
final quotient; the doubled case first chooses an anchor-safe representative,
uses the true prefix transition to rule out erase equality, and then invokes
Scherk's Proposition 1.3. -/
theorem WeakFactorForm.lemma4_step
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) (c : Fin n) (hc : c.val < rho) :
    (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset (c.val + 1))).card +
        (quotientLayer (W.partition.tailPeriod rho)
          (W.partition.valueCell c)).card - 1 ≤
      (quotientLayer (W.partition.tailPeriod rho)
        (W.partition.tailSumset c.val)).card := by
  classical
  obtain ⟨x, hx, hexception⟩ := W.leading_exception c hc
  by_cases hdouble : W.partition.IsHDoubledInCell
      (W.partition.tailPeriod c.val) c x
  · by_cases hanchor : occurrenceValue xs (I.anchor c) ≠ x
    · have hne := W.quotient_erase_ne_of_doubled_at_prefix
        c hc x hexception hdouble hanchor
      exact W.lemma4_step_of_quotient_erase_ne c x hx hne
    · have hanchorEq : occurrenceValue xs (I.anchor c) = x :=
        Classical.not_not.mp hanchor
      rcases hdouble with ⟨_hx, y, hy, hyx, hyquot⟩
      have hyException : W.partition.IsHException
          (W.partition.tailPeriod c.val) y := by
        rcases hexception with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        simpa [hyquot] using hd
      have hyDouble : W.partition.IsHDoubledInCell
          (W.partition.tailPeriod c.val) c y :=
        ⟨hy, x, hx, fun hxy ↦ hyx hxy.symm, hyquot.symm⟩
      have hyAnchor : occurrenceValue xs (I.anchor c) ≠ y := by
        rw [hanchorEq]
        exact fun hxy ↦ hyx hxy.symm
      have hne := W.quotient_erase_ne_of_doubled_at_prefix
        c hc y hyException hyDouble hyAnchor
      exact W.lemma4_step_of_quotient_erase_ne c y hy hne
  · exact W.lemma4_step_of_not_doubled c hc x hx hdouble

/-- Summed leading-cell holes estimate in dissertation Lemma 3. -/
theorem WeakFactorForm.leading_holes_le
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) :
    (∑ c ∈ leadingIndices n rho, (W.partition.valueCell c).card) +
        rho * (Nat.card (W.partition.tailPeriod rho) - 1) ≤
      Nat.card (W.partition.tailPeriod rho) *
        ∑ c ∈ leadingIndices n rho,
          (quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c)).card := by
  classical
  have hrhon : rho ≤ n := by
    have := W.range
    omega
  have hsum := Finset.sum_le_sum fun c
      (hc : c ∈ leadingIndices n rho) ↦ by
    have hc' : c.val < rho := by
      simpa [leadingIndices] using hc
    obtain ⟨x, hx, hunique⟩ :=
      W.exists_unique_tailPeriod_representative_of_leading c hc'
    exact card_add_natCard_sub_one_le_mul_quotientLayer_of_unique
      (W.partition.tailPeriod rho) (W.partition.valueCell c) hx hunique
  simpa [Finset.sum_add_distrib, card_leadingIndices hrhon,
    Finset.mul_sum] using hsum

/-- The source number `N = |commonCore| / |H|` is bounded by the number of
quotient classes represented by the common core. -/
theorem Theorem21SetPartition.commonCosetCount_le_card_quotientLayer_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    P.commonCosetCount H ≤ (quotientLayer H (P.commonCore H)).card := by
  unfold Theorem21SetPartition.commonCosetCount
  exact Nat.div_le_of_le_mul
    (card_le_natCard_mul_card_quotientLayer H (P.commonCore H))

/-- Every quotient class represented by the common core is represented in
each individual value cell. -/
theorem Theorem21SetPartition.quotientLayer_commonCore_subset_valueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    quotientLayer H (P.commonCore H) ⊆ quotientLayer H (P.valueCell c) := by
  classical
  intro q hq
  obtain ⟨x, hx, rfl⟩ :=
    (mem_quotientLayer_iff H (P.commonCore H) q).1 hq
  exact (P.mem_thickenedCell_iff_mem_quotientLayer H c x).1
    ((P.mem_commonCore_iff H x).1 hx c)

/-- Values of one cell lying outside the common `H`-saturation. -/
noncomputable def Theorem21SetPartition.outsideCoreValueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) : Finset A := by
  classical
  exact P.valueCell c \ P.commonCore H

/-- Outside-core quotient classes are disjoint from common-core quotient
classes. -/
theorem Theorem21SetPartition.disjoint_quotientLayer_commonCore_outside
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    Disjoint (quotientLayer H (P.commonCore H))
      (quotientLayer H (P.outsideCoreValueCell H c)) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqcore hqout
  obtain ⟨x, hxcore, hxq⟩ :=
    (mem_quotientLayer_iff H (P.commonCore H) q).1 hqcore
  obtain ⟨y, hyout, hyq⟩ :=
    (mem_quotientLayer_iff H (P.outsideCoreValueCell H c) q).1 hqout
  have hyx : y - x ∈ H := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp (hyq.trans hxq.symm)
  have hycore : y ∈ P.commonCore H := by
    apply (P.mem_commonCore_iff H y).2
    intro d
    apply (P.mem_thickenedCell_iff_mem_quotientLayer H d y).2
    have hxLayer := (P.mem_thickenedCell_iff_mem_quotientLayer H d x).1
      ((P.mem_commonCore_iff H x).1 hxcore d)
    simpa [hyq, hxq] using hxLayer
  exact (Finset.mem_sdiff.mp (by
    simpa [Theorem21SetPartition.outsideCoreValueCell] using hyout)).2 hycore

/-- With no doubled exceptions, one cell contributes at least `N + e_c`
distinct quotient classes: the common classes plus one distinct class for
each outside-core value. -/
theorem Theorem21SetPartition.commonCosetCount_add_cellExceptionDefect_le
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A)
    (hno : ∀ x : A, ¬ P.IsHDoubledException H x) (c : Fin n) :
    P.commonCosetCount H + P.cellExceptionDefect H c ≤
      (quotientLayer H (P.valueCell c)).card := by
  classical
  let coreQ := quotientLayer H (P.commonCore H)
  let outside := P.outsideCoreValueCell H c
  let outsideQ := quotientLayer H outside
  have hcoreLe : P.commonCosetCount H ≤ coreQ.card :=
    P.commonCosetCount_le_card_quotientLayer_commonCore H
  have houtCard : outsideQ.card = outside.card := by
    apply Finset.card_image_iff.mpr
    simpa [outside, Theorem21SetPartition.outsideCoreValueCell] using
      P.quotient_injOn_outside_commonCore H hno c
  have houtDefect : outside.card = P.cellExceptionDefect H c := by
    simp [outside, Theorem21SetPartition.outsideCoreValueCell,
      Theorem21SetPartition.cellExceptionDefect, Finset.card_sdiff,
      Finset.inter_comm]
  have hdisjoint : Disjoint coreQ outsideQ :=
    P.disjoint_quotientLayer_commonCore_outside H c
  have hunion : coreQ ∪ outsideQ ⊆ quotientLayer H (P.valueCell c) := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqcore | hqout
    · exact P.quotientLayer_commonCore_subset_valueCell H c hqcore
    · obtain ⟨x, hx, rfl⟩ :=
        (mem_quotientLayer_iff H outside _).1 hqout
      exact (mem_quotientLayer_iff H (P.valueCell c) _).2
        ⟨x, (Finset.mem_sdiff.mp hx).1, rfl⟩
  have hunionCard : coreQ.card + outsideQ.card = (coreQ ∪ outsideQ).card := by
    exact (Finset.card_union_of_disjoint hdisjoint).symm
  have hcardLe := Finset.card_le_card hunion
  rw [← hunionCard, houtCard, houtDefect] at hcardLe
  omega

/-- Summing the preceding cellwise estimate gives the exact Theorem E
incidence coefficient `N*n + e`. -/
theorem Theorem21SetPartition.commonCosetCount_mul_add_exceptionDefect_le_incidence
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A)
    (hno : ∀ x : A, ¬ P.IsHDoubledException H x) :
    P.commonCosetCount H * n + P.exceptionDefect H ≤
      P.quotientIncidenceAt H := by
  classical
  unfold Theorem21SetPartition.exceptionDefect
    Theorem21SetPartition.quotientIncidenceAt
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) ↦
    P.commonCosetCount_add_cellExceptionDefect_le H hno c
  rw [Finset.sum_add_distrib] at hsum
  simpa [Nat.mul_comm] using hsum

omit [Fintype A] in
/-- The arbitrary-subgroup incidence definition agrees, at the actual
sumset stabilizer, with the specialized quotient-incidence expression used
by the proved full-layer DGM theorem. -/
theorem Theorem21SetPartition.quotientIncidenceAt_stabilizer_eq
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.quotientIncidenceAt
        (AddAction.stabilizer A (P.sumset : Set A)) =
      P.stabilizerQuotientIncidence := by
  classical
  unfold Theorem21SetPartition.quotientIncidenceAt
    Theorem21SetPartition.stabilizerQuotientIncidence
  apply Finset.sum_congr rfl
  intro c _
  apply congrArg Finset.card
  ext q
  simp [quotientLayer, stabilizerQuotientLayer]

omit [Fintype A] in
/-- Nonempty cells make the full replacement sumset nonempty; this local
version is placed next to the DGM bridge so it does not rely on later
Theorem-2.1 case analysis. -/
theorem Theorem21SetPartition.sumset_nonempty_for_dgm
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.sumset.Nonempty := by
  classical
  unfold Theorem21SetPartition.sumset fullLayerSumSpectrum
  exact layerSubsumSpectrum_nonempty P.valueCells P.valueCells_nonempty
    P.valueCells.length le_rfl

/-- Full-layer DGM converts elimination of doubled exceptions into the exact
corrected Theorem E numerical bound.  This theorem discharges the entire
`N/e` cardinality calculation; it does not assert that the extremal chain has
already eliminated the exceptions. -/
theorem Theorem21SetPartition.theoremE_card_lower_of_no_doubled
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (hno : ∀ x : A, ¬ P.IsHDoubledException
      (AddAction.stabilizer A (P.sumset : Set A)) x) :
    ((P.commonCosetCount
          (AddAction.stabilizer A (P.sumset : Set A)) * n +
        P.exceptionDefect
          (AddAction.stabilizer A (P.sumset : Set A)) + 1) - n) *
      Nat.card (AddAction.stabilizer A (P.sumset : Set A)) ≤
        P.sumset.card := by
  classical
  let H : AddSubgroup A := AddAction.stabilizer A (P.sumset : Set A)
  have hincLower :=
    P.commonCosetCount_mul_add_exceptionDefect_le_incidence H hno
  have hincEq : P.quotientIncidenceAt H =
      P.stabilizerQuotientIncidence := by
    simpa [H] using P.quotientIncidenceAt_stabilizer_eq
  have hincPos : n ≤ P.quotientIncidenceAt H := by
    have hlen := length_le_sum_quotientLayer_card H P.valueCells
      P.valueCells_nonempty
    rw [P.length_valueCells] at hlen
    simp only [Theorem21SetPartition.valueCells, List.map_ofFn,
      List.sum_ofFn] at hlen
    exact hlen
  have hdgm := fullLayer_dgm_lower_bound P.valueCells P.valueCells_nonempty
  have hstabCard := card_addStab_eq_natCard_stabilizer
    P.sumset P.sumset_nonempty_for_dgm
  have hstabCardH : P.sumset.addStab.card = Nat.card H := by
    simpa [H] using hstabCard
  have hspec :
      (P.valueCells.map fun B ↦
        (stabilizerQuotientLayer P.sumset B).card).sum =
        P.stabilizerQuotientIncidence := by
    unfold Theorem21SetPartition.valueCells
      Theorem21SetPartition.stabilizerQuotientIncidence
    simp only [List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro c _
    rfl
  have hdgm' :
      (P.quotientIncidenceAt H - n + 1) * Nat.card H ≤
        P.sumset.card := by
    change
      ((P.valueCells.map fun B ↦
          (stabilizerQuotientLayer P.sumset B).card).sum -
          P.valueCells.length + 1) * P.sumset.addStab.card ≤
        P.sumset.card at hdgm
    rw [hspec, P.length_valueCells, hstabCardH] at hdgm
    rw [hincEq]
    exact hdgm
  have hcoeff :
      (P.commonCosetCount H * n + P.exceptionDefect H + 1) - n ≤
        P.quotientIncidenceAt H - n + 1 := by
    omega
  simpa [H] using
    (Nat.mul_le_mul_right (Nat.card H) hcoeff).trans hdgm'

/-- Factor-form version of the Theorem E numerical bound.  The tail is
quotiented by its *actual* stabilizer, so full-layer DGM gives the aperiodic
tail estimate.  Condition (II) then attaches the leading quotient layers.
Only after this Kneser/DGM step is the no-doubled hypothesis used, to replace
quotient incidence by the faithful `N*n+e` coefficient. -/
theorem FactorForm.theoremE_card_lower_of_no_doubled
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n} (F : FactorForm I rho)
    (hno : ∀ x : A, ¬ F.partition.IsHDoubledException
      (F.partition.tailPeriod rho) x) :
    ((F.partition.commonCosetCount (F.partition.tailPeriod rho) * n +
          F.partition.exceptionDefect (F.partition.tailPeriod rho) + 1) -
          n) * Nat.card (F.partition.tailPeriod rho) ≤
      F.partition.sumset.card := by
  classical
  let H : AddSubgroup A := F.partition.tailPeriod rho
  let qTail : ℕ :=
    (quotientLayer H (F.partition.tailSumset rho)).card
  let qLead : ℕ :=
    ∑ c ∈ leadingIndices n rho,
      (quotientLayer H (F.partition.valueCell c)).card
  let qTailInc : ℕ :=
    ∑ c ∈ tailIndices n rho,
      (quotientLayer H (F.partition.valueCell c)).card
  let qFull : ℕ := (quotientLayer H F.partition.sumset).card
  have htailNonempty : IsNonemptySetPartition
      (F.partition.tailValueCells rho) := by
    simpa [Theorem21SetPartition.tailValueCells] using
      F.partition.valueCells_nonempty.drop rho
  have hdgm := fullLayer_dgm_lower_bound
    (F.partition.tailValueCells rho) htailNonempty
  change
    (((F.partition.tailValueCells rho).map fun B ↦
          (stabilizerQuotientLayer (F.partition.tailSumset rho) B).card).sum -
        (F.partition.tailValueCells rho).length + 1) *
        (F.partition.tailSumset rho).addStab.card ≤
      (F.partition.tailSumset rho).card at hdgm
  simp_rw [← quotientLayer_eq_stabilizerQuotientLayer
    (F.partition.tailSumset rho)] at hdgm
  have hstabCard : (F.partition.tailSumset rho).addStab.card =
      Nat.card H := by
    have h := card_addStab_eq_natCard_stabilizer
      (F.partition.tailSumset rho)
      (F.partition.tailSumset_nonempty rho)
    simpa [H, Theorem21SetPartition.tailPeriod] using h
  have htailCard : (F.partition.tailSumset rho).card =
      Nat.card H * qTail := by
    apply card_eq_natCard_mul_card_quotientLayer_of_le_stabilizer
    simp [H, Theorem21SetPartition.tailPeriod]
  have htailLength : (F.partition.tailValueCells rho).length = n - rho := by
    simp [Theorem21SetPartition.tailValueCells,
      F.partition.length_valueCells]
  have htailIncidence :
      ((F.partition.tailValueCells rho).map fun B ↦
        (quotientLayer H B).card).sum = qTailInc := by
    simpa [qTailInc] using
      F.partition.sum_card_quotientLayer_tailValueCells_eq_tailIndices
        (rho := rho) H
  have hHactual : AddAction.stabilizer A
      (F.partition.tailSumset rho : Set A) = H := by
    simp [H, Theorem21SetPartition.tailPeriod]
  rw [hHactual] at hdgm
  rw [hstabCard, htailCard, htailLength, htailIncidence] at hdgm
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have htailBound : qTailInc - (n - rho) + 1 ≤ qTail := by
    have hdgm' : Nat.card H * (qTailInc - (n - rho) + 1) ≤
        Nat.card H * qTail := by
      simpa [Nat.mul_comm] using hdgm
    exact Nat.le_of_mul_le_mul_left hdgm' hHpos
  have hrange : rho ≤ n := by
    have := F.range
    omega
  have htailGuard : n - rho ≤ qTailInc := by
    have hlen := length_le_sum_quotientLayer_card H
      (F.partition.tailValueCells rho) htailNonempty
    rw [htailLength, htailIncidence] at hlen
    exact hlen
  have hbase : rho + 1 ≤ qTail + qLead := by
    simpa [H, qTail, qLead] using
      F.toWeakFactorForm.quotient_growth_base_le
  have hII : qTail + qLead - (rho + 1) + 1 ≤ qFull := by
    simpa [H, qTail, qLead, qFull] using F.quotient_growth
  have hsplit : qLead + qTailInc =
      F.partition.quotientIncidenceAt H := by
    have hs := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin n)) (fun c : Fin n ↦ c.val < rho)
      (fun c : Fin n ↦ (quotientLayer H
        (F.partition.valueCell c)).card)
    simpa [qLead, qTailInc, leadingIndices, tailIndices, not_lt,
      Theorem21SetPartition.quotientIncidenceAt] using hs
  have hincGuard : n ≤ F.partition.quotientIncidenceAt H := by
    have hleadGuard : rho ≤ qLead := by
      rw [← card_leadingIndices hrange]
      calc
        (leadingIndices n rho).card =
            ∑ c ∈ leadingIndices n rho, 1 := by simp
        _ ≤ qLead := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.card_pos.mpr
            (quotientLayer_nonempty H _
              (F.partition.valueCells_nonempty
                (F.partition.valueCell c) (by
                  simp [Theorem21SetPartition.valueCells])))
    omega
  have hquotientFull :
      F.partition.quotientIncidenceAt H - n + 1 ≤ qFull := by
    omega
  have hincLower :
      F.partition.commonCosetCount H * n +
          F.partition.exceptionDefect H ≤
        F.partition.quotientIncidenceAt H :=
    F.partition.commonCosetCount_mul_add_exceptionDefect_le_incidence H hno
  have hcoeff :
      (F.partition.commonCosetCount H * n +
          F.partition.exceptionDefect H + 1) - n ≤ qFull := by
    omega
  have hfullPeriodic : H ≤ AddAction.stabilizer A
      (F.partition.sumset : Set A) := by
    simpa [H] using F.toWeakFactorForm.tailPeriod_le_sumset_stabilizer
  have hfullCard : F.partition.sumset.card = Nat.card H * qFull := by
    exact card_eq_natCard_mul_card_quotientLayer_of_le_stabilizer
      H F.partition.sumset hfullPeriodic
  simpa [H, hfullCard, Nat.mul_comm] using
    Nat.mul_le_mul_right (Nat.card H) hcoeff

/-- Regression for the placement of natural subtraction in Theorem E.

The source coefficient is `(N * n + e + 1) - n`.  Subtracting one from `N`
first is not equivalent over `Nat`: at `N = 0`, `n = 2`, `e = 2`, the faithful
coefficient is `1`, whereas the prematurely truncated expression is `3`. -/
theorem theoremE_natSub_regression :
    (((0 : ℕ) * 2 + 2 + 1) - 2 = 1) ∧
      ((0 - 1) * 2 + 2 + 1 = 3) := by
  norm_num

/-- A downstream projection of Theorem E used by the older assembly lemmas.
It forgets the source base-family admissibility and weakens actual stabilizer
equality to a subperiod.  Consequently it must not be used as the exact
source statement; `GMOTheoremESourceOutput` below retains those data. -/
structure GMOTheoremEOutput
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  partition : Theorem21SetPartition xs n seed.card
  H : AddSubgroup A
  periodic : H ≤ AddAction.stabilizer A (partition.sumset : Set A)
  card_lower :
    ((partition.commonCosetCount H * n +
        partition.exceptionDefect H + 1) - n) * Nat.card H ≤
      partition.sumset.card
  unused_in_core : H ≠ ⊥ →
    ∀ i : Occurrence xs, i ∉ partition.support →
      occurrenceValue xs i ∈ partition.commonCore H

/-- Source-faithful Theorem E output relative to its literal initial
setpartition and anchors.  As in the source statement, `H` is a period of
the resulting sumset; it is not falsely required to be the full stabilizer.
When `H` is nontrivial, every unused labelled source occurrence lies in the
common core.  No unconditional `N ≥ 1` or global no-doubled conclusion is
built into this structure. -/
structure GMOTheoremESourceOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) where
  partition : Theorem21SetPartition xs n seed.card
  H : AddSubgroup A
  periodic : H ≤ AddAction.stabilizer A (partition.sumset : Set A)
  admissible : GMOReplacementAdmissible I partition
  card_lower :
    ((partition.commonCosetCount H * n +
        partition.exceptionDefect H + 1) - n) * Nat.card H ≤
      partition.sumset.card
  unused_mem_commonCore :
    H ≠ ⊥ → ∀ i : Occurrence xs, i ∉ partition.support →
      occurrenceValue xs i ∈ partition.commonCore H

/-- Simultaneously relabel every cell of a literal Theorem E output and its
source input.  All numerical data are invariant because both the common
intersection and the sum over cell defects are symmetric in the cells. -/
noncomputable def GMOTheoremESourceOutput.reindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (sigma : Equiv.Perm (Fin n)) :
    GMOTheoremESourceOutput (I.reindex sigma) := by
  classical
  refine {
    partition := out.partition.reindex sigma
    H := out.H
    periodic := ?_
    admissible := out.admissible.reindex sigma
    card_lower := ?_
    unused_mem_commonCore := ?_
  }
  · rw [out.partition.sumset_reindex sigma]
    exact out.periodic
  · simpa only [Theorem21SetPartition.commonCosetCount_reindex,
      Theorem21SetPartition.exceptionDefect_reindex,
      Theorem21SetPartition.sumset_reindex] using out.card_lower
  · intro hH i hi
    have hi' : i ∉ out.partition.support := by
      simpa only [out.partition.support_reindex sigma] using hi
    simpa only [out.partition.commonCore_reindex sigma out.H] using
      out.unused_mem_commonCore hH i hi'

/-- Undo a simultaneous cell reindexing of a source Theorem E output.  This
is the final descent needed after Lemma 5's WLOG tail permutation. -/
noncomputable def GMOTheoremESourceOutput.inverseReindex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (sigma : Equiv.Perm (Fin n))
    (out : GMOTheoremESourceOutput (I.reindex sigma)) :
    GMOTheoremESourceOutput I := by
  have temp := out.reindex sigma.symm
  simpa using temp

/-- The scalar trivial-period conclusion used as the contradiction target in
dissertation Lemma 3: an admissible replacement satisfying the ordinary
Cauchy--Davenport bound.  It is deliberately separate from an
actual-stabilizer normalization, since the trivial subgroup can be a strict
subperiod of the sumset. -/
structure GMOTheoremETrivialConclusion
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) where
  partition : Theorem21SetPartition xs n seed.card
  admissible : GMOReplacementAdmissible I partition
  card_lower : seed.card - n + 1 ≤ partition.sumset.card

/-- Under failure of the full source Theorem E output, any factor partition
that already has the required numerical bound must leave an unused labelled
occurrence outside its common core.  This is the exact logical step used in
the no-doubled branch of dissertation Lemma 5; failure of only the scalar
trivial conclusion would not suffice. -/
theorem FactorForm.exists_unused_outside_commonCore_of_no_sourceOutput
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I))
    (hcard :
      ((F.partition.commonCosetCount (F.partition.tailPeriod rho) * n +
          F.partition.exceptionDefect (F.partition.tailPeriod rho) + 1) -
          n) * Nat.card (F.partition.tailPeriod rho) ≤
        F.partition.sumset.card) :
    ∃ i : Occurrence xs,
      i ∉ F.partition.support ∧
        occurrenceValue xs i ∉
          F.partition.commonCore (F.partition.tailPeriod rho) := by
  classical
  by_contra hnone
  have hall : ∀ i : Occurrence xs, i ∉ F.partition.support →
      occurrenceValue xs i ∈
        F.partition.commonCore (F.partition.tailPeriod rho) := by
    intro i hi
    by_contra hout
    exact hnone ⟨i, hi, hout⟩
  apply hfail
  exact ⟨{
    partition := F.partition
    H := F.partition.tailPeriod rho
    periodic := F.toWeakFactorForm.tailPeriod_le_sumset_stabilizer
    admissible := F.admissible
    card_lower := hcard
    unused_mem_commonCore := fun _ i hi ↦ hall i hi
  }⟩

/-- The complete no-doubled-side replacement contradiction in dissertation
Lemma 5, isolated from the numerical derivation of the Theorem E bound.  If
that bound already holds but the source output is assumed not to exist, an
unused occurrence outside the common core enters a missing cell.  The local
Scherk step supplies an anchor-safe used occurrence whose quotient class
survives deletion.  Both the distinct-cell and same-cell cases are handled,
so no illicit `q ≠ d` assumption is made. -/
theorem FactorForm.false_of_card_lower_of_no_sourceOutput
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I))
    (hcard :
      ((F.partition.commonCosetCount (F.partition.tailPeriod rho) * n +
          F.partition.exceptionDefect (F.partition.tailPeriod rho) + 1) -
          n) * Nat.card (F.partition.tailPeriod rho) ≤
        F.partition.sumset.card) : False := by
  classical
  obtain ⟨x, hxUnused, hxOutside⟩ :=
    F.exists_unused_outside_commonCore_of_no_sourceOutput hfail hcard
  have hxException : F.partition.IsHException
      (F.partition.tailPeriod rho) (occurrenceValue xs x) :=
    (F.partition.isHException_iff_not_mem_commonCore
      (F.partition.tailPeriod rho) (occurrenceValue xs x)).2 hxOutside
  obtain ⟨d, hmissing⟩ := hxException
  obtain ⟨q, y, hrhoq, _hqLast, hyq, hyAnchor, hduplicate, herase⟩ :=
    F.exists_anchorSafe_local_tail_replacement
  have hsource : ∃ j ∈ F.partition.cells q, j ≠ y := by
    obtain ⟨z, hz, hzy, _hzquot⟩ := hduplicate
    have hzImage := hz
    unfold Theorem21SetPartition.valueCell at hzImage
    obtain ⟨j, hjq, hjValue⟩ := Finset.mem_image.mp hzImage
    refine ⟨j, hjq, ?_⟩
    intro hjy
    apply hzy
    rw [← hjValue, hjy]
  have htarget : ∀ j ∈ F.partition.cells d,
      occurrenceValue xs j ≠ occurrenceValue xs x := by
    intro j hj hvalue
    apply hmissing
    apply (mem_quotientLayer_iff (F.partition.tailPeriod rho)
      (F.partition.valueCell d) _).2
    refine ⟨occurrenceValue xs j, ?_, ?_⟩
    · unfold Theorem21SetPartition.valueCell
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    · simp [hvalue]
  by_cases hqd : q = d
  · subst d
    have hvalue : ∀ j ∈ F.partition.cells q, j ≠ y →
        occurrenceValue xs j ≠ occurrenceValue xs x := by
      intro j hj _
      exact htarget j hj
    obtain ⟨Q, hQcells, _hQsupport⟩ :=
      F.partition.exists_replaceUsedWithUnusedSameCell hyq hxUnused hvalue
    have htailZero : F.partition.tailSumset 0 ⊆ Q.tailSumset 0 :=
      F.partition.tailSumset_subset_replaceSameCell_of_erase_eq
        hyq hQcells 0 (herase 0 (Nat.zero_le rho))
    have hsum : F.partition.sumset ⊆ Q.sumset := by
      simpa [Theorem21SetPartition.tailSumset,
        Theorem21SetPartition.tailValueCells,
        Theorem21SetPartition.sumset] using htailZero
    have hanchorMem : occurrenceValue xs (I.anchor q) ∈
        insertValue (occurrenceValue xs x)
          (eraseValue (F.partition.valueCell q) (occurrenceValue xs y)) := by
      unfold insertValue eraseValue
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hyAnchor.symm, F.admissible.2 q⟩)
    have hQadmissible : GMOReplacementAdmissible I Q :=
      F.admissible.replaceUsedWithUnusedSameCell hyq hanchorMem hQcells hsum
    have hmono : Definition1SourceChain.MonotoneReplacement
        F.partition Q F.chain :=
      Definition1SourceChain.MonotoneReplacement.of_replaceSameCell_of_erase_eq
        F.inLambda.1 le_rfl hQadmissible hyq hduplicate hQcells herase
    have htailRho : F.partition.tailSumset rho ⊆ Q.tailSumset rho :=
      F.partition.tailSumset_subset_replaceSameCell_of_erase_eq
        hyq hQcells rho (herase rho le_rfl)
    have hinc : Q.quotientIncidenceAt (F.partition.tailPeriod rho) =
        F.partition.quotientIncidenceAt (F.partition.tailPeriod rho) + 1 :=
      F.partition.quotientIncidenceAt_replaceSameCell_eq_add_one
        (F.partition.tailPeriod rho) hyq hduplicate hmissing hQcells
    exact F.toWeakFactorForm.not_incidence_add_one_of_sourceMonotone
      Q hmono htailRho hinc
  · have hqd' : q ≠ d := hqd
    obtain ⟨Q, hQcells, _hQsupport⟩ :=
      F.partition.exists_replaceUsedWithUnused hqd' hyq hsource hxUnused htarget
    have htailZero : F.partition.tailSumset 0 ⊆ Q.tailSumset 0 :=
      F.partition.tailSumset_subset_replaceUsedWithUnused_of_erase_eq
        hqd' hyq hQcells 0 (herase 0 (Nat.zero_le rho))
    have hsum : F.partition.sumset ⊆ Q.sumset := by
      simpa [Theorem21SetPartition.tailSumset,
        Theorem21SetPartition.tailValueCells,
        Theorem21SetPartition.sumset] using htailZero
    have hQadmissible : GMOReplacementAdmissible I Q :=
      F.admissible.replaceUsedWithUnused hqd' hyq hyAnchor.symm hQcells hsum
    have hmono : Definition1SourceChain.MonotoneReplacement
        F.partition Q F.chain :=
      Definition1SourceChain.MonotoneReplacement.of_replaceUsedWithUnused_of_erase_eq
        F.inLambda.1 le_rfl hQadmissible hqd' hyq hduplicate hQcells herase
    have htailRho : F.partition.tailSumset rho ⊆ Q.tailSumset rho :=
      F.partition.tailSumset_subset_replaceUsedWithUnused_of_erase_eq
        hqd' hyq hQcells rho (herase rho le_rfl)
    have hinc : Q.quotientIncidenceAt (F.partition.tailPeriod rho) =
        F.partition.quotientIncidenceAt (F.partition.tailPeriod rho) + 1 :=
      F.partition.quotientIncidenceAt_replace_eq_add_one
        (F.partition.tailPeriod rho) hqd' hyq hduplicate hmissing hQcells
    exact F.toWeakFactorForm.not_incidence_add_one_of_sourceMonotone
      Q hmono htailRho hinc

/-- No-doubled branch of dissertation Lemma 5.  Under failure of the full
source Theorem E conclusion, every factor form must contain a doubled
exception modulo its final tail period.  The proof combines the exact
factor-form `N/e` bound with the honest unused-occurrence replacement
contradiction above. -/
theorem FactorForm.exists_doubledException_of_no_sourceOutput
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) :
    ∃ x : A, F.partition.IsHDoubledException
      (F.partition.tailPeriod rho) x := by
  by_contra hnone
  have hno : ∀ x : A, ¬ F.partition.IsHDoubledException
      (F.partition.tailPeriod rho) x := by
    simpa only [not_exists] using hnone
  exact F.false_of_card_lower_of_no_sourceOutput hfail
    (F.theoremE_card_lower_of_no_doubled hno)

/-- The WLOG/reselection core of the doubled branch in dissertation Lemma 5.
Starting from a genuine doubled exception, its cell is swapped into position
`rho` together with the source anchors and the entire prefix chain.  A fresh
`Lambda_{rho+1}` transition is then constructed and recentered at the
reindexed factor partition itself; the old `W.next` is never reused. -/
theorem FactorForm.exists_reindexed_recentered_doubled
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) :
    ∃ (sigma : Equiv.Perm (Fin n))
      (_hfix : PrefixFixed sigma rho)
      (W : WeakFactorForm (I.reindex sigma) rho)
      (x : A),
      W.F = W.partition ∧
      W.partition = F.partition.reindex sigma ∧
      W.partition.IsHException (W.partition.tailPeriod rho) x ∧
      W.partition.IsHDoubledInCell (W.partition.tailPeriod rho)
        ⟨rho, by have := F.range; omega⟩ x := by
  classical
  obtain ⟨x, hxException, q, hxDouble⟩ :=
    F.exists_doubledException_of_no_sourceOutput hfail
  obtain ⟨z, _hzquot, hzException, hzDouble, _hzAnchor,
      hrhoq, _hzNotPeriodic⟩ :=
    F.toWeakFactorForm.exists_lemma1_representative q x
      hxException hxDouble
  have hrhon : rho < n := by
    have := F.range
    omega
  obtain ⟨sigma, hfix, hsigmaRho⟩ :=
    exists_prefixFixed_swap_to_rho q hrhoq hrhon
  let I' := I.reindex sigma
  let P' := F.partition.reindex sigma
  let previous' := F.previous.reindex sigma
  have chain' : Definition1SourceChain I' rho previous' := by
    simpa only [I', previous'] using F.chain.reindex sigma hfix
  obtain ⟨next0, F0, step0⟩ :=
    exists_definition1Transition rho previous'
  have hPprevious : P' ∈ previous'.upsilon := by
    simpa only [P', previous'] using
      (F.previous.mem_reindex_iff sigma F.partition).2 F.inLambda.1
  have hPtail : P'.tailSumset rho = previous'.chosen.tailSumset rho := by
    calc
      P'.tailSumset rho = F.partition.tailSumset rho := by
        simpa only [P'] using
          F.partition.tailSumset_reindex sigma hfix
      _ = F.previous.chosen.tailSumset rho := F.inLambda.2.1
      _ = previous'.chosen.tailSumset rho := by
        have h := F.previous.chosen.tailSumset_reindex sigma hfix
        simpa only [previous', Definition1ExtremalState.reindex] using h.symm
  let Q := F0.reindex sigma.symm
  have hQprevious : Q ∈ F.previous.upsilon := by
    have hpre :=
      (F.previous.mem_reindex_iff_preimage sigma F0).1 step0.F_mem_previous
    simpa only [Q] using hpre
  have hfixSymm : PrefixFixed sigma.symm rho := hfix.symm
  have hQtailF0 : Q.tailSumset rho = F0.tailSumset rho := by
    simpa only [Q] using F0.tailSumset_reindex sigma.symm hfixSymm
  have hPreviousTail : previous'.chosen.tailSumset rho =
      F.previous.chosen.tailSumset rho := by
    simpa only [previous', Definition1ExtremalState.reindex] using
      F.previous.chosen.tailSumset_reindex sigma hfix
  have hQtail : Q.tailSumset rho =
      F.previous.chosen.tailSumset rho :=
    hQtailF0.trans (step0.F_tail_fixed.trans hPreviousTail)
  have hOldMax := F.transition.incidence_maximal Q hQprevious hQtail
  have hH : AddAction.stabilizer A
        (previous'.chosen.tailSumset rho : Set A) =
      AddAction.stabilizer A
        (F.previous.chosen.tailSumset rho : Set A) := by
    rw [hPreviousTail]
  have hP_le := step0.incidence_maximal P' hPprevious hPtail
  have hF0_le : F0.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous'.chosen.tailSumset rho : Set A)) ≤
      P'.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous'.chosen.tailSumset rho : Set A)) := by
    rw [hH]
    have hOldMax' := hOldMax.trans_eq F.inLambda.2.2.symm
    simpa only [Q, P',
      Theorem21SetPartition.quotientIncidenceAt_reindex] using hOldMax'
  have hPinc : P'.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous'.chosen.tailSumset rho : Set A)) =
      F0.quotientIncidenceAt
        (AddAction.stabilizer A
          (previous'.chosen.tailSumset rho : Set A)) :=
    Nat.le_antisymm hP_le hF0_le
  have hPinLambda0 : step0.InLambda P' :=
    ⟨hPprevious, hPtail, hPinc⟩
  obtain ⟨nextP, stepP⟩ := step0.exists_recentered hPinLambda0
  have hPinLambdaP : stepP.InLambda P' :=
    ⟨hPprevious, hPtail, rfl⟩
  let W : WeakFactorForm I' rho := {
    range := F.range
    partition := P'
    admissible := by
      simpa only [I', P'] using F.admissible.reindex sigma
    previous := previous'
    chain := chain'
    next := nextP
    F := P'
    transition := stepP
    partition_inLambda := hPinLambdaP
    tail_actual := by
      intro s hs
      have hfixs : PrefixFixed sigma s := by
        intro c hc
        exact hfix c (hc.trans_le hs)
      have hperiod : P'.tailPeriod s = F.partition.tailPeriod s := by
        simpa only [P'] using F.partition.tailPeriod_reindex sigma hfixs
      rw [hperiod]
      exact F.tail_actual s hs
    leading_exception := by
      intro c hc
      obtain ⟨y, hy, hyException⟩ := F.leading_exception c hc
      have hsigmac : sigma c = c := hfix c hc
      have hfixc : PrefixFixed sigma c.val := by
        intro d hd
        exact hfix d (hd.trans hc)
      have hperiod : P'.tailPeriod c.val =
          F.partition.tailPeriod c.val := by
        simpa only [P'] using F.partition.tailPeriod_reindex sigma hfixc
      refine ⟨y, ?_, ?_⟩
      · simpa only [P', Theorem21SetPartition.valueCell_reindex,
          hsigmac] using hy
      · rw [hperiod]
        exact (F.partition.isHException_reindex_iff sigma _ y).2
          hyException
  }
  have hperiodRho : P'.tailPeriod rho =
      F.partition.tailPeriod rho := by
    simpa only [P'] using F.partition.tailPeriod_reindex sigma hfix
  have hzException' : P'.IsHException (P'.tailPeriod rho) z := by
    rw [hperiodRho]
    exact (F.partition.isHException_reindex_iff sigma _ z).2 hzException
  have hzDouble' : P'.IsHDoubledInCell (P'.tailPeriod rho)
      ⟨rho, hrhon⟩ z := by
    rw [hperiodRho]
    have htransport :=
      (F.partition.isHDoubledInCell_reindex_iff sigma
        (F.partition.tailPeriod rho) ⟨rho, hrhon⟩ z).2
    exact htransport (by simpa only [hsigmaRho] using hzDouble)
  refine ⟨sigma, hfix, W, z, rfl, rfl, ?_, ?_⟩
  · exact hzException'
  · exact hzDouble'

omit [Fintype A] in
/-- Cellwise quotient inclusion plus equality of total quotient incidence
forces equality in every cell.  This is the finite counting step hidden in
the source phrase “from the definitions of Lambda and Upsilon”. -/
theorem Theorem21SetPartition.quotientLayer_eq_of_imagesIncluded_of_incidence_eq
    {xs : List A} {n m : ℕ}
    (F P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (hsub : F.quotientImagesIncluded P H)
    (hinc : P.quotientIncidenceAt H = F.quotientIncidenceAt H) :
    ∀ c : Fin n,
      quotientLayer H (P.valueCell c) =
        quotientLayer H (F.valueCell c) := by
  classical
  have hle (c : Fin n) :
      (quotientLayer H (F.valueCell c)).card ≤
        (quotientLayer H (P.valueCell c)).card :=
    Finset.card_le_card (hsub c)
  have hsum :
      (∑ c : Fin n, (quotientLayer H (F.valueCell c)).card) =
        ∑ c : Fin n, (quotientLayer H (P.valueCell c)).card := by
    simpa only [Theorem21SetPartition.quotientIncidenceAt] using hinc.symm
  have hcard (c : Fin n) :
      (quotientLayer H (F.valueCell c)).card =
        (quotientLayer H (P.valueCell c)).card :=
    (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (Fin n)))
      (fun c _ ↦ hle c)).1 hsum c (Finset.mem_univ c)
  intro c
  exact (Finset.eq_of_subset_of_card_le (hsub c) (by
    rw [hcard c])).symm

omit [Fintype A] in
/-- In a recentered Definition 1 stage, every member of the newly selected
`Upsilon_{rho+1}` has exactly the same quotient image in every indexed cell
as the current factor partition. -/
theorem WeakFactorForm.quotientLayer_eq_of_mem_next_of_recentered
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) (hF : W.F = W.partition)
    (P : Theorem21SetPartition xs n seed.card)
    (hP : P ∈ W.next.upsilon) (c : Fin n) :
    quotientLayer (W.partition.tailPeriod rho) (P.valueCell c) =
      quotientLayer (W.partition.tailPeriod rho)
        (W.partition.valueCell c) := by
  classical
  have hdata := (W.transition.mem_next_upsilon_iff P).1 hP
  have hH : W.partition.tailPeriod rho =
      AddAction.stabilizer A
        (W.previous.chosen.tailSumset rho : Set A) := by
    unfold Theorem21SetPartition.tailPeriod
    rw [W.inLambda.2.1]
  have hsub : W.partition.quotientImagesIncluded P
      (AddAction.stabilizer A
        (W.previous.chosen.tailSumset rho : Set A)) := by
    rw [← hF]
    exact hdata.2.2.2.1
  have hinc : P.quotientIncidenceAt
        (AddAction.stabilizer A
          (W.previous.chosen.tailSumset rho : Set A)) =
      W.partition.quotientIncidenceAt
        (AddAction.stabilizer A
          (W.previous.chosen.tailSumset rho : Set A)) := by
    rw [← hF]
    exact hdata.2.2.1
  rw [hH]
  exact W.partition.quotientLayer_eq_of_imagesIncluded_of_incidence_eq
    P _ hsub hinc c

omit [Fintype A] in
/-- Consequently, every exception of the recentered factor partition stays
an exception in every member of the new `Upsilon` family. -/
theorem WeakFactorForm.isHException_of_mem_next_of_recentered
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) (hF : W.F = W.partition)
    (P : Theorem21SetPartition xs n seed.card)
    (hP : P ∈ W.next.upsilon) (x : A)
    (hx : W.partition.IsHException (W.partition.tailPeriod rho) x) :
    P.IsHException (W.partition.tailPeriod rho) x := by
  classical
  obtain ⟨d, hd⟩ := hx
  refine ⟨d, ?_⟩
  rw [W.quotientLayer_eq_of_mem_next_of_recentered hF P hP d]
  exact hd

omit [Fintype A] in
/-- Every member of a source-chain extremal family remains in the literal
initial admissible family. -/
theorem Definition1SourceChain.admissible_of_mem
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (chain : Definition1SourceChain I r state)
    (P : Theorem21SetPartition xs n seed.card)
    (hP : P ∈ state.upsilon) : GMOReplacementAdmissible I P := by
  induction chain with
  | initial state valid =>
      exact ((valid.mem_upsilon_iff P).1 hP).1
  | @next r previous prior state F step ih =>
      exact ih (((step.mem_next_upsilon_iff P).1 hP).1)

omit [Fintype A] in
/-- Two members of the same depth-`r` source family have the same earlier
tail sumset at every genuine transition stage. -/
theorem Definition1SourceChain.tailSumset_eq_of_mem
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (chain : Definition1SourceChain I r state)
    (P Q : Theorem21SetPartition xs n seed.card)
    (hP : P ∈ state.upsilon) (hQ : Q ∈ state.upsilon)
    {j : ℕ} (hj : j < r) :
    P.tailSumset j = Q.tailSumset j := by
  induction chain with
  | initial state valid => omega
  | @next r previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hQdata := (step.mem_next_upsilon_iff Q).1 hQ
      by_cases hjr : j = r
      · subst j
        exact hPdata.2.1.trans hQdata.2.1.symm
      · exact ih hPdata.1 hQdata.1 (by omega)

omit [Fintype A] in
/-- The cellwise quotient images of two members of one source extremal
family agree at every earlier stage.  This is proved at the actual stored
transition for that stage, not by substituting the final transition. -/
theorem Definition1SourceChain.quotientLayer_eq_of_mem
    {xs : List A} {seed : Selection xs} {n r : ℕ}
    {I : GMOTheoremEInput xs seed n}
    {state : Definition1ExtremalState xs seed n}
    (chain : Definition1SourceChain I r state)
    (P Q : Theorem21SetPartition xs n seed.card)
    (hP : P ∈ state.upsilon) (hQ : Q ∈ state.upsilon)
    {j : ℕ} (hj : j < r) (c : Fin n) :
    quotientLayer (P.tailPeriod j) (P.valueCell c) =
      quotientLayer (P.tailPeriod j) (Q.valueCell c) := by
  classical
  induction chain with
  | initial state valid => omega
  | @next r previous prior state F step ih =>
      have hPdata := (step.mem_next_upsilon_iff P).1 hP
      have hQdata := (step.mem_next_upsilon_iff Q).1 hQ
      by_cases hjr : j = r
      · subst j
        let H : AddSubgroup A := AddAction.stabilizer A
          (previous.chosen.tailSumset r : Set A)
        have hPF : quotientLayer H (P.valueCell c) =
            quotientLayer H (F.valueCell c) :=
          F.quotientLayer_eq_of_imagesIncluded_of_incidence_eq P H
            hPdata.2.2.2.1 hPdata.2.2.1 c
        have hQF : quotientLayer H (Q.valueCell c) =
            quotientLayer H (F.valueCell c) :=
          F.quotientLayer_eq_of_imagesIncluded_of_incidence_eq Q H
            hQdata.2.2.2.1 hQdata.2.2.1 c
        have hperiod : P.tailPeriod r = H := by
          unfold Theorem21SetPartition.tailPeriod
          rw [hPdata.2.1]
        rw [hperiod]
        exact hPF.trans hQF.symm
      · exact ih hPdata.1 hQdata.1 (by omega)

omit [Fintype A] in
/-- The chosen member of a recentered `Upsilon_{rho+1}` is again an honest
weak `rho`-factor form.  Earlier periods and exceptions are transported
through the real prefix chain, while the stage-`rho` data come from literal
membership in the recentered family. -/
noncomputable def WeakFactorForm.nextChosenWeak_of_recentered
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) (_hF : W.F = W.partition) :
    WeakFactorForm I rho := by
  classical
  let G := W.next.chosen
  have hGnext : G ∈ W.next.upsilon := W.next.chosen_mem
  have hGdata := (W.transition.mem_next_upsilon_iff G).1 hGnext
  have hGprevious : G ∈ W.previous.upsilon := hGdata.1
  refine {
    range := W.range
    partition := G
    admissible := W.chain.admissible_of_mem G hGprevious
    previous := W.previous
    chain := W.chain
    next := W.next
    F := W.F
    transition := W.transition
    partition_inLambda := W.transition.inLambda_of_mem_next hGnext
    tail_actual := ?_
    leading_exception := ?_
  }
  · intro s hs
    have htail : G.tailSumset s = W.partition.tailSumset s := by
      by_cases hsrho : s = rho
      · subst s
        exact hGdata.2.1.trans W.inLambda.2.1.symm
      · exact W.chain.tailSumset_eq_of_mem G W.partition
          hGprevious W.inLambda.1 (by omega)
    have hperiod : G.tailPeriod s = W.partition.tailPeriod s := by
      unfold Theorem21SetPartition.tailPeriod
      rw [htail]
    rw [hperiod]
    exact W.tail_actual s hs
  · intro c hc
    obtain ⟨x, hx, hxException⟩ := W.leading_exception c hc
    obtain ⟨y, hy, hyq⟩ := (mem_quotientLayer_iff
      (W.partition.tailPeriod c.val) (G.valueCell c)
      (QuotientAddGroup.mk' (W.partition.tailPeriod c.val) x)).1 (by
        have hqeq := W.chain.quotientLayer_eq_of_mem W.partition G
          W.inLambda.1 hGprevious hc c
        rw [← hqeq]
        exact (mem_quotientLayer_iff _ _ _).2 ⟨x, hx, rfl⟩)
    have hyException : G.IsHException (G.tailPeriod c.val) y := by
      have htail := W.chain.tailSumset_eq_of_mem G W.partition
        hGprevious W.inLambda.1 hc
      have hperiod : G.tailPeriod c.val = W.partition.tailPeriod c.val := by
        unfold Theorem21SetPartition.tailPeriod
        rw [htail]
      rw [hperiod]
      obtain ⟨d, hd⟩ := hxException
      refine ⟨d, ?_⟩
      intro hyMem
      have hqeq := W.chain.quotientLayer_eq_of_mem W.partition G
        W.inLambda.1 hGprevious hc d
      apply hd
      rw [hqeq]
      simpa [hyq] using hyMem
    exact ⟨y, hy, hyException⟩

/-- Enlarging a period enlarges every thickened cell and hence the common
core. -/
theorem Theorem21SetPartition.commonCore_mono
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    {H K : AddSubgroup A} (hHK : H ≤ K) :
    P.commonCore H ⊆ P.commonCore K := by
  classical
  intro x hx
  rw [P.mem_commonCore_iff H x] at hx
  rw [P.mem_commonCore_iff K x]
  intro c
  unfold Theorem21SetPartition.thickenedCell at hx ⊢
  obtain ⟨a, ha, h, hh, rfl⟩ := Finset.mem_add.mp (hx c)
  exact Finset.mem_add.mpr
    ⟨a, ha, h, (mem_subgroupFinset K h).2
      (hHK ((mem_subgroupFinset H h).1 hh)), rfl⟩

/-- Actual-stabilizer data associated to a literal periodic witness.  The
source numerical bound remains indexed by the witness period; this
normalization only records the genuine stabilizer and the structural data
that transport monotonically to it. -/
structure GMOTheoremEActualNormalization
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I) where
  H : AddSubgroup A
  actual_period : H = AddAction.stabilizer A
    (out.partition.sumset : Set A)
  witness_le : out.H ≤ H
  unused_mem_commonCore : out.H ≠ ⊥ →
    ∀ i : Occurrence xs, i ∉ out.partition.support →
      occurrenceValue xs i ∈ out.partition.commonCore H

/-- Every literal periodic witness has a canonical actual-stabilizer
normalization, without pretending that its witness period was already
maximal. -/
noncomputable def GMOTheoremESourceOutput.toActualNormalization
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I) :
    GMOTheoremEActualNormalization out where
  H := AddAction.stabilizer A (out.partition.sumset : Set A)
  actual_period := rfl
  witness_le := out.periodic
  unused_mem_commonCore := by
    intro hH i hi
    exact out.partition.commonCore_mono out.periodic
      (out.unused_mem_commonCore hH i hi)

/-- Literal source statement of ordinary Theorem E.  Its input is an initial
setpartition, not merely the hypotheses used to construct one. -/
def GMOTheoremESourceStatement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (seed : Selection xs) (n : ℕ)
    (I : GMOTheoremEInput xs seed n),
    0 < n → Nonempty (GMOTheoremESourceOutput I)

/-- Forget the literal base-family data after the source theorem has been
proved. -/
def GMOTheoremESourceOutput.toProjected
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I) :
    GMOTheoremEOutput xs seed n where
  partition := out.partition
  H := out.H
  periodic := out.periodic
  card_lower := out.card_lower
  unused_in_core := out.unused_mem_commonCore

/-- One sufficient route to a Theorem E output.  Global elimination of
doubled exceptions yields the numerical inequality, while the independent
source conclusion places every unused labelled occurrence in the common
core.  The source proof does not assert global no-doubledness as its final
output, so this constructor is deliberately not presented as the unique or
complete route to Theorem E. -/
theorem nonempty_gmoTheoremEOutput_of_structural_conclusions
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P : Theorem21SetPartition xs n seed.card)
    (hno : ∀ x : A, ¬ P.IsHDoubledException
      (AddAction.stabilizer A (P.sumset : Set A)) x)
    (hstruct : AddAction.stabilizer A (P.sumset : Set A) ≠ ⊥ →
      ∀ i : Occurrence xs, i ∉ P.support →
        occurrenceValue xs i ∈ P.commonCore
          (AddAction.stabilizer A (P.sumset : Set A))) :
    Nonempty (GMOTheoremEOutput xs seed n) := by
  exact ⟨{
    partition := P
    H := AddAction.stabilizer A (P.sumset : Set A)
    periodic := le_rfl
    card_lower := P.theoremE_card_lower_of_no_doubled hno
    unused_in_core := hstruct
  }⟩

/-- Older projected Theorem E boundary obtained after constructing and then
forgetting a literal source input.  It is retained for downstream compatibility
but is not the exact source theorem; see `GMOTheoremESourceStatement`. -/
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

omit [AddCommGroup A] [Fintype A] in
/-- Leading and tail cells partition all cell indices, hence their incidence
totals add to the exact replacement length. -/
theorem Theorem21SetPartition.sum_leading_add_sum_tail
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m) :
    (∑ c ∈ leadingIndices n rho, (P.valueCell c).card) +
        ∑ c ∈ tailIndices n rho, (P.valueCell c).card = m := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun c : Fin n ↦ c.val < rho)
      (fun c : Fin n ↦ (P.valueCell c).card)
  rw [P.sum_card_valueCell] at hsplit
  simpa [leadingIndices, tailIndices, not_lt] using hsplit

omit [AddCommGroup A] [Fintype A] in
/-- Natural-number closing step for dissertation Lemma 3.  The hypotheses
are the quotient growth (II), the leading singleton-fiber holes count,
failure of the tail deficit (III), and the two periodic quotient-cardinality
identities.  Keeping this arithmetic separate makes every subtraction guard
auditable. -/
theorem lemma3_nat_closing
    {m n rho h qTail qLead qFull tailCard fullCard
      leadIncidence tailIncidence : ℕ}
    (hrange : rho ≤ n) (hh : 1 ≤ h)
    (hbase : rho + 1 ≤ qTail + qLead)
    (hII : qTail + qLead - (rho + 1) + 1 ≤ qFull)
    (htail : tailCard = h * qTail)
    (hfull : fullCard = h * qFull)
    (hholes : leadIncidence + rho * (h - 1) ≤ h * qLead)
    (hlead : rho ≤ leadIncidence)
    (htailGuard : n - rho ≤ tailIncidence)
    (hnotIII : tailIncidence - (n - rho) + 1 ≤ tailCard)
    (hsplit : leadIncidence + tailIncidence = m) :
    m - n + 1 ≤ fullCard := by
  have hrhoq : rho ≤ qTail + qLead := by omega
  have hquot : qTail + qLead - rho ≤ qFull := by omega
  have hmul := Nat.mul_le_mul_left h hquot
  have hmul' : h * qTail + h * qLead - h * rho ≤ h * qFull := by
    simpa [Nat.mul_sub_left_distrib, Nat.mul_add] using hmul
  have hrhoLe : rho ≤ rho * h := by
    simpa using Nat.mul_le_mul_left rho hh
  have hrhoMul : rho * (h - 1) + rho = h * rho := by
    calc
      rho * (h - 1) + rho = rho * h - rho + rho := by
        simp only [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = rho * h := Nat.sub_add_cancel hrhoLe
      _ = h * rho := Nat.mul_comm _ _
  have hmiddle : h * qTail + leadIncidence - rho ≤
      h * qTail + h * qLead - h * rho := by
    omega
  have hperiodicLower : tailCard + leadIncidence - rho ≤ fullCard := by
    rw [htail, hfull]
    exact hmiddle.trans hmul'
  have hcdt : m - n + 1 ≤ tailCard + leadIncidence - rho := by
    omega
  exact hcdt.trans hperiodicLower

omit [AddCommGroup A] [Fintype A] in
/-- Finite telescoping form used in dissertation Lemma 4.  Each one-step
Scherk/Kneser estimate loses at most one, so adjoining `rho` leading cells
loses at most `rho` in total. -/
theorem nat_card_telescope_sub
    (tail cell : ℕ → ℕ) (rho : ℕ)
    (hstep : ∀ j < rho,
      tail (j + 1) + cell j - 1 ≤ tail j)
    (hcell : ∀ j < rho, 1 ≤ cell j) :
    tail rho + (∑ j ∈ Finset.range rho, cell j) - rho ≤ tail 0 := by
  induction rho with
  | zero => simp
  | succ rho ih =>
      have hstepLast := hstep rho (Nat.lt_succ_self rho)
      have hcellLast := hcell rho (Nat.lt_succ_self rho)
      have ih' := ih
        (fun j hj ↦ hstep j (hj.trans (Nat.lt_succ_self rho)))
        (fun j hj ↦ hcell j (hj.trans (Nat.lt_succ_self rho)))
      have hsumGuard : rho ≤ ∑ j ∈ Finset.range rho, cell j := by
        calc
          rho = (Finset.range rho).card := (Finset.card_range rho).symm
          _ = ∑ _j ∈ Finset.range rho, 1 := by simp
          _ ≤ ∑ j ∈ Finset.range rho, cell j := by
            exact Finset.sum_le_sum fun j hj ↦
              hcell j (Finset.mem_range.mp hj |>.trans
                (Nat.lt_succ_self rho))
      rw [Finset.sum_range_succ]
      omega

omit [AddCommGroup A] [Fintype A] in
/-- Contrapositive form of finite tail telescoping.  If the first tail is
strictly below the accumulated cell mass minus the number of joins, then
one nonterminal adjacent tail step already has the same strict deficit. -/
theorem nat_exists_local_deficit_of_telescope
    (tail cell : ℕ → ℕ) (k : ℕ) (hk : 2 ≤ k)
    (hcell : ∀ j < k, 1 ≤ cell j)
    (hlast : tail (k - 1) = cell (k - 1))
    (hglobal :
      tail 0 < (∑ j ∈ Finset.range k, cell j) - k + 1) :
    ∃ j, j < k - 1 ∧ tail j < tail (j + 1) + cell j - 1 := by
  by_contra hnone
  push Not at hnone
  have hstep : ∀ j < k - 1,
      tail (j + 1) + cell j - 1 ≤ tail j := by
    intro j hj
    exact hnone j hj
  have htel := nat_card_telescope_sub tail cell (k - 1) hstep
    (fun j hj ↦ hcell j (by omega))
  let t := k - 1
  have hkt : k = t + 1 := by
    dsimp only [t]
    omega
  have hsum :
      (∑ j ∈ Finset.range k, cell j) =
        (∑ j ∈ Finset.range t, cell j) + cell t := by
    rw [hkt, Finset.sum_range_succ]
  have hmass :
      t ≤ ∑ j ∈ Finset.range t, cell j := by
    calc
      t = (Finset.range t).card :=
        (Finset.card_range t).symm
      _ = ∑ _j ∈ Finset.range t, 1 := by simp
      _ ≤ ∑ j ∈ Finset.range t, cell j := by
        exact Finset.sum_le_sum fun j hj ↦
          hcell j (by
            have := Finset.mem_range.mp hj
            dsimp only [t] at this
            omega)
  have htlt : t < k := by
    dsimp only [t]
    omega
  have hlastCell : 1 ≤ cell t := hcell t htlt
  have hguard :
      t + 1 ≤ (∑ j ∈ Finset.range t, cell j) + cell t := by
    omega
  have hrewrite :
      (∑ j ∈ Finset.range t, cell j) + cell t - (t + 1) + 1 =
        cell t + (∑ j ∈ Finset.range t, cell j) - t := by
    omega
  change tail t + (∑ j ∈ Finset.range t, cell j) - t ≤ tail 0 at htel
  change tail t = cell t at hlast
  rw [hlast] at htel
  rw [hsum, hkt, hrewrite] at hglobal
  omega

/-- Dissertation Lemma 4's telescoped condition (II).  Each leading index
uses `lemma4_step` at its own true prefix transition; the finite reindexing
below identifies `0, ..., rho-1` exactly with `leadingIndices n rho`. -/
theorem WeakFactorForm.lemma4_quotient_growth
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho) :
    ((quotientLayer (W.partition.tailPeriod rho)
          (W.partition.tailSumset rho)).card +
        (∑ c ∈ leadingIndices n rho,
          (quotientLayer (W.partition.tailPeriod rho)
            (W.partition.valueCell c)).card) - (rho + 1) + 1) ≤
      (quotientLayer (W.partition.tailPeriod rho)
        W.partition.sumset).card := by
  classical
  let H : AddSubgroup A := W.partition.tailPeriod rho
  have hrange : rho ≤ n := by
    have := W.range
    omega
  have hnpos : 0 < n := by
    have := W.range
    omega
  let idx : ℕ → Fin n := fun j ↦ ⟨j % n, Nat.mod_lt j hnpos⟩
  let tail : ℕ → ℕ := fun j ↦
    (quotientLayer H (W.partition.tailSumset j)).card
  let cell : ℕ → ℕ := fun j ↦
    (quotientLayer H (W.partition.valueCell (idx j))).card
  have hidx {j : ℕ} (hj : j < rho) : (idx j).val = j := by
    have hjn : j < n := hj.trans_le hrange
    simp [idx, Nat.mod_eq_of_lt hjn]
  have hstep : ∀ j < rho,
      tail (j + 1) + cell j - 1 ≤ tail j := by
    intro j hj
    have hc : (idx j).val < rho := by simpa [hidx hj] using hj
    have hs := W.lemma4_step (idx j) hc
    simpa [tail, cell, H, hidx hj] using hs
  have hcell : ∀ j < rho, 1 ≤ cell j := by
    intro j hj
    apply Finset.card_pos.mpr
    exact quotientLayer_nonempty H _ (W.partition.valueCells_nonempty
      (W.partition.valueCell (idx j)) (by
        simp [Theorem21SetPartition.valueCells]))
  have htelescope := nat_card_telescope_sub tail cell rho hstep hcell
  have hsum : (∑ j ∈ Finset.range rho, cell j) =
      ∑ c ∈ leadingIndices n rho,
        (quotientLayer H (W.partition.valueCell c)).card := by
    refine Finset.sum_bij (fun j _ ↦ idx j) ?_ ?_ ?_ ?_
    · intro j hj
      have hjrho : j < rho := Finset.mem_range.mp hj
      simpa [leadingIndices, hidx hjrho]
    · intro i hi j hj hij
      have hi' : i < rho := Finset.mem_range.mp hi
      have hj' : j < rho := Finset.mem_range.mp hj
      have hv := congrArg Fin.val hij
      simpa [hidx hi', hidx hj'] using hv
    · intro c hc
      have hc' : c.val < rho := by simpa [leadingIndices] using hc
      refine ⟨c.val, Finset.mem_range.mpr hc', ?_⟩
      apply Fin.ext
      exact hidx hc'
    · intro j hj
      rfl
  rw [hsum] at htelescope
  have htailZero : tail 0 =
      (quotientLayer H W.partition.sumset).card := by
    simp [tail, Theorem21SetPartition.tailSumset,
      Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.sumset]
  rw [htailZero] at htelescope
  have hbase := W.quotient_growth_base_le
  change rho + 1 ≤ tail rho +
    ∑ c ∈ leadingIndices n rho,
      (quotientLayer H (W.partition.valueCell c)).card at hbase
  change tail rho +
      (∑ c ∈ leadingIndices n rho,
        (quotientLayer H (W.partition.valueCell c)).card) - rho ≤
    (quotientLayer H W.partition.sumset).card at htelescope
  change tail rho +
      (∑ c ∈ leadingIndices n rho,
        (quotientLayer H (W.partition.valueCell c)).card) -
          (rho + 1) + 1 ≤
    (quotientLayer H W.partition.sumset).card
  omega

/-- Dissertation Lemma 3 in its source-faithful disjunctive form.  Condition
(II) forces either the missing condition (III), or an admissible replacement
already satisfying the ordinary Cauchy--Davenport bound.  The second branch
is intentionally the scalar trivial-period conclusion, not a false claim
that the trivial subgroup is the actual stabilizer. -/
theorem WeakFactorForm.lemma3_dichotomy
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (hII :
      ((quotientLayer (W.partition.tailPeriod rho)
            (W.partition.tailSumset rho)).card +
          (∑ c ∈ leadingIndices n rho,
            (quotientLayer (W.partition.tailPeriod rho)
              (W.partition.valueCell c)).card) - (rho + 1) + 1) ≤
        (quotientLayer (W.partition.tailPeriod rho)
          W.partition.sumset).card) :
    (W.partition.tailSumset rho).card <
        (∑ c ∈ tailIndices n rho,
          (W.partition.valueCell c).card) - (n - rho) + 1 ∨
      Nonempty (GMOTheoremETrivialConclusion I) := by
  classical
  by_cases hIII :
      (W.partition.tailSumset rho).card <
        (∑ c ∈ tailIndices n rho,
          (W.partition.valueCell c).card) - (n - rho) + 1
  · exact Or.inl hIII
  · right
    let H : AddSubgroup A := W.partition.tailPeriod rho
    let qTail := (quotientLayer H (W.partition.tailSumset rho)).card
    let qLead := ∑ c ∈ leadingIndices n rho,
      (quotientLayer H (W.partition.valueCell c)).card
    let qFull := (quotientLayer H W.partition.sumset).card
    let leadIncidence := ∑ c ∈ leadingIndices n rho,
      (W.partition.valueCell c).card
    let tailIncidence := ∑ c ∈ tailIndices n rho,
      (W.partition.valueCell c).card
    have hrange : rho ≤ n := by
      have := W.range
      omega
    have hbase : rho + 1 ≤ qTail + qLead := by
      simpa [H, qTail, qLead] using W.quotient_growth_base_le
    have hII' : qTail + qLead - (rho + 1) + 1 ≤ qFull := by
      simpa [H, qTail, qLead, qFull] using hII
    have htail : (W.partition.tailSumset rho).card =
        Nat.card H * qTail := by
      apply card_eq_natCard_mul_card_quotientLayer_of_le_stabilizer
      exact le_rfl
    have hfull : W.partition.sumset.card = Nat.card H * qFull := by
      apply card_eq_natCard_mul_card_quotientLayer_of_le_stabilizer
      exact W.tailPeriod_le_sumset_stabilizer
    have hholes : leadIncidence + rho * (Nat.card H - 1) ≤
        Nat.card H * qLead := by
      simpa [H, leadIncidence, qLead] using W.leading_holes_le
    have hlead : rho ≤ leadIncidence := by
      calc
        rho = (leadingIndices n rho).card :=
          (card_leadingIndices hrange).symm
        _ = ∑ c ∈ leadingIndices n rho, 1 := by simp
        _ ≤ ∑ c ∈ leadingIndices n rho,
            (W.partition.valueCell c).card := by
          exact Finset.sum_le_sum fun c _ ↦
            Finset.card_pos.mpr (W.partition.valueCells_nonempty
              (W.partition.valueCell c) (by
                simp [Theorem21SetPartition.valueCells]))
        _ = leadIncidence := rfl
    have htailGuard : n - rho ≤ tailIncidence := by
      simpa [tailIncidence] using
        W.partition.card_tailIndices_le_sum_card_valueCell hrange
    have hnotIII : tailIncidence - (n - rho) + 1 ≤
        (W.partition.tailSumset rho).card := by
      simpa [tailIncidence] using Nat.le_of_not_gt hIII
    have hsplit : leadIncidence + tailIncidence = seed.card := by
      simpa [leadIncidence, tailIncidence] using
        W.partition.sum_leading_add_sum_tail (rho := rho)
    have hcdt : seed.card - n + 1 ≤ W.partition.sumset.card :=
      lemma3_nat_closing hrange Nat.card_pos hbase hII' htail hfull
        hholes hlead htailGuard hnotIII hsplit
    exact ⟨{
      partition := W.partition
      admissible := W.admissible
      card_lower := hcdt
    }⟩

/-- Under the global contradiction hypothesis that no trivial/CDT
conclusion exists, Lemma 3 supplies condition (III). -/
theorem WeakFactorForm.tail_deficit_of_quotient_growth
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (hII :
      ((quotientLayer (W.partition.tailPeriod rho)
            (W.partition.tailSumset rho)).card +
          (∑ c ∈ leadingIndices n rho,
            (quotientLayer (W.partition.tailPeriod rho)
              (W.partition.valueCell c)).card) - (rho + 1) + 1) ≤
        (quotientLayer (W.partition.tailPeriod rho)
          W.partition.sumset).card)
    (hfail : ¬ Nonempty (GMOTheoremETrivialConclusion I)) :
    (W.partition.tailSumset rho).card <
      (∑ c ∈ tailIndices n rho,
        (W.partition.valueCell c).card) - (n - rho) + 1 := by
  rcases W.lemma3_dichotomy hII with hIII | htrivial
  · exact hIII
  · exact (hfail htrivial).elim

/-- The usual factor-form packaging of Lemma 3 after excluding the scalar
trivial/CDT branch. -/
noncomputable def WeakFactorForm.toFactorForm_of_quotient_growth
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (hII :
      ((quotientLayer (W.partition.tailPeriod rho)
            (W.partition.tailSumset rho)).card +
          (∑ c ∈ leadingIndices n rho,
            (quotientLayer (W.partition.tailPeriod rho)
              (W.partition.valueCell c)).card) - (rho + 1) + 1) ≤
        (quotientLayer (W.partition.tailPeriod rho)
          W.partition.sumset).card)
    (hfail : ¬ Nonempty (GMOTheoremETrivialConclusion I)) :
    FactorForm I rho where
  toWeakFactorForm := W
  quotient_growth := hII
  tail_deficit := W.tail_deficit_of_quotient_growth hII hfail

/-- Complete dissertation Lemma 4 under the standing contradiction
hypothesis of Theorem 3.1: Lemma 4 supplies (II), and the source-faithful
Lemma 3 dichotomy supplies (III) after excluding the trivial/CDT branch. -/
noncomputable def WeakFactorForm.toFactorForm
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (W : WeakFactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremETrivialConclusion I)) :
    FactorForm I rho :=
  W.toFactorForm_of_quotient_growth W.lemma4_quotient_growth hfail

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
  have hcore := h.unused_in_core hH i hisupport
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

/-- An actual unused labelled occurrence supplies a point of the common
core.  Its full `H`-coset is then contained in the core, so the source count
`N = |core| / |H|` is at least one.  This is the faithful conditional form of
`N ≥ 1`; no such assertion is built into Theorem E when there is no unused
source occurrence. -/
theorem GMOTheoremESourceOutput.one_le_commonCosetCount_of_exists_unused
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hH : out.H ≠ ⊥)
    (hu : ∃ i : Occurrence xs, i ∉ out.partition.support) :
    1 ≤ out.partition.commonCosetCount out.H := by
  classical
  rcases hu with ⟨i, hi⟩
  have hx : occurrenceValue xs i ∈ out.partition.commonCore out.H :=
    out.unused_mem_commonCore hH i hi
  have hcoset : addCosetFinset out.H (occurrenceValue xs i) ⊆
      out.partition.commonCore out.H := by
    intro y hy
    have hyH := (mem_addCosetFinset_iff out.H
      (occurrenceValue xs i) y).1 hy
    have hadd := out.partition.add_mem_commonCore out.H hyH hx
    simpa [sub_add_cancel] using hadd
  have hcard : Nat.card out.H ≤
      (out.partition.commonCore out.H).card := by
    simpa using Finset.card_le_card hcoset
  unfold Theorem21SetPartition.commonCosetCount
  exact (Nat.le_div_iff_mul_le Nat.card_pos).2 (by simpa using hcard)

/-- Conversely, `N = 0` forces the replacement support to use every source
occurrence; otherwise the preceding lemma would give `N ≥ 1`. -/
theorem GMOTheoremESourceOutput.support_eq_univ_of_commonCosetCount_eq_zero
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hH : out.H ≠ ⊥)
    (hN : out.partition.commonCosetCount out.H = 0) :
    out.partition.support = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  by_contra hi
  have hOne := out.one_le_commonCosetCount_of_exists_unused hH ⟨i, hi⟩
  omega

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
    have hcoeff :
        ((1 * n + h.partition.exceptionDefect h.H + 1) - n) =
          h.partition.exceptionDefect h.H + 1 := by
      omega
    rw [hcoeff] at hbound
    exact hbound
  · have houtside := h.card_outsideCommonCore hnontrivial
    have hoccurrences :
        h.partition.occurrencesInCommonCore h.H =
          occurrencesInAddCoset xs h.H alpha := by
      ext i
      rw [h.partition.mem_occurrencesInCommonCore_iff,
        mem_occurrencesInAddCoset_iff, hcore,
        mem_addCosetFinset_iff]
    rwa [hoccurrences] at houtside

/-- If Theorem E has reached `N = 1`, failure of the large alternative forces
the source-sharp exception bound `e ≤ |A/H| - 2`.  This is the exact
arithmetic closing step in the terminal case of Theorems 2.4/2.5. -/
theorem GMOTheoremEOutput.exceptionDefect_le_quotient_sub_two_of_count_eq_one
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n)
    (hproper : h.H < ⊤)
    (hN : h.partition.commonCosetCount h.H = 1)
    (hnotLarge : ¬ min (Nat.card A) (seed.card - n + 1) ≤
      h.partition.sumset.card) :
    h.partition.exceptionDefect h.H ≤ Nat.card (A ⧸ h.H) - 2 := by
  have hsumLt : h.partition.sumset.card < Nat.card A := by
    apply Nat.lt_of_not_ge
    intro hambient
    exact hnotLarge ((min_le_left _ _).trans hambient)
  have hbound := h.card_lower
  rw [hN] at hbound
  have hcoeff :
      ((1 * n + h.partition.exceptionDefect h.H + 1) - n) =
        h.partition.exceptionDefect h.H + 1 := by
    omega
  rw [hcoeff] at hbound
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup h.H
  have hprodLt :
      (h.partition.exceptionDefect h.H + 1) * Nat.card h.H <
        Nat.card (A ⧸ h.H) * Nat.card h.H := by
    rw [← hcard]
    exact hbound.trans_lt hsumLt
  have hHpos : 0 < Nat.card h.H := Nat.card_pos
  have heSuccLt :
      h.partition.exceptionDefect h.H + 1 < Nat.card (A ⧸ h.H) :=
    (Nat.mul_lt_mul_right hHpos).mp hprodLt
  have hquotient : 2 ≤ Nat.card (A ⧸ h.H) :=
    two_le_natCard_quotient_of_lt_top h.H hproper
  omega

/-- The `N = 1` proper-nontrivial Theorem E output already gives a complete
Theorem 2.1 output; no replacement is needed in this terminal case. -/
theorem GMOTheoremEOutput.nonempty_theorem21Output_of_count_eq_one
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n)
    (hnontrivial : h.H ≠ ⊥) (hproper : h.H < ⊤)
    (hN : h.partition.commonCosetCount h.H = 1) :
    Nonempty (GMOTheorem21Output xs seed n) := by
  by_cases hlarge : min (Nat.card A) (seed.card - n + 1) ≤
      h.partition.sumset.card
  · exact ⟨{
      partition := h.partition
      alternative := Or.inl ⟨hlarge⟩
    }⟩
  · have he :=
      h.exceptionDefect_le_quotient_sub_two_of_count_eq_one hproper hN hlarge
    exact ⟨{
      partition := h.partition
      alternative := Or.inr
        (h.nonempty_periodicAlternative_of_terminal
          hnontrivial hproper hN he)
    }⟩

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

/-- A scalar CDT conclusion is already a literal Theorem E output with the
trivial witness period.  This bridge is what allows Lemma 3 to be used under
failure of the full source output, without silently replacing that failure
by a stronger assumption. -/
noncomputable def GMOTheoremETrivialConclusion.toSourceOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (h : GMOTheoremETrivialConclusion I) :
    GMOTheoremESourceOutput I := by
  classical
  have hlen : n ≤ seed.card := by
    have hmass := length_le_sum_layer_card h.partition.valueCells
      h.partition.valueCells_nonempty
    rw [h.partition.length_valueCells] at hmass
    simpa [Theorem21SetPartition.valueCells, List.map_ofFn,
      List.sum_ofFn, h.partition.sum_card_valueCell] using hmass
  refine {
    partition := h.partition
    H := ⊥
    periodic := bot_le
    admissible := h.admissible
    card_lower := ?_
    unused_mem_commonCore := ?_
  }
  · have hincidence :=
      h.partition.exceptionDefect_bot_add_core_incidence
    have htotal :
        (h.partition.commonCore (⊥ : AddSubgroup A)).card * n +
            h.partition.exceptionDefect (⊥ : AddSubgroup A) = seed.card := by
      simpa [Nat.add_comm, Nat.mul_comm] using hincidence
    have hcoeff :
        ((h.partition.commonCosetCount (⊥ : AddSubgroup A) * n +
            h.partition.exceptionDefect (⊥ : AddSubgroup A) + 1) - n) *
              Nat.card (⊥ : AddSubgroup A) = seed.card - n + 1 := by
      simp only [h.partition.commonCosetCount_bot, Nat.card_unique, mul_one]
      rw [htotal]
      omega
    rw [hcoeff]
    exact h.card_lower
  · intro hbot
    exact (hbot rfl).elim

/-- Full source-output failure therefore entails the scalar failure required
by the Lemma-3-to-factor-form constructor. -/
theorem not_nonempty_trivialConclusion_of_no_sourceOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) :
    ¬ Nonempty (GMOTheoremETrivialConclusion I) := by
  rintro ⟨h⟩
  exact hfail ⟨h.toSourceOutput⟩

/-- The trivial-period specialization of Theorem E's numerical bound is at
least the large-branch threshold `|S'| - n + 1`.  Encoding the source
coefficient by subtracting `n` only after the full incidence sum makes this
uniform, including the empty-common-core case. -/
theorem GMOTheoremEOutput.card_lower_of_H_eq_bot
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (h : GMOTheoremEOutput xs seed n) (hH : h.H = ⊥)
    (hlen : n ≤ seed.card) :
    seed.card - n + 1 ≤ h.partition.sumset.card := by
  have hbound := h.card_lower
  rw [hH] at hbound
  simp only [h.partition.commonCosetCount_bot, Nat.card_unique, mul_one] at hbound
  have hincidence := h.partition.exceptionDefect_bot_add_core_incidence
  rw [Nat.mul_comm n
    (h.partition.commonCore (⊥ : AddSubgroup A)).card] at hincidence
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

omit [Fintype A] in
/-- Omitting the first cell of the `rho`-tail leaves exactly the
`rho+1`-tail. -/
theorem Theorem21SetPartition.tailSumsetWithoutCell_rho_eq_succ
    {xs : List A} {n m rho : ℕ} (P : Theorem21SetPartition xs n m)
    (hrhon : rho < n) :
    P.tailSumsetWithoutCell ⟨rho, hrhon⟩ rho =
      P.tailSumset (rho + 1) := by
  unfold Theorem21SetPartition.tailSumsetWithoutCell
    Theorem21SetPartition.tailValueCellsWithoutCell
    Theorem21SetPartition.tailSumset
    Theorem21SetPartition.tailValueCells
  simp

omit [AddCommGroup A] [Fintype A] in
/-- Removing index `rho` from the `rho`-tail index set leaves exactly the
next tail index set. -/
theorem tailIndices_erase_rho_eq_succ {n rho : ℕ} (hrhon : rho < n) :
    (tailIndices n rho).erase ⟨rho, hrhon⟩ =
      tailIndices n (rho + 1) := by
  classical
  ext c
  simp only [Finset.mem_erase, mem_tailIndices]
  constructor
  · rintro ⟨hcne, hrc⟩
    have hcval : c.val ≠ rho := by
      intro h
      apply hcne
      apply Fin.ext
      exact h
    omega
  · intro hsucc
    refine ⟨?_, by omega⟩
    intro hc
    have hv := congrArg Fin.val hc
    change c.val = rho at hv
    omega

/-- Equation (3.5), with both source branches explicit.  If the transported
exception is doubled, Lemma 2 applies.  Otherwise its quotient fiber in the
new first tail cell is a singleton, so quotient Kneser/Scherk supplies the
same equation-(3.3) input and Lemma 2's arithmetic closes the deficit. -/
theorem FactorForm.next_tail_deficit_of_exception_at_rho
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho) (x : A)
    (hx : x ∈ F.partition.valueCell ⟨rho, by
      have := F.range; omega⟩)
    (hxException : F.partition.IsHException
      (F.partition.tailPeriod rho) x) :
    (F.partition.tailSumset (rho + 1)).card <
      (∑ c ∈ tailIndices n (rho + 1),
        (F.partition.valueCell c).card) - (n - (rho + 1)) + 1 := by
  classical
  have hrhon : rho < n := by
    have := F.range
    omega
  let q : Fin n := ⟨rho, hrhon⟩
  have hqval : q.val = rho := rfl
  have hrhoq : rho ≤ q.val := le_rfl
  have hraw :
      (F.partition.tailSumsetWithoutCell q rho).card <
        (∑ c ∈ (tailIndices n rho).erase q,
          (F.partition.valueCell c).card) - ((n - rho) - 1) + 1 := by
    by_cases hdouble : F.partition.IsHDoubledInCell
        (F.partition.tailPeriod rho) q x
    · exact F.toWeakFactorForm.lemma2 F.tail_deficit q x
        hxException hdouble
    · have hB : (F.partition.tailSumset (rho + 1)).Nonempty :=
        F.partition.tailSumset_nonempty (rho + 1)
      have hC : (F.partition.valueCell q).Nonempty :=
        F.partition.valueCells_nonempty (F.partition.valueCell q) (by
          simp [Theorem21SetPartition.valueCells])
      have hsum : F.partition.tailSumset (rho + 1) +
          F.partition.valueCell q = F.partition.tailSumset rho := by
        rw [add_comm]
        simpa only [q, hqval] using
          (F.partition.tailSumset_eq_valueCell_add_succ q).symm
      have hunique : ∀ y ∈ F.partition.valueCell q,
          y - x ∈ AddAction.stabilizer A
            ((F.partition.tailSumset (rho + 1) +
              F.partition.valueCell q : Finset A) : Set A) → y = x := by
        intro y hy hystab
        by_contra hyx
        apply hdouble
        refine ⟨hx, y, hy, hyx, ?_⟩
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        unfold Theorem21SetPartition.tailPeriod
        simpa only [hsum] using hystab
      have hkneser := card_add_sub_one_le_of_unique_addStab_fiber
        (F.partition.tailSumset (rho + 1)) (F.partition.valueCell q)
        hB hC hx hunique
      have h33 :
          (F.partition.tailSumsetWithoutCell q rho).card +
              (F.partition.valueCell q).card - 1 ≤
            (F.partition.tailSumset rho).card := by
        rw [F.partition.tailSumsetWithoutCell_rho_eq_succ hrhon]
        rw [hsum] at hkneser
        exact hkneser
      exact F.toWeakFactorForm.lemma2_of_equation33 F.tail_deficit
        q hrhoq h33
  rw [F.partition.tailSumsetWithoutCell_rho_eq_succ hrhon] at hraw
  rw [show q = ⟨rho, hrhon⟩ by rfl,
    tailIndices_erase_rho_eq_succ hrhon] at hraw
  have harith : (n - rho) - 1 = n - (rho + 1) := by omega
  rwa [harith] at hraw

omit [Fintype A] in
/-- A strict full-layer deficit cannot occur in a one-cell tail. -/
theorem Theorem21SetPartition.two_le_tail_length_of_deficit
    {xs : List A} {n m s : ℕ} (P : Theorem21SetPartition xs n m)
    (hsn : s < n)
    (hdeficit : (P.tailSumset s).card <
      (∑ c ∈ tailIndices n s, (P.valueCell c).card) - (n - s) + 1) :
    2 ≤ n - s := by
  classical
  by_contra hnot
  have hn : n = s + 1 := by omega
  let q : Fin n := ⟨s, by omega⟩
  have htailNext : P.tailSumset (s + 1) = ({0} : Finset A) := by
    subst n
    simp [Theorem21SetPartition.tailSumset,
      Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.valueCells, fullLayerSumSpectrum]
  have htail : P.tailSumset s = P.valueCell q := by
    have hrec := P.tailSumset_eq_valueCell_add_succ q
    rw [htailNext] at hrec
    change P.tailSumset s = P.valueCell q + (0 : Finset A) at hrec
    simpa only [add_zero] using hrec
  have hindices : tailIndices n s = {q} := by
    ext c
    simp only [mem_tailIndices, Finset.mem_singleton]
    constructor
    · intro hc
      apply Fin.ext
      have hcLt := c.isLt
      simp only [q]
      omega
    · rintro rfl
      exact le_rfl
  rw [htail, hindices] at hdeficit
  have hns : n - s = 1 := by omega
  rw [hns] at hdeficit
  simp only [Finset.sum_singleton] at hdeficit
  have hcell : 1 ≤ (P.valueCell q).card :=
    Finset.card_pos.mpr (P.valueCells_nonempty
      (P.valueCell q) (by
        simp [Theorem21SetPartition.valueCells]))
  omega

omit [Fintype A] in
@[simp]
theorem card_quotientLayer_bot (B : Finset A) :
    (quotientLayer (⊥ : AddSubgroup A) B).card = B.card := by
  classical
  unfold quotientLayer
  apply Finset.card_image_iff.mpr
  intro x _ y _ hxy
  have hsub : x - y ∈ (⊥ : AddSubgroup A) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  exact sub_eq_zero.mp hsub

/-- The actual stabilizer of a strict full-layer-deficit tail is nontrivial.
This is the DGM/Kneser step immediately following equation (3.5). -/
theorem Theorem21SetPartition.tailPeriod_ne_bot_of_deficit
    {xs : List A} {n m s : ℕ} (P : Theorem21SetPartition xs n m)
    (hdeficit : (P.tailSumset s).card <
      (∑ c ∈ tailIndices n s, (P.valueCell c).card) - (n - s) + 1) :
    P.tailPeriod s ≠ ⊥ := by
  classical
  intro hbot
  have htailNonempty : IsNonemptySetPartition (P.tailValueCells s) := by
    simpa [Theorem21SetPartition.tailValueCells] using
      P.valueCells_nonempty.drop s
  have hdgm := fullLayer_dgm_lower_bound
    (P.tailValueCells s) htailNonempty
  change
    (((P.tailValueCells s).map fun B ↦
          (stabilizerQuotientLayer (P.tailSumset s) B).card).sum -
        (P.tailValueCells s).length + 1) *
        (P.tailSumset s).addStab.card ≤
      (P.tailSumset s).card at hdgm
  simp_rw [← quotientLayer_eq_stabilizerQuotientLayer
    (P.tailSumset s)] at hdgm
  have hperiod : AddAction.stabilizer A
      (P.tailSumset s : Set A) = (⊥ : AddSubgroup A) := by
    simpa [Theorem21SetPartition.tailPeriod] using hbot
  have hstabCard : (P.tailSumset s).addStab.card = 1 := by
    have h := card_addStab_eq_natCard_stabilizer
      (P.tailSumset s) (P.tailSumset_nonempty s)
    rw [hperiod] at h
    simpa using h
  rw [hperiod] at hdgm
  rw [hstabCard] at hdgm
  simp only [card_quotientLayer_bot, mul_one] at hdgm
  have hlength : (P.tailValueCells s).length = n - s := by
    simp [Theorem21SetPartition.tailValueCells, P.length_valueCells]
  have hsum : (P.tailValueCells s |>.map Finset.card).sum =
      ∑ c ∈ tailIndices n s, (P.valueCell c).card :=
    P.sum_card_tailValueCells_eq_tailIndices
  rw [hlength, hsum] at hdgm
  omega

/-- Thickening a nonempty replacement cell by the whole ambient subgroup
gives the whole ambient group. -/
@[simp]
theorem Theorem21SetPartition.thickenedCell_top
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (c : Fin n) :
    P.thickenedCell (⊤ : AddSubgroup A) c = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨a, ha⟩ := P.valueCells_nonempty (P.valueCell c) (by
    simp [Theorem21SetPartition.valueCells])
  unfold Theorem21SetPartition.thickenedCell
  apply Finset.mem_add.mpr
  refine ⟨a, ha, x - a, ?_, ?_⟩
  · simp
  · abel

/-- Consequently the common top-thickened core is all of the ambient
group. -/
@[simp]
theorem Theorem21SetPartition.commonCore_top
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.commonCore (⊤ : AddSubgroup A) = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  exact (P.mem_commonCore_iff (⊤ : AddSubgroup A) x).2 fun c ↦ by simp

/-- At top period there is exactly one common coset. -/
@[simp]
theorem Theorem21SetPartition.commonCosetCount_top
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.commonCosetCount (⊤ : AddSubgroup A) = 1 := by
  classical
  unfold Theorem21SetPartition.commonCosetCount
  rw [Theorem21SetPartition.commonCore_top P, Finset.card_univ]
  have htopCard : Nat.card (⊤ : AddSubgroup A) = Nat.card A := by
    simp [Nat.card_eq_fintype_card]
  rw [htopCard]
  simpa only [Nat.card_eq_fintype_card] using
    Nat.div_self (Nat.card_pos : 0 < Nat.card A)

/-- At top period every value of every cell lies in the common core, so the
exception defect vanishes. -/
@[simp]
theorem Theorem21SetPartition.exceptionDefect_top
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    P.exceptionDefect (⊤ : AddSubgroup A) = 0 := by
  classical
  simp [Theorem21SetPartition.exceptionDefect,
    Theorem21SetPartition.cellExceptionDefect]

/-- A top tail period already yields the literal source Theorem E output.
This is the full-source-failure contradiction used to keep the new period
proper after equation (3.5). -/
theorem nonempty_gmoTheoremESourceOutput_of_tailPeriod_eq_top
    {xs : List A} {seed : Selection xs} {n s : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (P : Theorem21SetPartition xs n seed.card)
    (hadmissible : GMOReplacementAdmissible I P)
    (htop : P.tailPeriod s = ⊤) :
    Nonempty (GMOTheoremESourceOutput I) := by
  classical
  have hperiod : (⊤ : AddSubgroup A) ≤
      AddAction.stabilizer A (P.sumset : Set A) := by
    have hmono := P.stabilizer_tailSumset_antitone
      (show 0 ≤ s from Nat.zero_le s)
    change P.tailPeriod s ≤ P.tailPeriod 0 at hmono
    rw [htop] at hmono
    simpa [Theorem21SetPartition.tailPeriod,
      Theorem21SetPartition.tailSumset,
      Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.sumset] using hmono
  have hstabTop : AddAction.stabilizer A (P.sumset : Set A) = ⊤ :=
    top_unique hperiod
  have hsumset : P.sumset = Finset.univ := by
    by_contra hne
    have hlt := stabilizer_lt_top_of_finset_nonempty_ne_univ
      P.sumset P.sumset_nonempty hne
    rw [hstabTop] at hlt
    exact (lt_irrefl _ hlt)
  refine ⟨{
    partition := P
    H := ⊤
    periodic := hperiod
    admissible := hadmissible
    card_lower := ?_
    unused_mem_commonCore := ?_
  }⟩
  · rw [Theorem21SetPartition.commonCosetCount_top P,
      Theorem21SetPartition.exceptionDefect_top P, hsumset,
      Finset.card_univ]
    simp only [one_mul, add_zero]
    have hcoeff : (n + 1) - n = 1 := by omega
    rw [hcoeff, one_mul]
    simp [Nat.card_eq_fintype_card]
  · intro _ i _
    rw [Theorem21SetPartition.commonCore_top P]
    exact Finset.mem_univ _

/-- The honest doubled branch up through equation (3.5): after simultaneous
tail reindexing and recentering, the genuinely chosen member of the new
`Upsilon` is a factor form whose next tail has strict deficit and a proper,
nontrivial actual stabilizer.  Both endpoint exclusions use failure of the
full literal source output. -/
theorem FactorForm.exists_reindexed_next_deficit_proper
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) :
    ∃ (sigma : Equiv.Perm (Fin n))
      (G : FactorForm (I.reindex sigma) rho) (y : A),
      G.partition = G.next.chosen ∧
      y ∈ G.partition.valueCell ⟨rho, by have := F.range; omega⟩ ∧
      G.partition.IsHException (G.partition.tailPeriod rho) y ∧
      (G.partition.tailSumset (rho + 1)).card <
        (∑ c ∈ tailIndices n (rho + 1),
          (G.partition.valueCell c).card) - (n - (rho + 1)) + 1 ∧
      G.partition.tailPeriod (rho + 1) ≠ ⊥ ∧
      G.partition.tailPeriod (rho + 1) < ⊤ := by
  classical
  obtain ⟨sigma, _hfix, W, x, hFcenter, _hpartition,
      hxException, hxDouble⟩ :=
    F.exists_reindexed_recentered_doubled hfail
  have hfail' : ¬ Nonempty
      (GMOTheoremESourceOutput (I.reindex sigma)) := by
    rintro ⟨out⟩
    exact hfail ⟨out.inverseReindex sigma⟩
  let Gweak : WeakFactorForm (I.reindex sigma) rho :=
    W.nextChosenWeak_of_recentered hFcenter
  let G : FactorForm (I.reindex sigma) rho :=
    Gweak.toFactorForm
      (not_nonempty_trivialConclusion_of_no_sourceOutput hfail')
  have hGmem : G.partition ∈ W.next.upsilon := by
    exact W.next.chosen_mem
  have hrhon : rho < n := by
    have := F.range
    omega
  let q : Fin n := ⟨rho, hrhon⟩
  have hxCell : x ∈ W.partition.valueCell q := hxDouble.1
  have hxQuot : QuotientAddGroup.mk' (W.partition.tailPeriod rho) x ∈
      quotientLayer (W.partition.tailPeriod rho)
        (W.partition.valueCell q) :=
    (mem_quotientLayer_iff _ _ _).2 ⟨x, hxCell, rfl⟩
  have hqeq := W.quotientLayer_eq_of_mem_next_of_recentered
    hFcenter G.partition hGmem q
  have hxQuotG : QuotientAddGroup.mk' (W.partition.tailPeriod rho) x ∈
      quotientLayer (W.partition.tailPeriod rho)
        (G.partition.valueCell q) := by
    rw [hqeq]
    exact hxQuot
  obtain ⟨y, hyCell, hyQuot⟩ :=
    (mem_quotientLayer_iff (W.partition.tailPeriod rho)
      (G.partition.valueCell q) _).1 hxQuotG
  have hxExceptionG : G.partition.IsHException
      (W.partition.tailPeriod rho) x :=
    W.isHException_of_mem_next_of_recentered hFcenter
      G.partition hGmem x hxException
  have hyExceptionOld : G.partition.IsHException
      (W.partition.tailPeriod rho) y := by
    obtain ⟨d, hd⟩ := hxExceptionG
    refine ⟨d, ?_⟩
    intro hyMem
    apply hd
    rw [← hyQuot]
    exact hyMem
  have hGdata := (W.transition.mem_next_upsilon_iff G.partition).1 hGmem
  have htail : G.partition.tailSumset rho = W.partition.tailSumset rho :=
    hGdata.2.1.trans W.inLambda.2.1.symm
  have hperiod : G.partition.tailPeriod rho =
      W.partition.tailPeriod rho := by
    unfold Theorem21SetPartition.tailPeriod
    rw [htail]
  have hyException : G.partition.IsHException
      (G.partition.tailPeriod rho) y := by
    rw [hperiod]
    exact hyExceptionOld
  have h35 := G.next_tail_deficit_of_exception_at_rho y
    (by simpa only [q] using hyCell) hyException
  have hKbot : G.partition.tailPeriod (rho + 1) ≠ ⊥ :=
    G.partition.tailPeriod_ne_bot_of_deficit h35
  have hKtop : G.partition.tailPeriod (rho + 1) ≠ ⊤ := by
    intro htop
    apply hfail'
    exact nonempty_gmoTheoremESourceOutput_of_tailPeriod_eq_top
      G.partition G.admissible htop
  refine ⟨sigma, G, y, rfl, ?_, hyException, h35, hKbot,
    lt_top_iff_ne_top.mpr hKtop⟩
  simpa only [q] using hyCell

/-- Complete successor step of dissertation Lemma 5 in the doubled branch.
The new stage is selected afresh from the recentered `Upsilon_{rho+1}`:
`G.next` is the actual previous state, and `Fnext` comes from a new call to
Definition 1 at `rho+1`.  Earlier periods and exceptions are transported
through the genuine source chain, not through the obsolete pre-recentering
choice. -/
theorem FactorForm.exists_reindexed_succ
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) :
    ∃ sigma : Equiv.Perm (Fin n),
      Nonempty (FactorForm (I.reindex sigma) (rho + 1)) := by
  classical
  obtain ⟨sigma, G, y, hGchosen, hyCell, hyException,
      h35, hKbot, hKtop⟩ :=
    F.exists_reindexed_next_deficit_proper hfail
  have hfail' : ¬ Nonempty
      (GMOTheoremESourceOutput (I.reindex sigma)) := by
    rintro ⟨out⟩
    exact hfail ⟨out.inverseReindex sigma⟩
  let chainSucc : Definition1SourceChain
      (I.reindex sigma) (rho + 1) G.next :=
    Definition1SourceChain.next G.chain G.next G.F G.transition
  obtain ⟨next2, Fnext, step2⟩ :=
    exists_definition1Transition (rho + 1) G.next
  have hGmem : G.partition ∈ G.next.upsilon := by
    rw [hGchosen]
    exact G.next.chosen_mem
  have hrangeSucc : rho + 1 + 2 ≤ n := by
    have htwo := G.partition.two_le_tail_length_of_deficit
      (s := rho + 1) (by have := G.range; omega) h35
    omega
  let Wsucc : WeakFactorForm (I.reindex sigma) (rho + 1) := {
    range := hrangeSucc
    partition := Fnext
    admissible := chainSucc.admissible_of_mem Fnext step2.F_mem_previous
    previous := G.next
    chain := chainSucc
    next := next2
    F := Fnext
    transition := step2
    partition_inLambda :=
      ⟨step2.F_mem_previous, step2.F_tail_fixed, rfl⟩
    tail_actual := by
      intro s hs
      by_cases hsr : s = rho + 1
      · subst s
        have htail : Fnext.tailSumset (rho + 1) =
            G.partition.tailSumset (rho + 1) := by
          calc
            Fnext.tailSumset (rho + 1) =
                G.next.chosen.tailSumset (rho + 1) := step2.F_tail_fixed
            _ = G.partition.tailSumset (rho + 1) := by rw [hGchosen]
        have hperiod : Fnext.tailPeriod (rho + 1) =
            G.partition.tailPeriod (rho + 1) := by
          unfold Theorem21SetPartition.tailPeriod
          rw [htail]
        rw [hperiod]
        exact ⟨bot_lt_iff_ne_bot.mpr hKbot, hKtop⟩
      · have hslt : s < rho + 1 := by omega
        have htail := chainSucc.tailSumset_eq_of_mem Fnext G.partition
          step2.F_mem_previous hGmem hslt
        have hperiod : Fnext.tailPeriod s = G.partition.tailPeriod s := by
          unfold Theorem21SetPartition.tailPeriod
          rw [htail]
        rw [hperiod]
        exact G.tail_actual s (by omega)
    leading_exception := by
      intro c hc
      have hcr : c.val ≤ rho := by omega
      by_cases hceq : c.val = rho
      · have hqmem : QuotientAddGroup.mk'
              (G.partition.tailPeriod rho) y ∈
            quotientLayer (G.partition.tailPeriod rho)
              (G.partition.valueCell c) := by
          have hcfin : c = ⟨rho, by have := F.range; omega⟩ := by
            apply Fin.ext
            exact hceq
          rw [hcfin]
          exact (mem_quotientLayer_iff _ _ _).2 ⟨y, hyCell, rfl⟩
        have hqeq := chainSucc.quotientLayer_eq_of_mem
          G.partition Fnext hGmem step2.F_mem_previous
          (j := rho) (by omega) c
        have hqmemF : QuotientAddGroup.mk'
              (G.partition.tailPeriod rho) y ∈
            quotientLayer (G.partition.tailPeriod rho)
              (Fnext.valueCell c) := by
          rw [← hqeq]
          exact hqmem
        obtain ⟨z, hzCell, hzQuot⟩ :=
          (mem_quotientLayer_iff (G.partition.tailPeriod rho)
            (Fnext.valueCell c) _).1 hqmemF
        have hzExceptionOld : Fnext.IsHException
            (G.partition.tailPeriod rho) z := by
          obtain ⟨d, hd⟩ := hyException
          refine ⟨d, ?_⟩
          intro hzMem
          have hqeqd := chainSucc.quotientLayer_eq_of_mem
            G.partition Fnext hGmem step2.F_mem_previous
            (j := rho) (by omega) d
          apply hd
          rw [hqeqd]
          rw [← hzQuot]
          exact hzMem
        have htail := chainSucc.tailSumset_eq_of_mem Fnext G.partition
          step2.F_mem_previous hGmem (j := rho) (by omega)
        have hperiod : Fnext.tailPeriod rho =
            G.partition.tailPeriod rho := by
          unfold Theorem21SetPartition.tailPeriod
          rw [htail]
        refine ⟨z, hzCell, ?_⟩
        rw [hceq, hperiod]
        exact hzExceptionOld
      · have hclt : c.val < rho := by omega
        obtain ⟨x, hxCell, hxException⟩ := G.leading_exception c hclt
        have hqmem : QuotientAddGroup.mk'
              (G.partition.tailPeriod c.val) x ∈
            quotientLayer (G.partition.tailPeriod c.val)
              (G.partition.valueCell c) :=
          (mem_quotientLayer_iff _ _ _).2 ⟨x, hxCell, rfl⟩
        have hqeq := chainSucc.quotientLayer_eq_of_mem
          G.partition Fnext hGmem step2.F_mem_previous
          (j := c.val) (by omega) c
        have hqmemF : QuotientAddGroup.mk'
              (G.partition.tailPeriod c.val) x ∈
            quotientLayer (G.partition.tailPeriod c.val)
              (Fnext.valueCell c) := by
          rw [← hqeq]
          exact hqmem
        obtain ⟨z, hzCell, hzQuot⟩ :=
          (mem_quotientLayer_iff (G.partition.tailPeriod c.val)
            (Fnext.valueCell c) _).1 hqmemF
        have hzExceptionOld : Fnext.IsHException
            (G.partition.tailPeriod c.val) z := by
          obtain ⟨d, hd⟩ := hxException
          refine ⟨d, ?_⟩
          intro hzMem
          have hqeqd := chainSucc.quotientLayer_eq_of_mem
            G.partition Fnext hGmem step2.F_mem_previous
            (j := c.val) (by omega) d
          apply hd
          rw [hqeqd]
          rw [← hzQuot]
          exact hzMem
        have htail := chainSucc.tailSumset_eq_of_mem Fnext G.partition
          step2.F_mem_previous hGmem (j := c.val) (by omega)
        have hperiod : Fnext.tailPeriod c.val =
            G.partition.tailPeriod c.val := by
          unfold Theorem21SetPartition.tailPeriod
          rw [htail]
        refine ⟨z, hzCell, ?_⟩
        rw [hperiod]
        exact hzExceptionOld
  }
  exact ⟨sigma, ⟨Wsucc.toFactorForm
    (not_nonempty_trivialConclusion_of_no_sourceOutput hfail')⟩⟩

/-- If the stage-zero tail stabilizer is trivial, the full-layer DGM bound
is already the scalar CDT conclusion.  Value-injectivity of each labelled
cell rules out doubled classes modulo `bot`. -/
theorem nonempty_trivialConclusion_of_tailPeriod_zero_eq_bot
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (P : Theorem21SetPartition xs n seed.card)
    (hadmissible : GMOReplacementAdmissible I P)
    (hbot : P.tailPeriod 0 = ⊥) :
    Nonempty (GMOTheoremETrivialConclusion I) := by
  classical
  have hstab : AddAction.stabilizer A (P.sumset : Set A) = ⊥ := by
    simpa [Theorem21SetPartition.tailPeriod,
      Theorem21SetPartition.tailSumset,
      Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.sumset] using hbot
  have hno : ∀ x : A, ¬ P.IsHDoubledException
      (AddAction.stabilizer A (P.sumset : Set A)) x := by
    intro x hx
    obtain ⟨_hex, q, hxq, y, hyq, hyx, hyquot⟩ := hx
    have hyxEq : y = x := by
      apply sub_eq_zero.mp
      have hsub := QuotientAddGroup.eq_iff_sub_mem.mp hyquot
      rw [hstab] at hsub
      simpa using hsub
    exact hyx hyxEq
  have hcard := P.theoremE_card_lower_of_no_doubled hno
  let out : GMOTheoremEOutput xs seed n := {
    partition := P
    H := ⊥
    periodic := bot_le
    card_lower := by simpa [hstab] using hcard
    unused_in_core := by intro h; exact (h rfl).elim
  }
  have hlen : n ≤ seed.card := by
    have hmass := length_le_sum_layer_card P.valueCells
      P.valueCells_nonempty
    rw [P.length_valueCells] at hmass
    simpa [Theorem21SetPartition.valueCells, List.map_ofFn,
      List.sum_ofFn, P.sum_card_valueCell] using hmass
  exact ⟨{
    partition := P
    admissible := hadmissible
    card_lower := out.card_lower_of_H_eq_bot rfl hlen
  }⟩

/-- Under failure of the literal source theorem, Definition 1 supplies the
honest zero-factor base whenever at least two cells are present. -/
theorem exists_factorForm_zero_of_no_sourceOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (htwo : 2 ≤ n)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) :
    Nonempty (FactorForm I 0) := by
  classical
  obtain ⟨previous, valid⟩ := exists_definition1InitialStateUnder I
  obtain ⟨next, P, step⟩ := exists_definition1Transition 0 previous
  have hPadmissible : GMOReplacementAdmissible I P :=
    ((valid.mem_upsilon_iff P).1 step.F_mem_previous).1
  have hPtail : P.tailSumset 0 = previous.chosen.tailSumset 0 :=
    step.F_tail_fixed
  have hPperiod : P.tailPeriod 0 =
      previous.chosen.tailPeriod 0 := by
    unfold Theorem21SetPartition.tailPeriod
    rw [hPtail]
  have hbot : P.tailPeriod 0 ≠ ⊥ := by
    intro hb
    apply hfail
    exact (nonempty_trivialConclusion_of_tailPeriod_zero_eq_bot
      P hPadmissible hb).elim fun trivial ↦ ⟨trivial.toSourceOutput⟩
  have htop : P.tailPeriod 0 ≠ ⊤ := by
    intro ht
    exact hfail (nonempty_gmoTheoremESourceOutput_of_tailPeriod_eq_top
      P hPadmissible ht)
  let W : WeakFactorForm I 0 := {
    range := by omega
    partition := P
    admissible := hPadmissible
    previous := previous
    chain := Definition1SourceChain.initial previous valid
    next := next
    F := P
    transition := step
    partition_inLambda :=
      ⟨step.F_mem_previous, step.F_tail_fixed, rfl⟩
    tail_actual := by
      intro r hr
      have hr0 : r = 0 := by omega
      subst r
      exact ⟨bot_lt_iff_ne_bot.mpr hbot, lt_top_iff_ne_top.mpr htop⟩
    leading_exception := by
      intro c hc
      omega
  }
  exact ⟨W.toFactorForm
    (not_nonempty_trivialConclusion_of_no_sourceOutput hfail)⟩

/-- Iterating the proved Lemma-5 successor strictly decreases the remaining
tail length, so a factor form cannot coexist with failure of the literal
source output.  Every reindexing step transports failure by inverse
reindexing the hypothetical output. -/
theorem FactorForm.false_of_no_sourceOutput
    {xs : List A} {seed : Selection xs} {n rho : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (F : FactorForm I rho)
    (hfail : ¬ Nonempty (GMOTheoremESourceOutput I)) : False := by
  obtain ⟨sigma, ⟨Fs⟩⟩ := F.exists_reindexed_succ hfail
  have hfail' : ¬ Nonempty
      (GMOTheoremESourceOutput (I.reindex sigma)) := by
    rintro ⟨out⟩
    exact hfail ⟨out.inverseReindex sigma⟩
  exact Fs.false_of_no_sourceOutput hfail'
termination_by n - rho
decreasing_by
  have := F.range
  omega

omit [Fintype A] in
/-- For one cell the full-layer sumset is that cell itself, whose value map
is injective on exactly the selected labelled occurrences. -/
theorem nonempty_trivialConclusion_of_n_eq_one
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (hn : n = 1) :
    Nonempty (GMOTheoremETrivialConclusion I) := by
  classical
  subst n
  let q : Fin 1 := ⟨0, by omega⟩
  have htailOne : I.initial.tailSumset 1 = ({0} : Finset A) := by
    simp [Theorem21SetPartition.tailSumset,
      Theorem21SetPartition.tailValueCells,
      Theorem21SetPartition.valueCells, fullLayerSumSpectrum]
  have hsumset : I.initial.sumset = I.initial.valueCell q := by
    have hrec := I.initial.tailSumset_eq_valueCell_add_succ q
    rw [htailOne] at hrec
    change I.initial.tailSumset 0 =
      I.initial.valueCell q + (0 : Finset A) at hrec
    have htailZero : I.initial.tailSumset 0 = I.initial.sumset := by
      simp [Theorem21SetPartition.tailSumset,
        Theorem21SetPartition.tailValueCells,
        Theorem21SetPartition.sumset]
    rw [htailZero, add_zero] at hrec
    exact hrec
  have hcellCard : (I.initial.valueCell q).card = seed.card := by
    have hsum := I.initial.sum_card_valueCell
    have hq : q = (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hq]
    simpa using hsum
  have hseedPos : 0 < seed.card := by
    rw [← hcellCard]
    exact Finset.card_pos.mpr (I.initial.valueCells_nonempty
      (I.initial.valueCell q) (by
        rw [Theorem21SetPartition.valueCells]
        exact List.mem_ofFn.mpr ⟨q, rfl⟩))
  refine ⟨{
    partition := I.initial
    admissible := I.initial_admissible
    card_lower := ?_
  }⟩
  rw [hsumset, hcellCard]
  omega

/-- The source-faithful ordinary Theorem E, now with no provider or external
boundary: the one-cell case is direct, while every larger positive `n`
would otherwise generate an impossible finite chain of factor forms. -/
theorem gmoTheoremESourceStatement : GMOTheoremESourceStatement A := by
  intro xs seed n I hn
  by_contra hfail
  have hfail' : ¬ Nonempty (GMOTheoremESourceOutput I) := hfail
  by_cases hone : n = 1
  · exact hfail' ((nonempty_trivialConclusion_of_n_eq_one I hone).map
      GMOTheoremETrivialConclusion.toSourceOutput)
  · have htwo : 2 ≤ n := by omega
    obtain ⟨F0⟩ := exists_factorForm_zero_of_no_sourceOutput htwo hfail'
    exact F0.false_of_no_sourceOutput hfail'

omit [AddCommGroup A] [Fintype A] in
/-- The selected-subsequence coloring now supplies the literal source input,
including exact labelled support rather than only its cardinality. -/
theorem exists_gmoTheoremEInput
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (hcap : SelectionMultiplicityAtMost xs seed n)
    (hlen : n ≤ seed.card) :
    Nonempty (GMOTheoremEInput xs seed n) := by
  classical
  obtain ⟨P, hsupport⟩ :=
    exists_selected_theorem21SetPartition xs seed n hcap hlen
  let anchor : Fin n → Occurrence xs := fun c ↦
    Classical.choose (P.cells_nonempty c)
  refine ⟨{
    initial := P
    initial_support := ?_
    anchor := anchor
    anchor_mem := ?_
  }⟩
  · exact hsupport
  · intro c
    exact Classical.choose_spec (P.cells_nonempty c)

/-- Unconditional projected Theorem E.  The zero-cell case is the empty
Definition-1 layer, whose stabilizer is top; positive `n` uses the fully
proved source-faithful theorem and then forgets its base-family data. -/
theorem gmoTheoremEStatement : GMOTheoremEStatement A := by
  intro xs seed n hcap hlen
  obtain ⟨I⟩ := exists_gmoTheoremEInput xs seed n hcap hlen
  by_cases hn : 0 < n
  · obtain ⟨out⟩ := gmoTheoremESourceStatement xs seed n I hn
    exact ⟨out.toProjected⟩
  · have hn0 : n = 0 := by omega
    have hbot : I.initial.tailPeriod 0 = ⊥ := by
      subst n
      simp [Theorem21SetPartition.tailPeriod,
        Theorem21SetPartition.tailSumset,
        Theorem21SetPartition.tailValueCells,
        Theorem21SetPartition.valueCells, fullLayerSumSpectrum]
    obtain ⟨trivial⟩ :=
      nonempty_trivialConclusion_of_tailPeriod_zero_eq_bot
        I.initial I.initial_admissible hbot
    exact ⟨trivial.toSourceOutput.toProjected⟩

/-- The well-founded cardinal data used by the genuine proper-subgroup
induction in Theorems 2.4/2.5. -/
structure GMOProperSubgroupInductionData (H : AddSubgroup A) : Prop where
  nontrivial : H ≠ ⊥
  proper : H < ⊤
  factorization : Nat.card A = Nat.card (A ⧸ H) * Nat.card H
  subgroup_lt : Nat.card H < Nat.card A
  quotient_lt : Nat.card (A ⧸ H) < Nat.card A

/-- Every proper nontrivial subgroup gives strict descent on both recursive
groups; no external induction provider is involved. -/
theorem gmoProperSubgroupInductionData
    (H : AddSubgroup A) (hHbot : H ≠ ⊥) (hHtop : H < ⊤) :
    GMOProperSubgroupInductionData H := by
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hHtwo : 2 ≤ Nat.card H := by
    letI : Fintype H := Fintype.ofFinite H
    by_contra hnot
    have hsub : Subsingleton H :=
      Fintype.card_le_one_iff_subsingleton.mp (by
        simpa [Nat.card_eq_fintype_card] using (Nat.lt_of_not_ge hnot))
    apply hHbot
    ext x
    constructor
    · intro hx
      have heq : (⟨x, hx⟩ : H) = 0 := hsub.elim _ _
      simpa using congrArg Subtype.val heq
    · intro hx
      subst x
      exact H.zero_mem
  have hQtwo : 2 ≤ Nat.card (A ⧸ H) :=
    two_le_natCard_quotient_of_lt_top H hHtop
  refine {
    nontrivial := hHbot
    proper := hHtop
    factorization := hfactor
    subgroup_lt := ?_
    quotient_lt := ?_
  }
  · rw [hfactor]
    nlinarith [Nat.card_pos (α := A ⧸ H)]
  · rw [hfactor]
    nlinarith [Nat.card_pos (α := H)]

/-- The honest **odd-prime** p-group specialization targeted by the frozen
thirteen-page final manuscript (PR #7 explicitly excludes `2`-groups).
Recursive width is measured by the canonical ordinary Davenport constant,
not by an unavailable general invariant-factor transport.  This is
deliberately not named `GMOTheorem21Statement`. -/
def OrdinaryGMOPGroupSourceStatement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (p : ℕ), Fact p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ (xs : List A) (n : ℕ),
      Nat.card A ≤ n →
      n + ordinaryDavenportValue A - 1 ≤ xs.length →
      Nonempty (OrdinaryGMOSourceOutput xs n)

omit [Fintype A] in
/-- The labelled source splits exactly into occurrences inside and outside
one additive coset.  This is the occurrence-faithful bookkeeping used by
Claim B and the maximal-subgroup replacement step. -/
theorem occurrencesInAddCoset_union_compl
    (xs : List A) (H : AddSubgroup A) (alpha : A) :
    occurrencesInAddCoset xs H alpha ∪
        ((Finset.univ : Selection xs) \ occurrencesInAddCoset xs H alpha) =
      Finset.univ := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

omit [Fintype A] in
theorem occurrencesInAddCoset_disjoint_compl
    (xs : List A) (H : AddSubgroup A) (alpha : A) :
    Disjoint (occurrencesInAddCoset xs H alpha)
      ((Finset.univ : Selection xs) \ occurrencesInAddCoset xs H alpha) := by
  classical
  exact Finset.disjoint_sdiff

omit [Fintype A] in
theorem card_occurrencesInAddCoset_add_compl
    (xs : List A) (H : AddSubgroup A) (alpha : A) :
    (occurrencesInAddCoset xs H alpha).card +
        ((Finset.univ : Selection xs) \
          occurrencesInAddCoset xs H alpha).card = xs.length := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (occurrencesInAddCoset xs H alpha))
  rw [Finset.card_univ] at h
  simpa [Nat.add_comm] using h

/-- Push a labelled occurrence selection through a list map. -/
noncomputable def mapSelection
    {X B : Type*} (f : X → B) (s : List X) (I : Selection s) :
    Selection (s.map f) := by
  classical
  exact I.map (ConcreteGDihedral.mapOccurrenceEquiv f s).toEmbedding

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem card_mapSelection {X B : Type*} (f : X → B)
    (s : List X) (I : Selection s) :
    (mapSelection f s I).card = I.card := by
  classical
  simp [mapSelection]

omit [Fintype A] in
/-- Quotient displacement from the chosen coset representative. -/
noncomputable def quotientDisplacement
    (H : AddSubgroup A) (alpha : A) : A → A ⧸ H :=
  fun x ↦ QuotientAddGroup.mk' H (x - alpha)

theorem quotientDisplacement_eq_zero_iff
    (H : AddSubgroup A) (alpha x : A) :
    quotientDisplacement H alpha x = 0 ↔ x ∈ addCosetFinset H alpha := by
  unfold quotientDisplacement
  constructor
  · intro hx
    apply (mem_addCosetFinset_iff H alpha x).2
    have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hx
    simpa using hmem
  · intro hx
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hmem := (mem_addCosetFinset_iff H alpha x).1 hx
    simpa using hmem

/-- The quotient image of every labelled occurrence outside `alpha+H` is
nonzero.  The occurrence equivalence preserves its original index. -/
theorem occurrenceValue_mapSelection_compl_ne_zero
    (xs : List A) (H : AddSubgroup A) (alpha : A)
    (j : Occurrence
      (xs.map (quotientDisplacement H alpha)))
    (hj : j ∈ mapSelection (quotientDisplacement H alpha) xs
      ((Finset.univ : Selection xs) \
        occurrencesInAddCoset xs H alpha)) :
    occurrenceValue (xs.map (quotientDisplacement H alpha)) j ≠ 0 := by
  classical
  unfold mapSelection at hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
  have hvalue := ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
    (quotientDisplacement H alpha) xs i
  change occurrenceValue (xs.map (quotientDisplacement H alpha))
      (ConcreteGDihedral.mapOccurrenceEquiv
        (quotientDisplacement H alpha) xs i) ≠ 0
  rw [hvalue]
  intro hz
  have hcoset := (quotientDisplacement_eq_zero_iff H alpha
    (occurrenceValue xs i)).1 hz
  exact (Finset.mem_sdiff.mp hi).2
    ((mem_occurrencesInAddCoset_iff xs H alpha i).2
      ((mem_addCosetFinset_iff H alpha (occurrenceValue xs i)).1 hcoset))

/-- A periodic common core with quotient-coset count zero is empty. -/
theorem Theorem21SetPartition.commonCore_eq_empty_of_count_eq_zero
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (hN : P.commonCosetCount H = 0) :
    P.commonCore H = ∅ := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hcoset : addCosetFinset H x ⊆ P.commonCore H := by
    intro y hy
    have hyH := (mem_addCosetFinset_iff H x y).1 hy
    have hadd := P.add_mem_commonCore H hyH hx
    simpa [sub_add_cancel] using hadd
  have hcard : Nat.card H ≤ (P.commonCore H).card := by
    simpa using Finset.card_le_card hcoset
  have hdiv : 1 ≤ (P.commonCore H).card / Nat.card H :=
    (Nat.le_div_iff_mul_le Nat.card_pos).2 (by simpa using hcard)
  unfold Theorem21SetPartition.commonCosetCount at hN
  omega

/-- The `N=0` endpoint of Section 5 is already the direct large alternative;
no Claim-B or quotient induction is needed. -/
theorem GMOTheoremESourceOutput.largeAlternative_of_commonCosetCount_eq_zero
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hlen : n ≤ seed.card)
    (hN : out.partition.commonCosetCount out.H = 0) :
    GMOTheorem21LargeAlternative xs seed n out.partition := by
  classical
  have hcore := out.partition.commonCore_eq_empty_of_count_eq_zero out.H hN
  have he : out.partition.exceptionDefect out.H = seed.card := by
    simp [Theorem21SetPartition.exceptionDefect,
      Theorem21SetPartition.cellExceptionDefect, hcore,
      out.partition.sum_card_valueCell]
  have hbound := out.card_lower
  rw [hN, he] at hbound
  have hcoeff : seed.card - n + 1 ≤
      ((0 * n + seed.card + 1) - n) * Nat.card out.H := by
    have hbase : (0 * n + seed.card + 1) - n = seed.card - n + 1 := by
      omega
    rw [hbase]
    have hone : 1 ≤ Nat.card out.H := Nat.card_pos
    simpa using Nat.mul_le_mul_left (seed.card - n + 1) hone
  refine ⟨(min_le_right (Nat.card A) (seed.card - n + 1)).trans ?_⟩
  exact hcoeff.trans hbound

/-- Ordinary Proposition F in normalized ambient-group form: two finite
subsets whose cardinalities sum to more than the group order have full
sumset. -/
theorem add_eq_univ_of_natCard_lt_card_add_card
    [DecidableEq A]
    (B C : Finset A) (hcard : Nat.card A < B.card + C.card) :
    (B + C : Finset A) = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  let R : Finset A := C.image fun c ↦ x - c
  have hRcard : R.card = C.card := by
    apply Finset.card_image_of_injective
    intro c d h
    exact sub_right_injective h
  have hinter : (B ∩ R).Nonempty := by
    by_contra hnone
    have hdisj : Disjoint B R := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hnone)
    have hunion : B.card + R.card = (B ∪ R).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    have hle : (B ∪ R).card ≤ Nat.card A := by
      simpa using Finset.card_le_univ (B ∪ R)
    rw [hRcard] at hunion
    omega
  obtain ⟨b, hbI⟩ := hinter
  have ⟨hbB, hbR⟩ := Finset.mem_inter.mp hbI
  obtain ⟨c, hcC, hbc⟩ := Finset.mem_image.mp hbR
  apply Finset.mem_add.mpr
  refine ⟨b, hbB, c, hcC, ?_⟩
  rw [← hbc]
  abel

/-- Claim-B Case 1, equation (13), in the ordinary-weight specialization:
two slices contained in the same subgroup and having more than one subgroup
order of total cardinality fill that subgroup under addition.  This is the
ambient-`A` form needed by the occurrence setpartition, so no multiplicity
or subtype coercion is discarded. -/
theorem add_eq_dgmSubgroupFinset_of_subsets_of_natCard_lt_card_add_card
    [DecidableEq A]
    (H : AddSubgroup A) (B C : Finset A)
    (hB : B ⊆ dgmSubgroupFinset H)
    (hC : C ⊆ dgmSubgroupFinset H)
    (hcard : Nat.card H < B.card + C.card) :
    B + C = dgmSubgroupFinset H := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp hx
    rw [mem_dgmSubgroupFinset_iff]
    exact H.add_mem
      ((mem_dgmSubgroupFinset_iff H b).1 (hB hb))
      ((mem_dgmSubgroupFinset_iff H c).1 (hC hc))
  · intro x hx
    let R : Finset A := C.image fun c ↦ x - c
    have hxH : x ∈ H := (mem_dgmSubgroupFinset_iff H x).1 hx
    have hRcard : R.card = C.card := by
      apply Finset.card_image_of_injective
      intro c d h
      exact sub_right_injective h
    have hR : R ⊆ dgmSubgroupFinset H := by
      intro r hr
      obtain ⟨c, hcC, rfl⟩ := Finset.mem_image.mp hr
      rw [mem_dgmSubgroupFinset_iff]
      exact H.sub_mem hxH
        ((mem_dgmSubgroupFinset_iff H c).1 (hC hcC))
    have hinter : (B ∩ R).Nonempty := by
      by_contra hnone
      have hdisj : Disjoint B R := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hnone)
      have hunion : B.card + R.card = (B ∪ R).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      have hunionSub : B ∪ R ⊆ dgmSubgroupFinset H :=
        Finset.union_subset hB hR
      have hle : (B ∪ R).card ≤ Nat.card H := by
        simpa using Finset.card_le_card hunionSub
      rw [hRcard] at hunion
      omega
    obtain ⟨b, hbI⟩ := hinter
    have ⟨hbB, hbR⟩ := Finset.mem_inter.mp hbI
    obtain ⟨c, hcC, hbc⟩ := Finset.mem_image.mp hbR
    apply Finset.mem_add.mpr
    refine ⟨b, hbB, c, hcC, ?_⟩
    rw [← hbc]
    abel

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
