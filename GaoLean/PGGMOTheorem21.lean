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
    Nonempty (Theorem21SetPartition xs n seed.card) := by
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
  }⟩
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
  obtain ⟨initial⟩ :=
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
  obtain ⟨initial⟩ :=
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
/-- The genuine `l = min rho q` maximal-exchange contradiction for a weak
factor form, with the source paper's `x ≠ a_q` convention made explicit as
the anchor-value hypothesis.  A wrapper can choose such a representative
from a doubled quotient class. -/
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
setpartition and anchors.  The period is the actual stabilizer, not an
arbitrary subperiod; when it is nontrivial, every unused labelled source
occurrence lies in the common core.  No unconditional `N ≥ 1` or global
no-doubled conclusion is built into this structure. -/
structure GMOTheoremESourceOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) where
  partition : Theorem21SetPartition xs n seed.card
  H : AddSubgroup A
  actual_period : H = AddAction.stabilizer A (partition.sumset : Set A)
  admissible : GMOReplacementAdmissible I partition
  card_lower :
    ((partition.commonCosetCount H * n +
        partition.exceptionDefect H + 1) - n) * Nat.card H ≤
      partition.sumset.card
  unused_mem_commonCore :
    H ≠ ⊥ → ∀ i : Occurrence xs, i ∉ partition.support →
      occurrenceValue xs i ∈ partition.commonCore H

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
  periodic := out.actual_period ▸ le_rfl
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
