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
    · simpa [hkvalue, hix]
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

/-- Regression for the placement of natural subtraction in Theorem E.

The source coefficient is `(N * n + e + 1) - n`.  Subtracting one from `N`
first is not equivalent over `Nat`: at `N = 0`, `n = 2`, `e = 2`, the faithful
coefficient is `1`, whereas the prematurely truncated expression is `3`. -/
theorem theoremE_natSub_regression :
    (((0 : ℕ) * 2 + 2 + 1) - 2 = 1) ∧
      ((0 - 1) * 2 + 2 + 1 = 3) := by
  norm_num

/-- Exact ordinary specialization of the stronger replacement theorem called
Theorem E in the source of Theorems 2.4 and 2.5. -/
structure GMOTheoremEOutput
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  partition : Theorem21SetPartition xs n seed.card
  H : AddSubgroup A
  periodic : H ≤ AddAction.stabilizer A (partition.sumset : Set A)
  card_lower :
    ((partition.commonCosetCount H * n +
        partition.exceptionDefect H + 1) - n) * Nat.card H ≤
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
