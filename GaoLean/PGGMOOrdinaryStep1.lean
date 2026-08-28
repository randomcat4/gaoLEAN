import GaoLean.PGGMOClaimBTarget

/-!
# Ordinary GMO Step 1: an occurrence-faithful extension package

This is the labelled version of Step 1 in the proof of Corollary 5.1 of
Gao--Geroldinger--Schmid.  The package never stores the desired conclusion.
It stores a genuine full-spectrum core in one affine subgroup coset and a
disjoint reserve of genuine occurrences in that same coset.  A maximal
zero-sum block in the quotient, padded only by the reserve, then extends the
core to the prescribed length.

The reserve has canonical size `d*(A/H)`.  The one-unit shift between `d*`
and the Davenport constant is kept explicit in the maximal-block lemma.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientFintype (H : AddSubgroup A) :
    Fintype (A ⧸ H) := Fintype.ofFinite (A ⧸ H)

section MaximalQuotientBlock

variable {X : Type v} [Fintype X] [DecidableEq X]
variable {B : Type u} [AddCommGroup B]

/-- A Davenport bound applied to a finite labelled pool.  The returned block
is a subset of the original labels, not merely a sublist of their values. -/
theorem exists_nonempty_zeroSum_finset_subset
    (R : Finset X) (f : X → B) (D : ℕ)
    (hD : OrdinaryDavenportAtMost B D) (hcard : D ≤ R.card) :
    ∃ J : Finset X, J.Nonempty ∧ J ⊆ R ∧ (∑ x ∈ J, f x) = 0 := by
  classical
  let w : List B := R.toList.map f
  have hwlen : D ≤ w.length := by simpa [w] using hcard
  obtain ⟨I, hIne, hIsum⟩ := ordinaryDavenportAtLeast_of_atMost hD w hwlen
  let source : Occurrence w ↪ X :=
    { toFun := fun i => R.toList.get
        ⟨i.1, by simpa [w] using i.2⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact R.nodup_toList.injective_get hij }
  let J : Finset X := I.map source
  have hsource_mem (i : Occurrence w) : source i ∈ R := by
    exact Finset.mem_toList.mp (List.get_mem R.toList _)
  have hvalue (i : Occurrence w) : f (source i) = occurrenceValue w i := by
    simp [source, w, occurrenceValue, List.get_eq_getElem]
  refine ⟨J, ?_, ?_, ?_⟩
  · simpa [J] using hIne
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    exact hsource_mem i
  · simpa [J, Finset.sum_map, hvalue] using hIsum

/-- A maximum-cardinality zero-sum block leaves fewer than `D` labels.
This is the exact ordinary quotient block used in Step 1. -/
theorem exists_zeroSum_subset_remainder_lt_davenport
    (R : Finset X) (f : X → B) (D : ℕ)
    (hD : OrdinaryDavenportAtMost B D) :
    ∃ I : Finset X,
      I ⊆ R ∧ (∑ x ∈ I, f x) = 0 ∧ R.card - I.card < D := by
  classical
  let good : Finset (Finset X) := Finset.univ.filter fun I =>
    I ⊆ R ∧ (∑ x ∈ I, f x) = 0
  have hempty : (∅ : Finset X) ∈ good := by simp [good]
  obtain ⟨I, hIgood, hImax⟩ := Finset.exists_max_image good
    (fun J => J.card) ⟨∅, hempty⟩
  have hIsub : I ⊆ R := (Finset.mem_filter.mp hIgood).2.1
  have hIz : (∑ x ∈ I, f x) = 0 := (Finset.mem_filter.mp hIgood).2.2
  refine ⟨I, hIsub, hIz, ?_⟩
  by_contra hnot
  have hrem : D ≤ (R \ I).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIsub]
    omega
  obtain ⟨J, hJne, hJsub, hJz⟩ :=
    exists_nonempty_zeroSum_finset_subset (R \ I) f D hD hrem
  have hJsubR : J ⊆ R := fun x hx => (Finset.mem_sdiff.mp (hJsub hx)).1
  have hdis : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro x hxI hxJ
    exact (Finset.mem_sdiff.mp (hJsub hxJ)).2 hxI
  have hUnionGood : I ∪ J ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.union_subset hIsub hJsubR, ?_⟩
    rw [Finset.sum_union hdis, hIz, hJz, zero_add]
  have hmax := hImax _ hUnionGood
  rw [Finset.card_union_of_disjoint hdis] at hmax
  have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
  omega

/-- Pad the omitted part of a maximal quotient zero-sum block by the same
number of genuine zero-valued reserve labels.  The output has exactly the
cardinality of the original pool. -/
theorem exists_zeroSum_padded_selection
    (pool reserve : Finset X) (f : X → B) (D : ℕ)
    (hD : OrdinaryDavenportAtMost B D)
    (hdis : Disjoint pool reserve)
    (hreserveZero : ∀ x ∈ reserve, f x = 0)
    (hreserveCard : D - 1 ≤ reserve.card) :
    ∃ tail : Finset X,
      tail ⊆ pool ∪ reserve ∧ tail.card = pool.card ∧
        (∑ x ∈ tail, f x) = 0 := by
  classical
  obtain ⟨I, hIsub, hIz, hrem⟩ :=
    exists_zeroSum_subset_remainder_lt_davenport pool f D hD
  let k := pool.card - I.card
  have hk : k ≤ reserve.card := by
    dsimp only [k]
    omega
  obtain ⟨F, hFsub, hFcard⟩ :=
    Finset.exists_subset_card_eq (s := reserve) hk
  have hIF : Disjoint I F :=
    (Finset.Disjoint.mono hIsub hFsub hdis)
  refine ⟨I ∪ F, ?_, ?_, ?_⟩
  · exact Finset.union_subset
      (hIsub.trans (Finset.subset_union_left))
      (hFsub.trans (Finset.subset_union_right))
  · rw [Finset.card_union_of_disjoint hIF, hFcard]
    dsimp only [k]
    exact Nat.sub_add_cancel (Finset.card_le_card hIsub)
  · rw [Finset.sum_union hIF, hIz]
    have hFz : (∑ x ∈ F, f x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hreserveZero x (hFsub hx)
    rw [hFz, zero_add]

end MaximalQuotientBlock

/-- The irreducible mathematical data delivered by the recursive Step 2.
`core_full` is a full `|H|`-spectrum on a literal labelled core.  It is not
the final prescribed-length conclusion. -/
structure OrdinaryGMOStep1Core (xs : List A) where
  H : AddSubgroup A
  beta : A
  container : Selection xs
  core : Selection xs
  core_subset_container : core ⊆ container
  container_in_coset : ∀ i ∈ container,
    occurrenceValue xs i ∈ addCosetFinset H beta
  container_card_lower :
    Nat.card H + pGroupDStar A ≤ container.card
  core_card : core.card = Nat.card H + pGroupDStar H
  core_full : ∀ h : A, h ∈ H →
    ∃ J : Selection xs,
      J ⊆ core ∧ J.card = Nat.card H ∧
        (∑ i ∈ J, occurrenceValue xs i) = Nat.card H • beta + h

/-- Step 1 chooses, from the excess of the affine container over its core, a
fixed genuine reserve of `d*(A/H)` labels. -/
structure OrdinaryGMOStep1Package (xs : List A)
    extends OrdinaryGMOStep1Core xs where
  reserve : Selection xs
  reserve_subset : reserve ⊆ container \ core
  reserve_card : reserve.card = pGroupDStar (A ⧸ H)

namespace OrdinaryGMOStep1Core

/-- Canonical convolution supplies enough literal container labels to choose
the quotient reserve; no reserve-provider is assumed. -/
theorem exists_package {xs : List A} (C : OrdinaryGMOStep1Core xs) :
    Nonempty (OrdinaryGMOStep1Package xs) := by
  classical
  let available : Selection xs := C.container \ C.core
  have hcoreContainerCard : C.core.card ≤ C.container.card :=
    Finset.card_le_card C.core_subset_container
  have havailCard : available.card = C.container.card - C.core.card := by
    dsimp only [available]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr C.core_subset_container]
  have hconv := pGroupDStar_subgroup_quotient_le C.H
  have hqAvail : pGroupDStar (A ⧸ C.H) ≤ available.card := by
    rw [havailCard, C.core_card]
    omega
  obtain ⟨reserve, hreserve, hcard⟩ :=
    Finset.exists_subset_card_eq (s := available) hqAvail
  exact ⟨{
    toOrdinaryGMOStep1Core := C
    reserve := reserve
    reserve_subset := hreserve
    reserve_card := hcard
  }⟩

end OrdinaryGMOStep1Core

namespace OrdinaryGMOStep1Package

theorem reserve_in_coset {xs : List A} (P : OrdinaryGMOStep1Package xs)
    {i : Occurrence xs} (hi : i ∈ P.reserve) :
    occurrenceValue xs i ∈ addCosetFinset P.H P.beta := by
  exact P.container_in_coset i
    (Finset.mem_sdiff.mp (P.reserve_subset hi)).1

theorem disjoint_core_reserve {xs : List A}
    (P : OrdinaryGMOStep1Package xs) : Disjoint P.core P.reserve := by
  rw [Finset.disjoint_left]
  intro i hiCore hiReserve
  exact (Finset.mem_sdiff.mp (P.reserve_subset hiReserve)).2 hiCore

/-- Step 1 extender.  A pool of `n-|H|` unused labels is made quotient-zero
by a maximal Davenport block and genuine reserve padding.  Its displacement
lies in `H`, so `core_full` chooses `|H|` core labels cancelling it.  The
union is an exact occurrence selection of size `n` and sum `n • beta`. -/
theorem nonempty_target {xs : List A} (P : OrdinaryGMOStep1Package xs)
    (n : ℕ) (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  classical
  let dH := pGroupDStar P.H
  let dQ := pGroupDStar (A ⧸ P.H)
  let used : Selection xs := P.core ∪ P.reserve
  let available : Selection xs := Finset.univ \ used
  have hHn : Nat.card P.H ≤ n :=
    (natCard_addSubgroup_le_ambient P.H).trans hnA
  have husedDis : Disjoint P.core P.reserve := P.disjoint_core_reserve
  have husedCard : used.card = Nat.card P.H + dH + dQ := by
    rw [show used = P.core ∪ P.reserve by rfl,
      Finset.card_union_of_disjoint husedDis, P.core_card, P.reserve_card]
    rfl
  have havailableCard : available.card = xs.length - used.card := by
    dsimp only [available]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ used)]
    simp
  have hpoolLe : n - Nat.card P.H ≤ available.card := by
    rw [havailableCard, husedCard]
    have hconv := pGroupDStar_subgroup_quotient_le P.H
    omega
  obtain ⟨pool, hpoolSub, hpoolCard⟩ :=
    Finset.exists_subset_card_eq (s := available) hpoolLe
  let qvalue : Occurrence xs → A ⧸ P.H := fun i =>
    quotientDisplacement P.H P.beta (occurrenceValue xs i)
  have hpoolReserve : Disjoint pool P.reserve := by
    rw [Finset.disjoint_left]
    intro i hiPool hiReserve
    have hiAvail := hpoolSub hiPool
    exact (Finset.mem_sdiff.mp hiAvail).2
      (Finset.mem_union_right P.core hiReserve)
  have hreserveZero : ∀ i ∈ P.reserve, qvalue i = 0 := by
    intro i hi
    exact (quotientDisplacement_eq_zero_iff P.H P.beta
      (occurrenceValue xs i)).2 (P.reserve_in_coset hi)
  have hD := (pGroupDStar_spec (A ⧸ P.H)).1
  have hreserveEnough : (dQ + 1) - 1 ≤ P.reserve.card := by
    simp [dQ, P.reserve_card]
  obtain ⟨tail, htailSub, htailCard, htailQSum⟩ :=
    exists_zeroSum_padded_selection pool P.reserve qvalue (dQ + 1)
      hD hpoolReserve hreserveZero hreserveEnough
  have htailCore : Disjoint P.core tail := by
    rw [Finset.disjoint_left]
    intro i hiCore hiTail
    rcases Finset.mem_union.mp (htailSub hiTail) with hiPool | hiReserve
    · have hiAvail := hpoolSub hiPool
      exact (Finset.mem_sdiff.mp hiAvail).2
        (Finset.mem_union_left P.reserve hiCore)
    · exact (Finset.disjoint_left.mp husedDis) hiCore hiReserve
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i
  have htailMem : tailSum - tail.card • P.beta ∈ P.H := by
    apply QuotientAddGroup.eq_zero_iff.mp
    have hq : QuotientAddGroup.mk' P.H
        (tailSum - tail.card • P.beta) = 0 := by
      simpa [qvalue, quotientDisplacement, tailSum,
        Finset.sum_sub_distrib] using htailQSum
    exact hq
  obtain ⟨coreSel, hcoreSub, hcoreCard, hcoreSum⟩ :=
    P.core_full (-(tailSum - tail.card • P.beta))
      (P.H.neg_mem htailMem)
  have hcoreTail : Disjoint coreSel tail :=
    Finset.Disjoint.mono hcoreSub (Finset.Subset.rfl) htailCore
  refine ⟨{
    selected := coreSel ∪ tail
    card_selected := ?_
    sum_mem_target := ⟨P.beta, ?_⟩
  }⟩
  · rw [Finset.card_union_of_disjoint hcoreTail, hcoreCard, htailCard,
      hpoolCard]
    exact Nat.add_sub_of_le hHn
  · rw [Finset.sum_union hcoreTail, hcoreSum]
    have hsplit : Nat.card P.H + tail.card = n := by
      rw [htailCard, hpoolCard]
      exact Nat.add_sub_of_le hHn
    calc
      Nat.card P.H • P.beta + (-(tailSum - tail.card • P.beta)) + tailSum =
          Nat.card P.H • P.beta + tail.card • P.beta := by abel
      _ = (Nat.card P.H + tail.card) • P.beta := by
        rw [add_nsmul]
      _ = n • P.beta := by rw [hsplit]

end OrdinaryGMOStep1Package

/-- Public wrapper which chooses the canonical quotient reserve and then runs
the occurrence-faithful extender. -/
theorem OrdinaryGMOStep1Core.nonempty_target {xs : List A}
    (C : OrdinaryGMOStep1Core xs) (n : ℕ)
    (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  obtain ⟨P⟩ := C.exists_package
  exact P.nonempty_target n hnA hlen

end GaoLean

#print axioms GaoLean.exists_nonempty_zeroSum_finset_subset
#print axioms GaoLean.exists_zeroSum_subset_remainder_lt_davenport
#print axioms GaoLean.exists_zeroSum_padded_selection
#print axioms GaoLean.OrdinaryGMOStep1Core.exists_package
#print axioms GaoLean.OrdinaryGMOStep1Package.nonempty_target
#print axioms GaoLean.OrdinaryGMOStep1Core.nonempty_target
