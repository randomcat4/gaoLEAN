import GaoLean.PGGMOPGroupInvariant
import GaoLean.PGGMOTheorem21

/-!
# Algebraic bridges for the ordinary GMO Claim B induction

This module contains only reusable algebraic consequences of the canonical
ordinary Davenport invariant.  It does not assert Claim B, construct a GMO
setpartition, or hide any structural provider behind a proposition parameter.

The main interfaces are:

* invariance of `pGroupDStar` under additive equivalence;
* exact and padded (`k ≥ d*`) versions of ordinary Lemma 4.2;
* the lower bound `2 ≤ d*` for a nontrivial finite abelian odd `p`-group;
* subgroup--quotient convolution inside an intermediate subgroup;
* quotient compatibility with `iteratedFinsetSum`; and
* lifting a quotient-level summand together with a full `H`-coset cover.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

section AddEquivInvariance

variable {A : Type u} {B : Type v}
  [AddCommGroup A] [AddCommGroup B]

/-- The ordinary Davenport upper property transports across an additive
equivalence.  Occurrences are preserved because `List.map` preserves the
index type, and a zero sum is pulled back through the inverse equivalence. -/
theorem ordinaryDavenportAtMost_of_addEquiv
    (e : A ≃+ B) {D : ℕ} (hD : OrdinaryDavenportAtMost A D) :
    OrdinaryDavenportAtMost B D := by
  intro s hs
  have hmapped : HasNonemptyZeroSum (s.map e.symm) := by
    apply hD
    simpa using hs
  exact hasNonemptyZeroSum_of_map_addMonoidHom
    e.symm.toAddMonoidHom e.symm.injective s hmapped

/-- Exact ordinary Davenport constants are invariant under additive
equivalence, including the lower witnesses at every smaller length. -/
theorem isOrdinaryDavenportConstant_of_addEquiv
    (e : A ≃+ B) {D : ℕ} (hD : IsOrdinaryDavenportConstant A D) :
    IsOrdinaryDavenportConstant B D := by
  refine ⟨ordinaryDavenportAtMost_of_addEquiv e hD.1, ?_⟩
  intro n hn
  obtain ⟨s, hslen, hsfree⟩ := hD.2 n hn
  refine ⟨s.map e, by simpa using hslen, ?_⟩
  intro hzero
  exact hsfree (hasNonemptyZeroSum_of_map_addMonoidHom
    e.toAddMonoidHom e.injective s hzero)

/-- The canonical `d* = D-1` is invariant under additive equivalence. -/
theorem pGroupDStar_addEquiv
    [Finite A] [Finite B] (e : A ≃+ B) :
    pGroupDStar A = pGroupDStar B := by
  have hB : IsOrdinaryDavenportConstant B (ordinaryDavenportValue A) :=
    isOrdinaryDavenportConstant_of_addEquiv e
      (ordinaryDavenportValue_spec A)
  have hvalue : ordinaryDavenportValue A = ordinaryDavenportValue B :=
    isOrdinaryDavenportConstant_unique hB
      (ordinaryDavenportValue_spec B)
  simp only [pGroupDStar, hvalue]

end AddEquivInvariance

section PaddedOrdinarySpanning

variable {B : Type u} [AddCommGroup B] [Fintype B] [DecidableEq B]

/-- Ordinary Lemma 4.2 at the canonical exact length `d*(B)`. -/
theorem iteratedFinsetSum_replicate_pGroupDStar_eq_univ
    (U : Finset B) (hzero : 0 ∈ U)
    (hgen : AddSubgroup.closure (U : Set B) = ⊤) :
    iteratedFinsetSum (List.replicate (pGroupDStar B) U) = Finset.univ := by
  have h := iteratedFinsetSum_replicate_pred_eq_univ_of_davenport
    U (ordinaryDavenportValue B) hzero hgen
    (ordinaryDavenportValue_spec B).1
  simpa only [pGroupDStar] using h

/-- Padding by zeros extends Lemma 4.2 from `d*(B)` to every exact length
`k ≥ d*(B)`. -/
theorem mem_iteratedFinsetSum_replicate_of_pGroupDStar_le
    (U : Finset B) (hzero : 0 ∈ U)
    (hgen : AddSubgroup.closure (U : Set B) = ⊤)
    (k : ℕ) (hk : pGroupDStar B ≤ k) (x : B) :
    x ∈ iteratedFinsetSum (List.replicate k U) := by
  have hx : x ∈ iteratedFinsetSum
      (List.replicate (pGroupDStar B) U) := by
    rw [iteratedFinsetSum_replicate_pGroupDStar_eq_univ U hzero hgen]
    simp
  obtain ⟨w, hwlen, hwU, hwsum⟩ :=
    (mem_iteratedFinsetSum_replicate_iff U (pGroupDStar B) x).1 hx
  let v := List.replicate (k - pGroupDStar B) (0 : B) ++ w
  apply (mem_iteratedFinsetSum_replicate_iff U k x).2
  refine ⟨v, ?_, ?_, ?_⟩
  · simp [v, hwlen]
    omega
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · have hy0 : y = 0 := List.eq_of_mem_replicate hy
      simpa [hy0] using hzero
    · exact hwU y hy
  · simp [v, hwsum]

/-- Set equality form of the padded ordinary Lemma 4.2. -/
theorem iteratedFinsetSum_replicate_eq_univ_of_pGroupDStar_le
    (U : Finset B) (hzero : 0 ∈ U)
    (hgen : AddSubgroup.closure (U : Set B) = ⊤)
    (k : ℕ) (hk : pGroupDStar B ≤ k) :
    iteratedFinsetSum (List.replicate k U) = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  exact mem_iteratedFinsetSum_replicate_of_pGroupDStar_le
    U hzero hgen k hk x

end PaddedOrdinarySpanning

section NontrivialOddPGroup

variable {B : Type u} [AddCommGroup B] [Fintype B] [Nontrivial B]

/-- A nontrivial finite group has ordinary Davenport constant greater than
one.  This elementary fact is kept separate from the oddness argument. -/
theorem one_lt_ordinaryDavenportValue :
    1 < ordinaryDavenportValue B := by
  have hpos : 0 < ordinaryDavenportValue B :=
    ordinaryDavenportConstant_pos _ (ordinaryDavenportValue_spec B)
  by_contra hnot
  have hvalue : ordinaryDavenportValue B = 1 := by omega
  obtain ⟨x, hx⟩ := exists_ne (0 : B)
  have hzero : HasNonemptyZeroSum ([x] : List B) := by
    apply (ordinaryDavenportValue_spec B).1
    simp [hvalue]
  obtain ⟨I, hIne, hIsum⟩ := hzero
  have hI : I = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨j, hj⟩ := hIne
    have hij : i = j := by
      apply Fin.ext
      have hi : i.1 < 1 := by simpa using i.2
      have hj' : j.1 < 1 := by simpa using j.2
      omega
    simpa [hij] using hj
  apply hx
  simpa [hI, occurrenceValue] using hIsum

/-- In a nontrivial finite abelian odd `p`-group, `d*` is at least two.
The proof uses only: positivity/nontriviality, Olson oddness, and
`d* + 1 = D`. -/
theorem two_le_pGroupDStar_of_odd_pGroup
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hB : IsPGroup p (Multiplicative B)) :
    2 ≤ pGroupDStar B := by
  have hodd : Odd (ordinaryDavenportValue B) :=
    odd_ordinaryDavenport_of_isPGroup B p
      (ordinaryDavenportValue B) hp hpTwo hB
      (ordinaryDavenportValue_spec B)
  have hgt : 1 < ordinaryDavenportValue B :=
    one_lt_ordinaryDavenportValue (B := B)
  have hrecover := pGroupDStar_add_one B
  rcases hodd with ⟨t, ht⟩
  omega

end NontrivialOddPGroup

section InternalSubgroupConvolution

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The copy of `H` inside the additive group `K`, for `H ≤ K`. -/
def internalAddSubgroup (H K : AddSubgroup A) : AddSubgroup K :=
  H.comap K.subtype

/-- The internal copy of `H` in `K` is additively equivalent to `H`. -/
def internalAddSubgroupEquiv (H K : AddSubgroup A) (hHK : H ≤ K) :
    internalAddSubgroup H K ≃+ H where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, hHK x.2⟩, x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := by ext; rfl

/-- Subgroup--quotient `d*` convolution inside `K`, expressed with the
original subgroup invariant rather than the definitionally different comap
subtype. -/
theorem pGroupDStar_internal_of_le
    (H K : AddSubgroup A) (hHK : H ≤ K) :
    pGroupDStar H + pGroupDStar (K ⧸ internalAddSubgroup H K) ≤
      pGroupDStar K := by
  letI : Fintype K := Fintype.ofFinite K
  have hconv := pGroupDStar_internal_subgroup_quotient_le
    K (internalAddSubgroup H K)
  have heq : pGroupDStar (internalAddSubgroup H K) = pGroupDStar H :=
    pGroupDStar_addEquiv (internalAddSubgroupEquiv H K hHK)
  simpa only [heq] using hconv

end InternalSubgroupConvolution

section AffineSpanning

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The affine copy `a + U` of a finite set in a subgroup. -/
noncomputable def affineSubgroupFinset
    (H : AddSubgroup A) (a : A) (U : Finset H) : Finset A := by
  classical
  exact U.image fun h ↦ a + H.subtype h

/-- Summing an affine image of a subgroup-valued list separates the constant
translation from the subgroup sum. -/
theorem sum_map_add_subgroup_coe
    (H : AddSubgroup A) (a : A) (w : List H) :
    (w.map fun z ↦ a + H.subtype z).sum =
      w.length • a + H.subtype w.sum := by
  induction w with
  | nil => simp
  | cons z w ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, map_add]
      rw [ih]
      simp [add_nsmul]
      abel

/-- Affine/subgroup form of Lemma 4.2, with explicit zero padding.  If `U`
generates `H`, then every element of the coset `k•a + H` is a sum of exactly
`k` elements of `a + U`, for every `k ≥ d*(H)`. -/
theorem addCosetFinset_subset_iteratedFinsetSum_replicate_affine
    (H : AddSubgroup A) (a : A) (U : Finset H)
    (hzero : 0 ∈ U) (hgen : AddSubgroup.closure (U : Set H) = ⊤)
    (k : ℕ) (hk : pGroupDStar H ≤ k) :
    addCosetFinset H (k • a) ⊆
      iteratedFinsetSum
        (List.replicate k (affineSubgroupFinset H a U)) := by
  classical
  intro x hx
  have hdiff : x - k • a ∈ H :=
    (mem_addCosetFinset_iff H (k • a) x).1 hx
  let h : H := ⟨x - k • a, hdiff⟩
  have hmem : h ∈ iteratedFinsetSum (List.replicate k U) :=
    mem_iteratedFinsetSum_replicate_of_pGroupDStar_le
      U hzero hgen k hk h
  obtain ⟨w, hwlen, hwU, hwsum⟩ :=
    (mem_iteratedFinsetSum_replicate_iff U k h).1 hmem
  let v : List A := w.map fun z ↦ a + H.subtype z
  apply (mem_iteratedFinsetSum_replicate_iff
    (affineSubgroupFinset H a U) k x).2
  refine ⟨v, by simp [v, hwlen], ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ :
        ∃ z ∈ w, a + H.subtype z = y := by
      simpa only [v] using (List.mem_map.mp hy)
    subst y
    apply Finset.mem_image.mpr
    exact ⟨z, hwU z hz, rfl⟩
  · have hsumv : v.sum = w.length • a + H.subtype w.sum := by
      simpa only [v] using sum_map_add_subgroup_coe H a w
    rw [hsumv, hwlen, hwsum]
    change k • a + (x - k • a) = x
    abel

/-- Exact `d*(H)` affine version of Lemma 4.2. -/
theorem addCosetFinset_subset_iteratedFinsetSum_replicate_affine_pGroupDStar
    (H : AddSubgroup A) (a : A) (U : Finset H)
    (hzero : 0 ∈ U) (hgen : AddSubgroup.closure (U : Set H) = ⊤) :
    addCosetFinset H (pGroupDStar H • a) ⊆
      iteratedFinsetSum
        (List.replicate (pGroupDStar H) (affineSubgroupFinset H a U)) := by
  exact addCosetFinset_subset_iteratedFinsetSum_replicate_affine
    H a U hzero hgen (pGroupDStar H) le_rfl

end AffineSpanning

section QuotientAndCosetLift

variable {A : Type u} [AddCommGroup A] [Fintype A]
  [DecidableEq A]

/-- The singleton zero finite set is the additive identity for pointwise
finite-set addition. -/
theorem singleton_zero_add_finset (S : Finset A) :
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

/-- Iterated finite sumsets split across list append. -/
theorem iteratedFinsetSum_append
    (P Q : List (Finset A)) :
    iteratedFinsetSum (P ++ Q) =
      iteratedFinsetSum P + iteratedFinsetSum Q := by
  induction P with
  | nil => simp only [List.nil_append, iteratedFinsetSum_nil,
      singleton_zero_add_finset]
  | cons C P ih =>
      simp only [List.cons_append, iteratedFinsetSum_cons, ih]
      rw [add_assoc]

/-- Projection to a quotient commutes with an iterated finite sumset. -/
theorem quotientLayer_iteratedFinsetSum
    (H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (P : List (Finset A)) :
    quotientLayer H (iteratedFinsetSum P) =
      iteratedFinsetSum (P.map (quotientLayer H)) := by
  induction P with
  | nil =>
      ext q
      simp [iteratedFinsetSum, mem_quotientLayer_iff, eq_comm]
  | cons C P ih =>
      simp only [iteratedFinsetSum_cons, List.map_cons]
      rw [quotientLayer_add, ih]

/-- A full `H`-coset already covered by one block can be added to any
literal lift of a quotient summand covered by a second block.  The conclusion
retains the literal lift `y`; quotient membership alone cannot canonically
choose a representative. -/
theorem exists_addCosetFinset_subset_iteratedFinsetSum_append_of_quotient_mem
    (H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (P Q : List (Finset A)) (a : A)
    (hcoset : addCosetFinset H a ⊆ iteratedFinsetSum P)
    (q : A ⧸ H)
    (hq : q ∈ iteratedFinsetSum (Q.map (quotientLayer H))) :
    ∃ y ∈ iteratedFinsetSum Q, (y : A ⧸ H) = q ∧
      addCosetFinset H (a + y) ⊆ iteratedFinsetSum (P ++ Q) := by
  classical
  have hq' : q ∈ quotientLayer H (iteratedFinsetSum Q) := by
    rw [quotientLayer_iteratedFinsetSum]
    exact hq
  obtain ⟨y, hy, hyq⟩ := (mem_quotientLayer_iff H
    (iteratedFinsetSum Q) q).1 hq'
  refine ⟨y, hy, hyq, ?_⟩
  intro z hz
  have hzH : z - (a + y) ∈ H :=
    (mem_addCosetFinset_iff H (a + y) z).1 hz
  let x := z - y
  have hxcoset : x ∈ addCosetFinset H a := by
    apply (mem_addCosetFinset_iff H a x).2
    change (z - y) - a ∈ H
    convert hzH using 1 <;> abel
  rw [iteratedFinsetSum_append]
  apply Finset.mem_add.mpr
  refine ⟨x, hcoset hxcoset, y, hy, ?_⟩
  dsimp [x]
  abel

end QuotientAndCosetLift

end GaoLean

#print axioms GaoLean.pGroupDStar_addEquiv
#print axioms GaoLean.two_le_pGroupDStar_of_odd_pGroup
#print axioms GaoLean.pGroupDStar_internal_of_le
#print axioms GaoLean.addCosetFinset_subset_iteratedFinsetSum_replicate_affine
#print axioms GaoLean.quotientLayer_iteratedFinsetSum
#print axioms GaoLean.exists_addCosetFinset_subset_iteratedFinsetSum_append_of_quotient_mem
