import GaoLean.PlusMinus
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Group-algebra core of the plus-minus Davenport bound

This file formalizes the coefficient-extraction half of Proposition 3.1 in
the 13-page `gao0824` PR #7 manuscript.  The group-algebra product is defined
literally over `ZMod p`; its support is tracked by occurrence-indexed
coefficients in `{-1,0,1}`.  Thus repeated source values are never collapsed.
-/

namespace GaoLean

section GroupAlgebraExpansion

variable {A : Type*} [AddCommGroup A]

/-- The additive group algebra used in the manuscript. -/
abbrev PMGroupAlgebra (p : ℕ) (A : Type*) [AddCommGroup A] :=
  AddMonoidAlgebra (ZMod p) A

/-- The factor `[x]+[-x]-2[0]` from Proposition 3.1. -/
noncomputable def pmGroupAlgebraFactor (p : ℕ) (x : A) : PMGroupAlgebra p A :=
  AddMonoidAlgebra.single x 1 + AddMonoidAlgebra.single (-x) 1 -
    AddMonoidAlgebra.single 0 2

/-- The ordered product of the group-algebra factors attached to a source
list.  The algebra is commutative here, but retaining the list order makes the
induction occurrence-faithful. -/
noncomputable def pmGroupAlgebraProduct (p : ℕ) (s : List A) : PMGroupAlgebra p A :=
  (s.map (pmGroupAlgebraFactor p)).prod

/-- A possibly-zero restricted-coefficient assignment with a prescribed
integer-weighted sum. -/
structure WeakRestrictedCoefficientRelation (s : List A) (target : A) where
  coefficient : Occurrence s → ℤ
  restricted : ∀ i, IsRestrictedCoefficient (coefficient i)
  weightedSum_eq :
    ∑ i, coefficient i • occurrenceValue s i = target

namespace WeakRestrictedCoefficientRelation

/-- Prepend one restricted coefficient to an assignment on the tail. -/
def prepend {s : List A} {target : A}
    (x : A) (a : ℤ) (ha : IsRestrictedCoefficient a)
    (R : WeakRestrictedCoefficientRelation s target) :
    WeakRestrictedCoefficientRelation (x :: s) (a • x + target) where
  coefficient := fun i ↦
    Fin.cases (n := s.length) a R.coefficient i
  restricted := by
    intro i
    refine Fin.cases (n := s.length) ha (fun j ↦ ?_) i
    exact R.restricted j
  weightedSum_eq := by
    calc
      (∑ i : Fin (s.length + 1),
          (Fin.cases (n := s.length) a R.coefficient i : ℤ) •
          occurrenceValue (x :: s) i) =
          ∑ i : Fin (s.length + 1),
            Fin.cases (n := s.length) (a • x)
              (fun j ↦ R.coefficient j • occurrenceValue s j) i := by
        apply Finset.sum_congr rfl
        intro i _
        refine Fin.cases (n := s.length) ?_ (fun j ↦ ?_) i <;>
          simp [occurrenceValue]
      _ = a • x + ∑ j, R.coefficient j • occurrenceValue s j := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ]
      _ = a • x + target := by rw [R.weightedSum_eq]

/-- A nonzero prepended coefficient upgrades a weak assignment at zero to
the project's `RestrictedCoefficientRelation`. -/
def toRelation_of_prepend_ne_zero {s : List A} {target : A}
    (x : A) (a : ℤ) (ha : IsRestrictedCoefficient a) (ha0 : a ≠ 0)
    (R : WeakRestrictedCoefficientRelation s target)
    (htarget : a • x + target = 0) :
    RestrictedCoefficientRelation (x :: s) := by
  let W := R.prepend x a ha
  exact
    { coefficient := W.coefficient
      restricted := W.restricted
      nonzero := ⟨⟨0, by simp⟩, by simp [W, prepend, ha0]⟩
      weightedSum_eq_zero := W.weightedSum_eq.trans htarget }

/-- Prepending a zero coefficient preserves a pre-existing nonzero
restricted relation on the tail. -/
def prependZeroRelation {s : List A} (x : A)
    (R : RestrictedCoefficientRelation s) :
    RestrictedCoefficientRelation (x :: s) := by
  let W : WeakRestrictedCoefficientRelation s 0 :=
    { coefficient := R.coefficient
      restricted := R.restricted
      weightedSum_eq := R.weightedSum_eq_zero }
  let V := W.prepend x 0 (by simp [IsRestrictedCoefficient])
  exact
    { coefficient := V.coefficient
      restricted := V.restricted
      nonzero := by
        rcases R.nonzero with ⟨i, hi⟩
        exact ⟨Fin.succ i, by simpa [V, prepend] using hi⟩
      weightedSum_eq_zero := by simpa using V.weightedSum_eq }

end WeakRestrictedCoefficientRelation

/-- Every support value of a single factor is one of `x`, `-x`, or `0`. -/
theorem mem_support_pmGroupAlgebraFactor
    (p : ℕ) (x a : A)
    (ha : a ∈ (pmGroupAlgebraFactor p x).coeff.support) :
    a = x ∨ a = -x ∨ a = 0 := by
  by_contra h
  simp only [not_or] at h
  apply (Finsupp.mem_support_iff.mp ha)
  simp [pmGroupAlgebraFactor, h.1, h.2.1, h.2.2]

/-- Every support value of the full product is realized by an
occurrence-indexed restricted-coefficient assignment. -/
theorem weakRestrictedCoefficientRelation_of_mem_support_pmGroupAlgebraProduct
    (p : ℕ) (s : List A) (a : A)
    (ha : a ∈ (pmGroupAlgebraProduct p s).coeff.support) :
    Nonempty (WeakRestrictedCoefficientRelation s a) := by
  classical
  induction s generalizing a with
  | nil =>
      have ha0 : a = 0 := by
        by_contra hne
        apply Finsupp.mem_support_iff.mp ha
        simp [pmGroupAlgebraProduct, AddMonoidAlgebra.one_def, hne]
      subst a
      exact ⟨
        { coefficient := Fin.elim0
          restricted := fun i ↦ Fin.elim0 i
          weightedSum_eq := by
            apply Finset.sum_eq_zero
            intro i _
            exact Fin.elim0 i }⟩
  | cons x s ih =>
      have hprodmem :
          a ∈ (pmGroupAlgebraFactor p x *
            pmGroupAlgebraProduct p s).coeff.support := by
        simpa [pmGroupAlgebraProduct] using ha
      have hmem := AddMonoidAlgebra.support_coeff_mul_subset
        (pmGroupAlgebraFactor p x) (pmGroupAlgebraProduct p s) hprodmem
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hmem
      rcases ih v hv with ⟨R⟩
      rcases mem_support_pmGroupAlgebraFactor p x u hu with hux | hux | hu0
      · let W := R.prepend x 1 (by simp [IsRestrictedCoefficient])
        have W' : WeakRestrictedCoefficientRelation (x :: s) (x + v) := by
          simpa using W
        have htarget : x + v = a := by simpa [hux] using huv
        exact ⟨htarget ▸ W'⟩
      · let W := R.prepend x (-1) (by simp [IsRestrictedCoefficient])
        have W' : WeakRestrictedCoefficientRelation (x :: s) (-x + v) := by
          simpa using W
        have htarget : -x + v = a := by simpa [hux] using huv
        exact ⟨htarget ▸ W'⟩
      · let W := R.prepend x 0 (by simp [IsRestrictedCoefficient])
        have W' : WeakRestrictedCoefficientRelation (x :: s) v := by
          simpa using W
        have htarget : v = a := by simpa [hu0] using huv
        exact ⟨htarget ▸ W'⟩

/-- If no nonzero restricted relation exists, the coefficient of `[0]` in
the product is exactly `(-2)^length`.  The proof uses support control rather
than silently treating equal source values as one variable. -/
theorem coeff_zero_pmGroupAlgebraProduct_of_no_relation
    (p : ℕ) (s : List A)
    (hfree : IsEmpty (RestrictedCoefficientRelation s)) :
    (pmGroupAlgebraProduct p s).coeff 0 = (-2 : ZMod p) ^ s.length := by
  classical
  induction s with
  | nil => simp [pmGroupAlgebraProduct]
  | cons x s ih =>
      have htail : IsEmpty (RestrictedCoefficientRelation s) :=
        ⟨fun R ↦ hfree.false
          (WeakRestrictedCoefficientRelation.prependZeroRelation x R)⟩
      have hx (a : A) (ha : a = x ∨ a = -x) :
          (pmGroupAlgebraProduct p s).coeff a = 0 := by
        by_contra hne
        have hmem : a ∈ (pmGroupAlgebraProduct p s).coeff.support :=
          Finsupp.mem_support_iff.mpr hne
        rcases weakRestrictedCoefficientRelation_of_mem_support_pmGroupAlgebraProduct
            p s a hmem with ⟨R⟩
        rcases ha with hax | hax
        · exact hfree.false <|
            R.toRelation_of_prepend_ne_zero x (-1)
              (by simp [IsRestrictedCoefficient]) (by norm_num) (by simp [hax])
        · exact hfree.false <|
            R.toRelation_of_prepend_ne_zero x 1
              (by simp [IsRestrictedCoefficient]) (by norm_num) (by simp [hax])
      have hpos : (pmGroupAlgebraProduct p s).coeff x = 0 := hx x (Or.inl rfl)
      have hneg : (pmGroupAlgebraProduct p s).coeff (-x) = 0 := hx (-x) (Or.inr rfl)
      rw [show pmGroupAlgebraProduct p (x :: s) =
          pmGroupAlgebraFactor p x * pmGroupAlgebraProduct p s by
            rfl]
      unfold pmGroupAlgebraFactor
      rw [sub_mul, add_mul]
      have hcoeff :
          ((AddMonoidAlgebra.single x 1 * pmGroupAlgebraProduct p s +
              AddMonoidAlgebra.single (-x) 1 * pmGroupAlgebraProduct p s -
              AddMonoidAlgebra.single 0 2 *
                pmGroupAlgebraProduct p s).coeff 0) =
            (AddMonoidAlgebra.single x 1 *
                pmGroupAlgebraProduct p s).coeff 0 +
          (AddMonoidAlgebra.single (-x) 1 *
            pmGroupAlgebraProduct p s).coeff 0 -
          (AddMonoidAlgebra.single 0 2 *
            pmGroupAlgebraProduct p s).coeff 0 := by
        simp
      rw [hcoeff]
      simp [hpos, hneg, ih htail, pow_succ]
      ring

/-- Exact group-algebra vanishing interface for a fixed length.  The next
layer of Proposition 3.1 derives this from augmentation-ideal nilpotence. -/
def PMGroupAlgebraProductVanishesAt
    (p : ℕ) (A : Type*) [AddCommGroup A] (m : ℕ) : Prop :=
  ∀ s : List A, s.length = m → pmGroupAlgebraProduct p s = 0

/-- The coefficient-extraction half of Proposition 3.1: group-algebra
vanishing in odd characteristic produces the precise occurrence-labelled
restricted-coefficient output consumed by `PlusMinus.lean`. -/
theorem restrictedCoefficientOutputAt_of_pmGroupAlgebraProductVanishes
    (p m : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0)
    (hvanish : PMGroupAlgebraProductVanishesAt p A m) :
    RestrictedCoefficientOutputAt A m := by
  intro s hs
  by_contra hnone
  have hfree : IsEmpty (RestrictedCoefficientRelation s) :=
    ⟨fun R ↦ hnone ⟨R⟩⟩
  have hcoeff := coeff_zero_pmGroupAlgebraProduct_of_no_relation p s hfree
  have hzero : (pmGroupAlgebraProduct p s).coeff 0 = 0 := by
    rw [hvanish s hs]
    rfl
  rw [hzero] at hcoeff
  have hne : (-2 : ZMod p) ^ s.length ≠ 0 := by
    apply pow_ne_zero
    simpa using hp2
  exact hne hcoeff.symm

end GroupAlgebraExpansion

section AugmentationNilpotence

variable {A : Type*} [AddCommGroup A]

/-- The standard augmentation generator `[x]-[0]`. -/
noncomputable def augmentationGenerator (p : ℕ) (x : A) :
    PMGroupAlgebra p A :=
  AddMonoidAlgebra.single x 1 - AddMonoidAlgebra.single 0 1

/-- Generator-level form of `I^D=0`: every product of at least `D`
augmentation generators vanishes.  A later invariant-factor layer establishes
this interface from the truncated-polynomial description of the group
algebra. -/
def AugmentationProductsVanishAt
    (p : ℕ) (A : Type*) [AddCommGroup A] (D : ℕ) : Prop :=
  ∀ t : List A, D ≤ t.length →
    (t.map (augmentationGenerator p)).prod = 0

/-- The elementary group-algebra identity used in the manuscript:
`[x]+[-x]-2[0]=[-x]([x]-[0])^2`. -/
theorem pmGroupAlgebraFactor_eq_single_mul_augmentation_sq
    (p : ℕ) (x : A) :
    pmGroupAlgebraFactor p x =
      AddMonoidAlgebra.single (-x) 1 * augmentationGenerator p x ^ 2 := by
  classical
  unfold pmGroupAlgebraFactor augmentationGenerator
  rw [pow_two]
  ring_nf
  simp only [pow_two, AddMonoidAlgebra.single_mul_single]
  have hone : AddMonoidAlgebra.single 0 (1 : ZMod p) =
      (1 : PMGroupAlgebra p A) := by rfl
  have htwo : AddMonoidAlgebra.single 0 (2 : ZMod p) =
      (2 : PMGroupAlgebra p A) := by
    exact (AddMonoidAlgebra.natCast_def 2).symm
  have hzeroIndex : x + -x + 0 = 0 := by simp
  have hxIndex : x + x + -x = x := by abel
  have hnegIndex : -x + (0 + 0) = -x := by simp
  rw [hzeroIndex, hxIndex, hnegIndex]
  simp only [mul_one]
  rw [hone, htwo]
  ring

/-- Duplicate every source entry; its length is exactly twice the original
length. -/
def duplicateEntries (s : List A) : List A :=
  s.flatMap fun x ↦ [x, x]

omit [AddCommGroup A] in
@[simp]
theorem length_duplicateEntries (s : List A) :
    (duplicateEntries s).length = 2 * s.length := by
  induction s with
  | nil => simp [duplicateEntries]
  | cons x s ih =>
      simp [duplicateEntries]
      omega

/-- Factor the Proposition 3.1 product into harmless basis units times a
product of exactly two augmentation generators per occurrence. -/
theorem pmGroupAlgebraProduct_eq_units_mul_augmentationProduct
    (p : ℕ) (s : List A) :
    pmGroupAlgebraProduct p s =
      (s.map fun x ↦ AddMonoidAlgebra.single (-x) (1 : ZMod p)).prod *
      ((duplicateEntries s).map (augmentationGenerator p)).prod := by
  classical
  induction s with
  | nil => simp [pmGroupAlgebraProduct, duplicateEntries]
  | cons x s ih =>
      rw [show pmGroupAlgebraProduct p (x :: s) =
          pmGroupAlgebraFactor p x * pmGroupAlgebraProduct p s by rfl]
      rw [pmGroupAlgebraFactor_eq_single_mul_augmentation_sq, ih]
      simp only [List.map_cons, List.prod_cons, duplicateEntries,
        List.flatMap_cons, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_nil, pow_two]
      ring

/-- Augmentation nilpotence at degree `D` makes every plus-minus product of
length `m` vanish as soon as `D ≤ 2m`. -/
theorem pmGroupAlgebraProductVanishesAt_of_augmentationProductsVanishAt
    (p D m : ℕ) (hDm : D ≤ 2 * m)
    (hnil : AugmentationProductsVanishAt p A D) :
    PMGroupAlgebraProductVanishesAt p A m := by
  intro s hs
  rw [pmGroupAlgebraProduct_eq_units_mul_augmentationProduct]
  have hlen : D ≤ (duplicateEntries s).length := by
    rw [length_duplicateEntries, hs]
    exact hDm
  rw [hnil (duplicateEntries s) hlen, mul_zero]

/-- Odd prime characteristic makes the constant coefficient `-2` nonzero. -/
theorem two_ne_zero_zmod_of_odd_prime
    (p : ℕ) (hp : p.Prime) (hpOdd : Odd p) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
  have hpEq : p = 2 := Nat.le_antisymm hpLe hp.two_le
  subst p
  norm_num at hpOdd

/-- Proposition 3.1 up to its invariant-factor nilpotence input: the actual
group-algebra argument now produces the occurrence-labelled restricted
coefficient relation internally. -/
theorem restrictedCoefficientOutputAt_of_augmentationProductsVanishAt
    (p D m : ℕ) (hp : p.Prime) (hpOdd : Odd p)
    (hDm : D ≤ 2 * m)
    (hnil : AugmentationProductsVanishAt p A D) :
    RestrictedCoefficientOutputAt A m := by
  letI : Fact p.Prime := ⟨hp⟩
  exact restrictedCoefficientOutputAt_of_pmGroupAlgebraProductVanishes
    p m (two_ne_zero_zmod_of_odd_prime p hp hpOdd)
      (pmGroupAlgebraProductVanishesAt_of_augmentationProductsVanishAt
        p D m hDm hnil)

/-- The numerical specialization used by Proposition 3.1.  Once
`I^D=0` is supplied in generator-product form, no restricted-coefficient
output remains as an assumption. -/
theorem plusMinusDavenportAtMost_half_of_augmentationProductsVanishAt
    (p D : ℕ) (hp : p.Prime) (hpOdd : Odd p) (hDOdd : Odd D)
    (hnil : AugmentationProductsVanishAt p A D) :
    PlusMinusDavenportAtMost A ((D + 1) / 2) := by
  apply plusMinusDavenportAtMost_of_restrictedCoefficientOutput
  apply restrictedCoefficientOutputAt_of_augmentationProductsVanishAt
    p D ((D + 1) / 2) hp hpOdd
  · rw [twice_half_succ_of_odd hDOdd]
    omega
  · exact hnil

end AugmentationNilpotence

end GaoLean

#print axioms GaoLean.weakRestrictedCoefficientRelation_of_mem_support_pmGroupAlgebraProduct
#print axioms GaoLean.coeff_zero_pmGroupAlgebraProduct_of_no_relation
#print axioms GaoLean.restrictedCoefficientOutputAt_of_pmGroupAlgebraProductVanishes
#print axioms GaoLean.pmGroupAlgebraFactor_eq_single_mul_augmentation_sq
#print axioms GaoLean.pmGroupAlgebraProduct_eq_units_mul_augmentationProduct
#print axioms GaoLean.restrictedCoefficientOutputAt_of_augmentationProductsVanishAt
#print axioms GaoLean.plusMinusDavenportAtMost_half_of_augmentationProductsVanishAt
