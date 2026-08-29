import GaoLean.PGGeneralWeightedDavenportMinimum
import Mathlib.GroupTheory.Archimedean

/-!
# Normalizing arbitrary integer weight sets

This file contains the algebraic normalization used in Corollary 1.2 of the
source paper.  No finiteness assumption is made on the weight set.
-/

namespace GaoLean

open scoped BigOperators

/-- Multiplication by an integer, viewed as an additive endomorphism of `ℤ`. -/
def intMulAddHom (g : ℤ) : ℤ →+ ℤ where
  toFun z := g * z
  map_zero' := by simp
  map_add' := by intro x y; ring

/-- Divide a weight set by a chosen common generator, without making a
choice of quotients. -/
def normalizedWeightSet (g : ℤ) (W : Set ℤ) : Set ℤ :=
  (intMulAddHom g) ⁻¹' W

@[simp]
theorem mem_normalizedWeightSet_iff (g z : ℤ) (W : Set ℤ) :
    z ∈ normalizedWeightSet g W ↔ g * z ∈ W :=
  Iff.rfl

/-- Every arbitrary integer weight set has a cyclic closure generator. -/
theorem exists_weightClosureGenerator (W : Set ℤ) :
    ∃ g : ℤ, AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ) := by
  obtain ⟨g, hg⟩ := Int.subgroup_cyclic (AddSubgroup.closure W)
  exact ⟨g, hg⟩

/-- Every original weight is an integral multiple of a closure generator. -/
theorem exists_normalizedWeight_of_mem
    {W : Set ℤ} {g w : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (hw : w ∈ W) :
    ∃ z : ℤ, z ∈ normalizedWeightSet g W ∧ g * z = w := by
  have hwgen : w ∈ AddSubgroup.closure ({g} : Set ℤ) := by
    rw [← hgen]
    exact AddSubgroup.subset_closure hw
  obtain ⟨z, hz⟩ := AddSubgroup.mem_closure_singleton.mp hwgen
  have hgz : g * z = w := by
    simpa [mul_comm] using hz
  refine ⟨z, ?_, hgz⟩
  · change g * z ∈ W
    rw [hgz]
    exact hw

/-- Multiplication by the generator maps the normalized set exactly onto
the original set. -/
theorem image_normalizedWeightSet_eq
    {W : Set ℤ} {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ)) :
    intMulAddHom g '' normalizedWeightSet g W = W := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hw
    obtain ⟨z, hz, hgz⟩ := exists_normalizedWeight_of_mem hgen hw
    exact ⟨z, hz, hgz⟩

/-- The singleton weight `1` generates the additive group of integers. -/
theorem closure_singleton_one_int :
    AddSubgroup.closure ({1} : Set ℤ) = ⊤ := by
  ext z
  simp

/-- Normalization by a cyclic closure generator produces a primitive weight
set, including the degenerate generator `g = 0`. -/
theorem normalizedWeightSet_isPrimitive
    {W : Set ℤ} (hW : W.Nonempty) {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ)) :
    IsPrimitiveWeightSet (normalizedWeightSet g W) := by
  unfold IsPrimitiveWeightSet
  by_cases hg : g = 0
  · subst g
    obtain ⟨w, hw⟩ := hW
    have hwzero : w = 0 := by
      have hwcl : w ∈ AddSubgroup.closure ({0} : Set ℤ) := by
        rw [← hgen]
        exact AddSubgroup.subset_closure hw
      rw [AddSubgroup.closure_singleton_zero] at hwcl
      simpa using hwcl
    have hzeroW : (0 : ℤ) ∈ W := hwzero ▸ hw
    have hnorm : normalizedWeightSet 0 W = Set.univ := by
      ext z
      simp [normalizedWeightSet, intMulAddHom, hzeroW]
    rw [hnorm, AddSubgroup.closure_univ]
  · let f := intMulAddHom g
    have hf : Function.Injective f := by
      intro x y hxy
      dsimp [f, intMulAddHom] at hxy
      exact mul_left_cancel₀ hg hxy
    rw [← closure_singleton_one_int]
    apply (AddSubgroup.map_injective hf)
    rw [f.map_closure, f.map_closure]
    change AddSubgroup.closure (intMulAddHom g '' normalizedWeightSet g W) =
      AddSubgroup.closure (intMulAddHom g '' ({1} : Set ℤ))
    rw [image_normalizedWeightSet_eq hgen]
    rw [hgen]
    congr 1
    ext z
    simp [intMulAddHom]

/-- A normalized weight set is nonempty whenever the original one is. -/
theorem normalizedWeightSet_nonempty
    {W : Set ℤ} (hW : W.Nonempty) {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ)) :
    (normalizedWeightSet g W).Nonempty := by
  obtain ⟨w, hw⟩ := hW
  obtain ⟨z, hz, -⟩ := exists_normalizedWeight_of_mem hgen hw
  exact ⟨z, hz⟩

/-- Multiplication by `g` on an arbitrary additive commutative group. -/
def zsmulAddHom {A : Type*} [AddCommGroup A] (g : ℤ) : A →+ A where
  toFun x := g • x
  map_zero' := by simp
  map_add' := by intro x y; simp

/-- The image group `gA`, used as the finite ambient group after
normalization. -/
abbrev ZSmulRange {A : Type*} [AddCommGroup A] (g : ℤ) :=
  (zsmulAddHom (A := A) g).range

/-- The canonical surjection from `A` onto `gA`. -/
abbrev zsmulRangeHom {A : Type*} [AddCommGroup A] (g : ℤ) :
    A →+ ZSmulRange (A := A) g :=
  (zsmulAddHom (A := A) g).rangeRestrict

@[simp]
theorem coe_zsmulRangeHom {A : Type*} [AddCommGroup A] (g : ℤ) (x : A) :
    ((zsmulRangeHom (A := A) g x : ZSmulRange (A := A) g) : A) = g • x :=
  rfl

/-- A normalized weighted sum on the scaled source `g • xs`, valued in
`gA`, pulls back to an original weighted sum on `xs`.  The selected source
occurrences and their cardinality are preserved exactly. -/
noncomputable def hasWeightedSumOfCard_of_normalized_range
    {A : Type*} [AddCommGroup A]
    {W : Set ℤ} {g : ℤ}
    (xs : List A) (n : ℕ) (y : ZSmulRange (A := A) g)
    (h : HasWeightedSumOfCard (normalizedWeightSet g W)
      (xs.map (zsmulRangeHom (A := A) g)) n y) :
    HasWeightedSumOfCard W xs n (y : A) := by
  classical
  let f := zsmulRangeHom (A := A) g
  let e := ConcreteGDihedral.mapOccurrenceEquiv f xs
  let J : Selection xs := h.selected.map e.symm.toEmbedding
  let weights : Occurrence xs → ℤ := fun i => g * h.weights (e i)
  have hvalue (i : Occurrence xs) :
      occurrenceValue (xs.map f) (e i) = f (occurrenceValue xs i) :=
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f xs i
  have hvalueSymm (j : Occurrence (xs.map f)) :
      f (occurrenceValue xs (e.symm j)) = occurrenceValue (xs.map f) j :=
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm f xs j
  refine {
    selected := J
    weights := weights
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    have hjw := h.weights_mem j hj
    simpa [weights, e, normalizedWeightSet, intMulAddHom] using hjw
  · simpa [J] using h.card_selected
  · let incl := AddSubgroup.subtype (zsmulAddHom (A := A) g).range
    have hsum := congrArg incl h.weighted_sum
    have hcoeval
        (j : Occurrence (xs.map (zsmulRangeHom (A := A) g))) :
        ((occurrenceValue
            (xs.map (zsmulRangeHom (A := A) g)) j :
              ZSmulRange (A := A) g) : A) =
          g • occurrenceValue xs
            ((ConcreteGDihedral.mapOccurrenceEquiv
              (zsmulRangeHom (A := A) g) xs).symm j) := by
      rw [← ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm
        (zsmulRangeHom (A := A) g) xs j]
      rfl
    have hsumPre0 :
        (∑ j ∈ h.selected, h.weights j •
          (g • occurrenceValue xs
            ((ConcreteGDihedral.mapOccurrenceEquiv
              (zsmulRangeHom (A := A) g) xs).symm j))) = (y : A) := by
      simpa only [map_sum, map_zsmul, hcoeval, incl,
        AddSubgroup.coe_subtype] using hsum
    have hsumPre :
        (∑ j ∈ h.selected, h.weights j •
          (g • occurrenceValue xs (e.symm j))) = (y : A) := by
      simpa [e, f] using hsumPre0
    have hsumScaled :
        (∑ i ∈ J, h.weights (e i) •
          (g • occurrenceValue xs i)) = (y : A) := by
      simpa [J, e] using hsumPre
    calc
      (∑ i ∈ J, weights i • occurrenceValue xs i) =
          ∑ i ∈ J, h.weights (e i) •
            (g • occurrenceValue xs i) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [weights, smul_smul, mul_comm]
      _ = (y : A) := hsumScaled

/-- A total choice of normalized representative.  Outside `W` its value is
irrelevant; on `W` it lies in the normalized set and multiplies back to the
original weight. -/
noncomputable def normalizedWeightQuotient
    {W : Set ℤ} {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (w : ℤ) : ℤ := by
  classical
  exact if hw : w ∈ W then
    Classical.choose (exists_normalizedWeight_of_mem hgen hw)
  else 0

theorem normalizedWeightQuotient_spec
    {W : Set ℤ} {g w : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (hw : w ∈ W) :
    normalizedWeightQuotient hgen w ∈ normalizedWeightSet g W ∧
      g * normalizedWeightQuotient hgen w = w := by
  classical
  rw [normalizedWeightQuotient, dif_pos hw]
  exact Classical.choose_spec (exists_normalizedWeight_of_mem hgen hw)

/-- An original weighted zero sum becomes a normalized weighted zero sum on
the scaled source in `gA`. -/
noncomputable def hasWeightedZeroSumOfCard_normalized_range
    {A : Type*} [AddCommGroup A]
    {W : Set ℤ} {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (xs : List A) (n : ℕ)
    (h : HasWeightedSumOfCard W xs n 0) :
    HasWeightedSumOfCard (normalizedWeightSet g W)
      (xs.map (zsmulRangeHom (A := A) g)) n 0 := by
  classical
  let f := zsmulRangeHom (A := A) g
  let e := ConcreteGDihedral.mapOccurrenceEquiv f xs
  let J : Selection (xs.map f) := h.selected.map e.toEmbedding
  let weights : Occurrence (xs.map f) → ℤ := fun j =>
    normalizedWeightQuotient hgen (h.weights (e.symm j))
  have hvalue (i : Occurrence xs) :
      occurrenceValue (xs.map f) (e i) = f (occurrenceValue xs i) :=
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f xs i
  refine {
    selected := J
    weights := weights
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro j hj
    rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
    exact (normalizedWeightQuotient_spec hgen (h.weights_mem i hi)).1
  · simpa [J] using h.card_selected
  · apply Subtype.ext
    change (AddSubgroup.subtype (zsmulAddHom (A := A) g).range)
      (∑ j ∈ J, weights j • occurrenceValue (xs.map f) j) = 0
    rw [map_sum]
    simp_rw [map_zsmul]
    have hsumScaled :
        (∑ i ∈ h.selected,
          normalizedWeightQuotient hgen (h.weights i) •
            (g • occurrenceValue xs i)) = 0 := by
      calc
        (∑ i ∈ h.selected,
            normalizedWeightQuotient hgen (h.weights i) •
              (g • occurrenceValue xs i)) =
            ∑ i ∈ h.selected, h.weights i • occurrenceValue xs i := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [smul_smul]
              have hq := (normalizedWeightQuotient_spec hgen
                (h.weights_mem i hi)).2
              rw [mul_comm, hq]
        _ = 0 := h.weighted_sum
    have hcoe (x : A) :
        (AddSubgroup.subtype (zsmulAddHom (A := A) g).range)
            (zsmulRangeHom (A := A) g x) = g • x := rfl
    have hzsmul (x : A) : zsmulAddHom (A := A) g x = g • x := rfl
    simpa [J, weights, e, hvalue, f, hcoe, hzsmul] using hsumScaled

/-- Zero-sum existence transports from the original source to the normalized
scaled source. -/
theorem hasNonemptyWeightedZeroSum_normalized_range
    {A : Type*} [AddCommGroup A]
    {W : Set ℤ} {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (xs : List A)
    (h : HasNonemptyWeightedZeroSum W xs) :
    HasNonemptyWeightedZeroSum (normalizedWeightSet g W)
      (xs.map (zsmulRangeHom (A := A) g)) := by
  rcases h with ⟨n, hn, ⟨hsum⟩⟩
  exact ⟨n, hn, ⟨hasWeightedZeroSumOfCard_normalized_range
    hgen xs n hsum⟩⟩

/-- The normalized Davenport threshold on `gA` is no larger than any
certified original threshold on `A`. -/
theorem weightedDavenportAtMost_normalized_range
    {A : Type*} [AddCommGroup A]
    {W : Set ℤ} {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (D : ℕ) (hD : WeightedDavenportAtMost W A D) :
    WeightedDavenportAtMost (normalizedWeightSet g W)
      (ZSmulRange (A := A) g) D := by
  classical
  intro ys hlen
  let f := zsmulRangeHom (A := A) g
  let sec : ZSmulRange (A := A) g → A :=
    Function.surjInv (zsmulAddHom (A := A) g).rangeRestrict_surjective
  let xs : List A := ys.map sec
  have hxs : xs.length = D := by simpa [xs] using hlen
  have hzero := hD xs hxs
  have hnorm := hasNonemptyWeightedZeroSum_normalized_range hgen xs hzero
  have hsection : f ∘ sec = id := by
    funext y
    exact Function.surjInv_eq
      (zsmulAddHom (A := A) g).rangeRestrict_surjective y
  simpa [xs, List.map_map, f, hsection] using hnorm

/-- The canonical normalized Davenport value is bounded by an exact
original Davenport value. -/
theorem weightedDavenportValue_normalized_range_le
    {A : Type*} [AddCommGroup A] [Finite A]
    {W : Set ℤ} (hW : W.Nonempty) {g : ℤ}
    (hgen : AddSubgroup.closure W = AddSubgroup.closure ({g} : Set ℤ))
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D) :
    weightedDavenportValue (normalizedWeightSet g W)
        (ZSmulRange (A := A) g)
        (normalizedWeightSet_nonempty hW hgen) ≤ D := by
  let D' := weightedDavenportValue (normalizedWeightSet g W)
    (ZSmulRange (A := A) g) (normalizedWeightSet_nonempty hW hgen)
  have hD'exact : IsWeightedDavenportConstant (normalizedWeightSet g W)
      (ZSmulRange (A := A) g) D' := by
    simpa [D'] using weightedDavenportValue_spec
      (normalizedWeightSet g W) (ZSmulRange (A := A) g)
      (normalizedWeightSet_nonempty hW hgen)
  exact weightedDavenportConstant_le_of_atMost
    (normalizedWeightSet g W) (ZSmulRange (A := A) g)
    hD'exact (weightedDavenportAtMost_normalized_range hgen D hD.1)

/-- Pull a normalized existence conclusion on the scaled source back to the
literal original weighted existence conclusion. -/
theorem weightedGMOExistenceConclusion_of_normalized_range
    {A : Type*} [AddCommGroup A]
    {W : Set ℤ} {g : ℤ} {xs : List A} {n : ℕ}
    (h : WeightedGMOExistenceConclusion (normalizedWeightSet g W)
      (xs.map (zsmulRangeHom (A := A) g)) n) :
    WeightedGMOExistenceConclusion W xs n := by
  rcases h with ⟨y, ⟨hy⟩⟩
  refine ⟨(y : A), ⟨?_⟩⟩
  simpa using hasWeightedSumOfCard_of_normalized_range xs n (n • y) hy

universe u

/-- Corollary 1.2, in provider form: primitive-weight existence providers
for all finite abelian groups imply the literal arbitrary-nonempty-weight
existence provider.  The reduction keeps arbitrary (possibly infinite)
weight sets and occurrence-labelled selections. -/
theorem generalWeightedGMOExistenceProvider_of_primitiveProviders
    {A : Type u} [AddCommGroup A] [Fintype A]
    (hprimitive :
      ∀ (B : Type u) [AddCommGroup B] [Fintype B],
        ∀ (V : Set ℤ), V.Nonempty → IsPrimitiveWeightSet V →
          ∀ (DV : ℕ), IsWeightedDavenportConstant V B DV →
            ∀ (ys : List B) (n : ℕ),
              Nat.card B ≤ n →
              n + DV - 1 ≤ ys.length →
              WeightedGMOExistenceConclusion V ys n) :
    GeneralWeightedGMOExistenceProvider A := by
  intro W hW D hD xs n hn hlen
  obtain ⟨g, hgen⟩ := exists_weightClosureGenerator W
  let V : Set ℤ := normalizedWeightSet g W
  let B := ZSmulRange (A := A) g
  letI : Fintype B := Fintype.ofFinite B
  let f := zsmulRangeHom (A := A) g
  let hV : V.Nonempty := by
    simpa [V] using normalizedWeightSet_nonempty hW hgen
  have hVprimitive : IsPrimitiveWeightSet V := by
    simpa [V] using normalizedWeightSet_isPrimitive hW hgen
  let DV : ℕ := weightedDavenportValue V B hV
  have hDV : IsWeightedDavenportConstant V B DV := by
    simpa [DV] using weightedDavenportValue_spec V B hV
  have hDVle : DV ≤ D := by
    simpa [V, B, DV, hV] using
      weightedDavenportValue_normalized_range_le hW hgen D hD
  have hcardBA : Nat.card B ≤ Nat.card A := by
    exact Nat.card_le_card_of_injective
      (fun y : B => (y : A)) Subtype.val_injective
  have hnB : Nat.card B ≤ n := hcardBA.trans hn
  have hlenB : n + DV - 1 ≤ (xs.map f).length := by
    simp only [List.length_map]
    omega
  have hnormalized : WeightedGMOExistenceConclusion V (xs.map f) n :=
    hprimitive B V hV hVprimitive DV hDV (xs.map f) n hnB hlenB
  exact weightedGMOExistenceConclusion_of_normalized_range
    (W := W) (g := g) (xs := xs) (n := n) (by
      simpa [V, f] using hnormalized)

end GaoLean

#print axioms GaoLean.exists_weightClosureGenerator
#print axioms GaoLean.normalizedWeightSet_isPrimitive
#print axioms GaoLean.hasWeightedSumOfCard_of_normalized_range
#print axioms GaoLean.hasWeightedZeroSumOfCard_normalized_range
#print axioms GaoLean.weightedDavenportAtMost_normalized_range
#print axioms GaoLean.weightedDavenportValue_normalized_range_le
#print axioms GaoLean.weightedGMOExistenceConclusion_of_normalized_range
#print axioms GaoLean.generalWeightedGMOExistenceProvider_of_primitiveProviders
