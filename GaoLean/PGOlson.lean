import GaoLean.PGPlusMinusGroupAlgebra
import GaoLean.PGDavenportConvolution
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Invariant-factor data for the Olson and plus-minus bounds

This file begins the remaining source-facing bridge from a finite direct
product of cyclic `p`-groups to the exact generator data consumed by the
group-algebra proof of Proposition 3.1.
-/

namespace GaoLean

section OrdinaryGroupAlgebraExpansion

variable {A : Type*} [AddCommGroup A]

/-- A possibly-zero occurrence-indexed `{0,1}` coefficient assignment. -/
structure WeakZeroOneCoefficientRelation (s : List A) (target : A) where
  coefficient : Occurrence s → ℤ
  zeroOne : ∀ i, coefficient i = 0 ∨ coefficient i = 1
  weightedSum_eq :
    ∑ i, coefficient i • occurrenceValue s i = target

/-- A nonzero occurrence-indexed `{0,1}` relation at zero. -/
structure ZeroOneCoefficientRelation (s : List A)
    extends WeakZeroOneCoefficientRelation s 0 where
  nonzero : ∃ i, coefficient i ≠ 0

namespace WeakZeroOneCoefficientRelation

/-- Prepend one `{0,1}` coefficient. -/
def prepend {s : List A} {target : A}
    (x : A) (a : ℤ) (ha : a = 0 ∨ a = 1)
    (R : WeakZeroOneCoefficientRelation s target) :
    WeakZeroOneCoefficientRelation (x :: s) (a • x + target) where
  coefficient := fun i ↦ Fin.cases (n := s.length) a R.coefficient i
  zeroOne := by
    intro i
    refine Fin.cases (n := s.length) ha (fun j ↦ R.zeroOne j) i
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

/-- A selected prepended coordinate creates a nonzero relation when the new
target is zero. -/
def toRelation_of_prepend_one {s : List A} {target : A}
    (x : A) (R : WeakZeroOneCoefficientRelation s target)
    (htarget : x + target = 0) :
    ZeroOneCoefficientRelation (x :: s) := by
  let W := R.prepend x 1 (Or.inr rfl)
  exact
    { coefficient := W.coefficient
      zeroOne := W.zeroOne
      weightedSum_eq := by
        simpa using W.weightedSum_eq.trans (by simpa using htarget)
      nonzero := ⟨⟨0, by simp⟩, by simp [W, prepend]⟩ }

/-- Prepending an unselected coordinate preserves a tail relation. -/
def prependZeroRelation {s : List A} (x : A)
    (R : ZeroOneCoefficientRelation s) :
    ZeroOneCoefficientRelation (x :: s) := by
  let W := R.toWeakZeroOneCoefficientRelation.prepend x 0 (Or.inl rfl)
  exact
    { coefficient := W.coefficient
      zeroOne := W.zeroOne
      weightedSum_eq := by simpa using W.weightedSum_eq
      nonzero := by
        rcases R.nonzero with ⟨i, hi⟩
        exact ⟨Fin.succ i, by simpa [W, prepend] using hi⟩ }

end WeakZeroOneCoefficientRelation

/-- Delete zero coefficients from a nonzero `{0,1}` relation to obtain the
project's occurrence-labelled ordinary zero sum. -/
theorem hasNonemptyZeroSum_of_zeroOneCoefficientRelation
    {s : List A} (R : ZeroOneCoefficientRelation s) :
    HasNonemptyZeroSum s := by
  classical
  let I : Selection s := Finset.univ.filter (fun i ↦ R.coefficient i ≠ 0)
  refine ⟨I, ?_, ?_⟩
  · rcases R.nonzero with ⟨i, hi⟩
    exact ⟨i, by simp [I, hi]⟩
  · calc
      (∑ i ∈ I, occurrenceValue s i) =
          ∑ i ∈ I, R.coefficient i • occurrenceValue s i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi0 : R.coefficient i ≠ 0 := by simpa [I] using hi
        rcases R.zeroOne i with hzero | hone
        · exact (hi0 hzero).elim
        · simp [hone]
      _ = ∑ i, R.coefficient i • occurrenceValue s i := by
        apply Finset.sum_subset (Finset.subset_univ I)
        intro i _ hi
        have hzero : R.coefficient i = 0 := by
          rcases R.zeroOne i with hzero | hone
          · exact hzero
          · exfalso
            apply hi
            simp [I, hone]
        simp [hzero]
      _ = 0 := R.weightedSum_eq

/-- The ordinary augmentation product `∏_j ([x_j]-[0])`. -/
noncomputable def ordinaryAugmentationProduct (p : ℕ) (s : List A) :
    PMGroupAlgebra p A :=
  (s.map (augmentationGenerator p)).prod

/-- Every support value of one augmentation factor is either selected (`x`)
or unselected (`0`). -/
theorem mem_support_augmentationGenerator
    (p : ℕ) (x a : A)
    (ha : a ∈ (augmentationGenerator p x).coeff.support) :
    a = x ∨ a = 0 := by
  by_contra h
  simp only [not_or] at h
  apply Finsupp.mem_support_iff.mp ha
  simp [augmentationGenerator, h.1, h.2]

/-- Every support value of the ordinary augmentation product is represented
by an occurrence-indexed `{0,1}` assignment. -/
theorem weakZeroOneRelation_of_mem_support_ordinaryAugmentationProduct
    (p : ℕ) (s : List A) (a : A)
    (ha : a ∈ (ordinaryAugmentationProduct p s).coeff.support) :
    Nonempty (WeakZeroOneCoefficientRelation s a) := by
  classical
  induction s generalizing a with
  | nil =>
      have ha0 : a = 0 := by
        by_contra hne
        apply Finsupp.mem_support_iff.mp ha
        simp [ordinaryAugmentationProduct, AddMonoidAlgebra.one_def, hne]
      subst a
      exact ⟨
        { coefficient := Fin.elim0
          zeroOne := fun i ↦ Fin.elim0 i
          weightedSum_eq := by
            apply Finset.sum_eq_zero
            intro i _
            exact Fin.elim0 i }⟩
  | cons x s ih =>
      have hprodmem :
          a ∈ (augmentationGenerator p x *
            ordinaryAugmentationProduct p s).coeff.support := by
        simpa [ordinaryAugmentationProduct] using ha
      have hmem := AddMonoidAlgebra.support_coeff_mul_subset
        (augmentationGenerator p x) (ordinaryAugmentationProduct p s) hprodmem
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hmem
      rcases ih v hv with ⟨R⟩
      rcases mem_support_augmentationGenerator p x u hu with hux | hu0
      · let W := R.prepend x 1 (Or.inr rfl)
        have W' : WeakZeroOneCoefficientRelation (x :: s) (x + v) := by
          simpa using W
        have htarget : x + v = a := by simpa [hux] using huv
        exact ⟨htarget ▸ W'⟩
      · let W := R.prepend x 0 (Or.inl rfl)
        have W' : WeakZeroOneCoefficientRelation (x :: s) v := by
          simpa using W
        have htarget : v = a := by simpa [hu0] using huv
        exact ⟨htarget ▸ W'⟩

/-- If the source has no nonempty ordinary zero sum, the coefficient of
`[0]` in its augmentation product is exactly `(-1)^length`. -/
theorem coeff_zero_ordinaryAugmentationProduct_of_zeroSumFree
    (p : ℕ) (s : List A) (hfree : ¬HasNonemptyZeroSum s) :
    (ordinaryAugmentationProduct p s).coeff 0 = (-1 : ZMod p) ^ s.length := by
  classical
  induction s with
  | nil => simp [ordinaryAugmentationProduct]
  | cons x s ih =>
      have htail : ¬HasNonemptyZeroSum s := by
        intro hs
        rcases hs with ⟨I, hIne, hIsum⟩
        let R : ZeroOneCoefficientRelation s := by
          let c : Occurrence s → ℤ := fun i ↦ if i ∈ I then 1 else 0
          exact
            { coefficient := c
              zeroOne := by
                intro i
                by_cases hi : i ∈ I
                · exact Or.inr (by simp [c, hi])
                · exact Or.inl (by simp [c, hi])
              nonzero := by
                rcases hIne with ⟨i, hi⟩
                exact ⟨i, by simp [c, hi]⟩
              weightedSum_eq := by
                simp [c, hIsum] }
        exact hfree (hasNonemptyZeroSum_of_zeroOneCoefficientRelation
          (WeakZeroOneCoefficientRelation.prependZeroRelation x R))
      have hx : (ordinaryAugmentationProduct p s).coeff (-x) = 0 := by
        by_contra hne
        have hmem : -x ∈ (ordinaryAugmentationProduct p s).coeff.support :=
          Finsupp.mem_support_iff.mpr hne
        rcases weakZeroOneRelation_of_mem_support_ordinaryAugmentationProduct
            p s (-x) hmem with ⟨R⟩
        exact hfree (hasNonemptyZeroSum_of_zeroOneCoefficientRelation
          (R.toRelation_of_prepend_one x (by simp)))
      rw [show ordinaryAugmentationProduct p (x :: s) =
          augmentationGenerator p x * ordinaryAugmentationProduct p s by rfl]
      unfold augmentationGenerator
      rw [sub_mul]
      simp [hx, ih htail, pow_succ]

/-- Augmentation-product nilpotence gives the ordinary Davenport upper bound
at the same sharp degree. -/
theorem ordinaryDavenportAtMost_of_augmentationProductsVanishAt
    (p D : ℕ) [Fact p.Prime]
    (hnil : AugmentationProductsVanishAt p A D) :
    OrdinaryDavenportAtMost A D := by
  intro s hs
  by_contra hfree
  have hcoeff := coeff_zero_ordinaryAugmentationProduct_of_zeroSumFree
    p s hfree
  have hzero : (ordinaryAugmentationProduct p s).coeff 0 = 0 := by
    rw [ordinaryAugmentationProduct, hnil s (by omega)]
    rfl
  rw [hzero] at hcoeff
  have hne : (-1 : ZMod p) ^ s.length ≠ 0 := pow_ne_zero _ (by simp)
  exact hne hcoeff.symm

/-- The project's exact ordinary Davenport value is unique. -/
theorem isOrdinaryDavenportConstant_unique
    {D E : ℕ} (hD : IsOrdinaryDavenportConstant A D)
    (hE : IsOrdinaryDavenportConstant A E) : D = E := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hDE | hED
  · obtain ⟨s, hslen, hsfree⟩ := hE.2 D hDE
    exact hsfree (hD.1 s hslen)
  · obtain ⟨s, hslen, hsfree⟩ := hD.2 E hED
    exact hsfree (hE.1 s hslen)

/-- An ordinary zero sum is a plus-minus zero sum by assigning the positive
sign to every selected occurrence. -/
theorem plusMinusDavenportAtMost_of_ordinaryDavenportAtMost
    {D : ℕ} (hD : OrdinaryDavenportAtMost A D) :
    PlusMinusDavenportAtMost A D := by
  intro s hs
  rcases hD s hs with ⟨I, hIne, hsum⟩
  refine ⟨I, hIne, fun _ ↦ PlusMinusSign.positive, ?_⟩
  simpa [PlusMinusSign.act] using hsum

end OrdinaryGroupAlgebraExpansion

section InvariantProductGenerators

variable {A ι : Type*} [AddCommGroup A] [Fintype ι]

/-- The pullback of the standard generator in one cyclic coordinate. -/
noncomputable def invariantProductGenerator
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i)))
    (i : ι) : A := by
  classical
  exact e.symm (Pi.single i 1)

/-- The finite generator/exponent list attached to a cyclic-product
presentation. -/
noncomputable def invariantProductGeneratorData
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    List (A × ℕ) := by
  classical
  exact Finset.univ.toList.map fun i ↦
    (invariantProductGenerator p μ e i, μ i)

/-- Each standard cyclic generator is killed by its declared prime power. -/
theorem invariantProductGenerator_order_dvd
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i)))
    (i : ι) :
    p ^ μ i • invariantProductGenerator p μ e i = 0 := by
  classical
  apply e.injective
  ext j
  by_cases hij : i = j
  · subst j
    simp [invariantProductGenerator]
  · simp [invariantProductGenerator, hij]

/-- The pulled-back standard cyclic generators generate the whole additive
group. -/
theorem closure_range_invariantProductGenerator_eq_top
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    AddSubgroup.closure (Set.range (invariantProductGenerator p μ e)) = ⊤ := by
  classical
  apply top_unique
  intro x _
  let H := AddSubgroup.closure (Set.range (invariantProductGenerator p μ e))
  have hgenerator (i : ι) : invariantProductGenerator p μ e i ∈ H :=
    AddSubgroup.subset_closure ⟨i, rfl⟩
  have hcoordinate (i : ι) (a : ZMod (p ^ μ i)) :
      e.symm (Pi.single i a) ∈ H := by
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
    have hsingle : Pi.single i (z : ZMod (p ^ μ i)) =
        z • (Pi.single i (1 : ZMod (p ^ μ i)) :
          ((j : ι) → ZMod (p ^ μ j))) := by
      ext j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [hsingle, map_zsmul]
    exact H.zsmul_mem (hgenerator i) z
  have hx : x = ∑ i, e.symm (Pi.single i ((e x) i)) := by
    apply e.injective
    ext j
    simp
  rw [hx]
  exact AddSubgroup.sum_mem H fun i _ ↦ hcoordinate i ((e x) i)

/-- The concrete finite data list enumerates exactly the range of the
standard generators, hence generates the whole group. -/
theorem invariantProductGeneratorData_generates
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    AddSubgroup.closure
      {x : A | x ∈ (invariantProductGeneratorData p μ e).map Prod.fst} = ⊤ := by
  classical
  rw [← closure_range_invariantProductGenerator_eq_top p μ e]
  congr 1
  ext x
  simp [invariantProductGeneratorData]

/-- Every entry of the concrete finite data list satisfies its declared
prime-power relation. -/
theorem invariantProductGeneratorData_orders
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    ∀ q ∈ invariantProductGeneratorData p μ e,
      p ^ q.2 • q.1 = 0 := by
  classical
  intro q hq
  simp only [invariantProductGeneratorData, List.mem_map,
    Finset.mem_toList] at hq
  rcases hq with ⟨i, _, rfl⟩
  exact invariantProductGenerator_order_dvd p μ e i

/-- The list-based degree is definitionally the invariant-factor sum over
the finite coordinate type. -/
theorem pGroupGeneratorDegree_invariantProductGeneratorData
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    pGroupGeneratorDegree p (invariantProductGeneratorData p μ e) =
      1 + ∑ i, (p ^ μ i - 1) := by
  classical
  unfold pGroupGeneratorDegree invariantProductGeneratorData
  rw [List.map_map]
  change 1 + (Finset.univ.toList.map fun i ↦ p ^ μ i - 1).sum = _
  simp

/-- Olson's ordinary upper bound for an explicit cyclic `p`-power product,
proved from the same augmentation-ideal nilpotence theorem. -/
theorem ordinaryDavenportAtMost_invariantProduct
    (p : ℕ) (hp : p.Prime)
    (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    OrdinaryDavenportAtMost A
      (pGroupGeneratorDegree p (invariantProductGeneratorData p μ e)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply ordinaryDavenportAtMost_of_augmentationProductsVanishAt p
  rw [← finiteNilpotentGeneratorDegree_pGroupData p
    (invariantProductGeneratorData p μ e)]
  exact augmentationProductsVanishAt_of_pGroupGeneratorData p hp
    (invariantProductGeneratorData p μ e)
    (invariantProductGeneratorData_generates p μ e)
    (invariantProductGeneratorData_orders p μ e)

/-- Occurrence labels for the sharp ordinary Davenport lower witness: one
label for each of the `p^μ_i-1` copies in coordinate `i`. -/
abbrev InvariantProductWitnessLabel (p : ℕ) (μ : ι → ℕ) :=
  Σ i : ι, Fin (p ^ μ i - 1)

/-- The standard zero-sum-free candidate containing `p^μ_i-1` copies of
the generator in coordinate `i`. -/
noncomputable def invariantProductDavenportWitness
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    List A := by
  classical
  let Ω := InvariantProductWitnessLabel p μ
  let enum : Fin (Fintype.card Ω) ≃ Ω := (Fintype.equivFin Ω).symm
  exact List.ofFn fun k ↦ invariantProductGenerator p μ e (enum k).1

theorem length_invariantProductDavenportWitness
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    (invariantProductDavenportWitness p μ e).length =
      ∑ i, (p ^ μ i - 1) := by
  classical
  simp [invariantProductDavenportWitness, Fintype.card_sigma]

/-- Occurrences of the lower witness are canonically equivalent to their
coordinate/copy labels. -/
noncomputable def invariantProductWitnessOccurrenceEquiv
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    Occurrence (invariantProductDavenportWitness p μ e) ≃
      InvariantProductWitnessLabel p μ := by
  classical
  let Ω := InvariantProductWitnessLabel p μ
  have hlen : (invariantProductDavenportWitness p μ e).length =
      Fintype.card Ω := by
    simp [invariantProductDavenportWitness, Ω]
  exact (finCongr hlen).trans (Fintype.equivFin Ω).symm

@[simp]
theorem occurrenceValue_invariantProductDavenportWitness
    (p : ℕ) (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i)))
    (k : Occurrence (invariantProductDavenportWitness p μ e)) :
    occurrenceValue (invariantProductDavenportWitness p μ e) k =
      invariantProductGenerator p μ e
        ((invariantProductWitnessOccurrenceEquiv p μ e k).1) := by
  classical
  simp [invariantProductDavenportWitness,
    invariantProductWitnessOccurrenceEquiv, occurrenceValue,
    List.get_eq_getElem]
  congr 2

/-- The standard lower witness is zero-sum-free.  The proof counts selected
occurrences separately in every cyclic coordinate; occurrence labels, not
values, control the multiplicities. -/
theorem invariantProductDavenportWitness_zeroSumFree
    (p : ℕ) (hp : p.Prime) (μ : ι → ℕ)
    (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    ¬HasNonemptyZeroSum (invariantProductDavenportWitness p μ e) := by
  classical
  intro hzero
  rcases hzero with ⟨I, hIne, hsum⟩
  let E := invariantProductWitnessOccurrenceEquiv p μ e
  let countAt (j : ι) : ℕ :=
    (I.filter fun k ↦ (E k).1 = j).card
  have hsumE :
      ∑ k ∈ I, e (occurrenceValue
        (invariantProductDavenportWitness p μ e) k) = 0 := by
    rw [← map_sum, hsum, map_zero]
  have hcountZeroZMod (j : ι) :
      (countAt j : ZMod (p ^ μ j)) = 0 := by
    have hj := congrFun hsumE j
    have hsumCount :
        (∑ k ∈ I, (Pi.single (E k).1
          (1 : ZMod (p ^ μ (E k).1)) :
            ((i : ι) → ZMod (p ^ μ i))) j) =
            (countAt j : ZMod (p ^ μ j)) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkj : (E k).1 = j
      · subst j
        simp
      · simp [hkj]
    have hj' :
        (∑ k ∈ I, (Pi.single (E k).1
            (1 : ZMod (p ^ μ (E k).1)) :
              ((i : ι) → ZMod (p ^ μ i))) j) = 0 := by
      simpa [E, invariantProductGenerator, Finset.sum_apply] using hj
    exact hsumCount.symm.trans hj'
  have hcountLe (j : ι) : countAt j ≤ p ^ μ j - 1 := by
    let C := I.filter fun k ↦ (E k).1 = j
    let f : C → Fin (p ^ μ j - 1) := fun k ↦ by
      have hk : (E k.1).1 = j := (Finset.mem_filter.mp k.2).2
      exact Fin.cast (congrArg (fun i ↦ p ^ μ i - 1) hk) (E k.1).2
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply E.injective
      have ha : (E a.1).1 = j := (Finset.mem_filter.mp a.2).2
      have hb : (E b.1).1 = j := (Finset.mem_filter.mp b.2).2
      have hfst : (E a.1).1 = (E b.1).1 := ha.trans hb.symm
      apply Sigma.ext hfst
      apply (Fin.heq_ext_iff
        (congrArg (fun i ↦ p ^ μ i - 1) hfst)).2
      have habval := congrArg Fin.val hab
      dsimp [f] at habval
      simpa only [Fin.val_cast] using habval
    have hcard := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe] at hcard
    simpa [C, countAt] using hcard
  have hcountZero (j : ι) : countAt j = 0 := by
    have hdiv : p ^ μ j ∣ countAt j :=
      (ZMod.natCast_eq_zero_iff (countAt j) (p ^ μ j)).mp
        (hcountZeroZMod j)
    apply Nat.eq_zero_of_dvd_of_lt hdiv
    have hpos : 0 < p ^ μ j := pow_pos hp.pos _
    exact (hcountLe j).trans_lt (Nat.sub_lt hpos (by omega))
  rcases hIne with ⟨k, hk⟩
  have hkpos : 0 < countAt (E k).1 := by
    apply Finset.card_pos.mpr
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  rw [hcountZero (E k).1] at hkpos
  omega

/-- Olson's exact ordinary Davenport formula for an explicit finite product
of cyclic `p`-power groups. -/
theorem isOrdinaryDavenportConstant_invariantProduct
    (p : ℕ) (hp : p.Prime) (μ : ι → ℕ)
    (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    IsOrdinaryDavenportConstant A
      (pGroupGeneratorDegree p (invariantProductGeneratorData p μ e)) := by
  refine ⟨ordinaryDavenportAtMost_invariantProduct p hp μ e, ?_⟩
  intro n hn
  let w := invariantProductDavenportWitness p μ e
  have hwlen : w.length = ∑ i, (p ^ μ i - 1) :=
    length_invariantProductDavenportWitness p μ e
  have hnle : n ≤ w.length := by
    rw [hwlen]
    rw [pGroupGeneratorDegree_invariantProductGeneratorData p μ e] at hn
    omega
  refine ⟨w.take n, ?_, ?_⟩
  · simp [List.length_take, Nat.min_eq_left hnle]
  · intro hzero
    exact invariantProductDavenportWitness_zeroSumFree p hp μ e
      (hasNonemptyZeroSum_of_take w n hnle hzero)

/-- Proposition 3.1 specialized to an explicit cyclic `p`-power product,
with no generator or nilpotence premise left. -/
theorem plusMinusDavenportAtMost_half_of_invariantProduct
    (p : ℕ) (hp : p.Prime) (hpOdd : Odd p)
    (μ : ι → ℕ) (e : A ≃+ ((i : ι) → ZMod (p ^ μ i))) :
    PlusMinusDavenportAtMost A
      ((pGroupGeneratorDegree p (invariantProductGeneratorData p μ e) + 1) / 2) :=
  plusMinusDavenportAtMost_half_of_pGroupGeneratorData p hp hpOdd
    (invariantProductGeneratorData p μ e)
    (invariantProductGeneratorData_generates p μ e)
    (invariantProductGeneratorData_orders p μ e)

end InvariantProductGenerators

section FinitePGroupClassification

variable (A : Type*) [AddCommGroup A] [Finite A]

/-- The finite-abelian structure theorem specialized to a `p`-group: all
nontrivial primary cyclic factors have the same prime `p`; zero-exponent
factors are harmless copies of `ZMod 1`. -/
theorem exists_invariantProduct_of_isPGroup
    (p : ℕ) (hp : p.Prime) (hA : IsPGroup p (Multiplicative A)) :
    ∃ (ι : Type) (_ : Fintype ι) (μ : ι → ℕ),
      Nonempty (A ≃+ ((i : ι) → ZMod (p ^ μ i))) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι, hι, q, hq, μ, ⟨e⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite A
  letI : Fintype ι := hι
  let eprod : A ≃+ ((i : ι) → ZMod (q i ^ μ i)) :=
    e.trans (DirectSum.addEquivProd fun i ↦ ZMod (q i ^ μ i))
  obtain ⟨n, hcardp⟩ := (IsPGroup.iff_card.mp hA)
  have hcardprod : Nat.card A = ∏ i, q i ^ μ i := by
    calc
      Nat.card A = Nat.card ((i : ι) → ZMod (q i ^ μ i)) :=
        Nat.card_congr eprod.toEquiv
      _ = ∏ i, q i ^ μ i := by
        rw [Nat.card_pi]
        simp [Nat.card_zmod]
  have hcardmul : Nat.card (Multiplicative A) = ∏ i, q i ^ μ i :=
    (Nat.card_congr Multiplicative.toAdd).trans hcardprod
  have hqp (i : ι) (hμ : μ i ≠ 0) : q i = p := by
    have hfactor : q i ^ μ i ∣ ∏ j, q j ^ μ j :=
      Finset.dvd_prod_of_mem (fun j ↦ q j ^ μ j) (Finset.mem_univ i)
    have hqprod : q i ∣ ∏ j, q j ^ μ j :=
      (dvd_pow_self (q i) hμ).trans hfactor
    have hqpow : q i ∣ p ^ n := by
      rw [← hcardp, hcardmul]
      exact hqprod
    have hqdivp : q i ∣ p := (hq i).dvd_of_dvd_pow hqpow
    exact ((hp.dvd_iff_eq (hq i).ne_one).mp hqdivp).symm
  let c : (i : ι) → ZMod (q i ^ μ i) ≃+ ZMod (p ^ μ i) := fun i ↦ by
    by_cases hμ : μ i = 0
    · exact (ZMod.ringEquivCongr (by simp [hμ])).toAddEquiv
    · exact (ZMod.ringEquivCongr (by rw [hqp i hμ])).toAddEquiv
  exact ⟨ι, hι, μ, ⟨eprod.trans (AddEquiv.piCongrRight c)⟩⟩

/-- Olson's invariant-factor formula for an arbitrary finite abelian
`p`-group, with the decomposition data exposed in the conclusion. -/
theorem exists_olsonInvariantProduct
    (p : ℕ) (hp : p.Prime) (hA : IsPGroup p (Multiplicative A)) :
    ∃ (ι : Type) (_ : Fintype ι) (μ : ι → ℕ)
      (_e : A ≃+ ((i : ι) → ZMod (p ^ μ i))),
      IsOrdinaryDavenportConstant A (1 + ∑ i, (p ^ μ i - 1)) := by
  obtain ⟨ι, hι, μ, ⟨e⟩⟩ :=
    exists_invariantProduct_of_isPGroup A p hp hA
  letI : Fintype ι := hι
  refine ⟨ι, hι, μ, e, ?_⟩
  rw [← pGroupGeneratorDegree_invariantProductGeneratorData p μ e]
  exact isOrdinaryDavenportConstant_invariantProduct p hp μ e

/-- Unconditional Proposition 3.1 for finite abelian odd `p`-groups, in the
paper's literal form with an arbitrary exact ordinary Davenport value `D`. -/
theorem plusMinusDavenportAtMost_half_of_isPGroup
    (p D : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hD : IsOrdinaryDavenportConstant A D) :
    PlusMinusDavenportAtMost A ((D + 1) / 2) := by
  obtain ⟨ι, hι, μ, e, hOlson⟩ := exists_olsonInvariantProduct A p hp hA
  letI : Fintype ι := hι
  have hDegree : D = 1 + ∑ i, (p ^ μ i - 1) :=
    isOrdinaryDavenportConstant_unique hD hOlson
  rw [hDegree]
  rw [← pGroupGeneratorDegree_invariantProductGeneratorData p μ e]
  exact plusMinusDavenportAtMost_half_of_invariantProduct
    p hp (hp.odd_of_ne_two hpTwo) μ e

/-- The exact ordinary Davenport value of a finite abelian odd `p`-group is
odd, derived from the invariant-factor formula. -/
theorem odd_ordinaryDavenport_of_isPGroup
    (p D : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hD : IsOrdinaryDavenportConstant A D) : Odd D := by
  obtain ⟨ι, hι, μ, e, hOlson⟩ := exists_olsonInvariantProduct A p hp hA
  letI : Fintype ι := hι
  have hDegree : D = 1 + ∑ i, (p ^ μ i - 1) :=
    isOrdinaryDavenportConstant_unique hD hOlson
  rw [hDegree, ← pGroupGeneratorDegree_invariantProductGeneratorData p μ e]
  exact odd_pGroupGeneratorDegree p (hp.odd_of_ne_two hpTwo)
    (invariantProductGeneratorData p μ e)

/-- The occurrence-labelled restricted-coefficient output used by the high
reflection branch is internal for finite abelian odd `p`-groups. -/
theorem restrictedCoefficientOutputAt_half_of_isPGroup
    (p D : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hD : IsOrdinaryDavenportConstant A D) :
    RestrictedCoefficientOutputAt A ((D + 1) / 2) := by
  obtain ⟨ι, hι, μ, e, hOlson⟩ := exists_olsonInvariantProduct A p hp hA
  letI : Fintype ι := hι
  have hDegree : D = 1 + ∑ i, (p ^ μ i - 1) :=
    isOrdinaryDavenportConstant_unique hD hOlson
  let data := invariantProductGeneratorData p μ e
  have hDegreeData : D = pGroupGeneratorDegree p data := by
    rw [hDegree]
    exact (pGroupGeneratorDegree_invariantProductGeneratorData p μ e).symm
  have hDOdd : Odd D := odd_ordinaryDavenport_of_isPGroup A p D hp hpTwo hA hD
  apply restrictedCoefficientOutputAt_of_augmentationProductsVanishAt
    p D ((D + 1) / 2) hp (hp.odd_of_ne_two hpTwo)
  · rw [twice_half_succ_of_odd hDOdd]
    omega
  · rw [hDegreeData, ← finiteNilpotentGeneratorDegree_pGroupData p data]
    exact augmentationProductsVanishAt_of_pGroupGeneratorData p hp data
      (invariantProductGeneratorData_generates p μ e)
      (invariantProductGeneratorData_orders p μ e)

end FinitePGroupClassification

end GaoLean

#print axioms GaoLean.invariantProductGeneratorData_generates
#print axioms GaoLean.invariantProductGeneratorData_orders
#print axioms GaoLean.ordinaryDavenportAtMost_of_augmentationProductsVanishAt
#print axioms GaoLean.ordinaryDavenportAtMost_invariantProduct
#print axioms GaoLean.invariantProductDavenportWitness_zeroSumFree
#print axioms GaoLean.isOrdinaryDavenportConstant_invariantProduct
#print axioms GaoLean.plusMinusDavenportAtMost_half_of_invariantProduct
#print axioms GaoLean.exists_invariantProduct_of_isPGroup
#print axioms GaoLean.exists_olsonInvariantProduct
#print axioms GaoLean.plusMinusDavenportAtMost_half_of_isPGroup
#print axioms GaoLean.odd_ordinaryDavenport_of_isPGroup
#print axioms GaoLean.restrictedCoefficientOutputAt_half_of_isPGroup
