import GaoLean.PGGeneralWeightedLemma35
import GaoLean.PGGeneralWeightedArithmetic
import GaoLean.PGGeneralWeightedStep6Numerics
import GaoLean.PGGeneralWeightedReserveAssembly
import GaoLean.PGGMOQuotientLift

/-!
# General-weight Step 1: affine structure from the labelled Lemma 3.5 core

The source proof applies Lemma 3.5 to the zero-adjoined translated cells

`{0} ∪ (-β + W·xᵢ)`.

The presence of the literal zero is essential: a cell which is a singleton
modulo the subgroup returned by Lemma 3.5 must then lie in the subgroup
itself.  Translating back gives one common weighted affine coset.  Primitive
weights then give one common source affine coset, exactly as in Remark B of
the source proof.  All carriers below are genuine source occurrences, so
equal source values at different positions are never identified.

This file deliberately does not assume the desired concentration conclusion.
It constructs the affine data from the zero-adjoined cells and the already
proved general, labelled Lemma 3.5.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance generalWeightedStep1AffineDecidableEq
    {X : Type*} : DecidableEq X :=
  Classical.decEq X

noncomputable local instance generalWeightedStep1AffinePropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The literal finite carrier of a subgroup.  Kept local to the
general-weight development so this module does not depend on the ordinary
Theorem E implementation. -/
noncomputable def weightedStep1SubgroupFinset
    (H : AddSubgroup A) : Finset A := by
  classical
  exact Finset.univ.filter fun x ↦ x ∈ H

@[simp]
theorem mem_weightedStep1SubgroupFinset
    (H : AddSubgroup A) (x : A) :
    x ∈ weightedStep1SubgroupFinset H ↔ x ∈ H := by
  classical
  simp [weightedStep1SubgroupFinset]

/-! ## The literal zero-adjoined translated cell -/

/-- The cell used in source Step 1 after translating a weighted block by
`-β` and adjoining zero. -/
noncomputable def weightedStep1AffineCell
    (W : Set ℤ) (β x : A) : Finset A :=
  ({0} : Finset A) ∪ (weightedValueBlock W x + {-β})

@[simp]
theorem zero_mem_weightedStep1AffineCell
    (W : Set ℤ) (β x : A) :
    0 ∈ weightedStep1AffineCell W β x := by
  classical
  simp [weightedStep1AffineCell]

theorem weighted_sub_center_mem_weightedStep1AffineCell
    (W : Set ℤ) (β x : A) {w : ℤ} (hw : w ∈ W) :
    w • x - β ∈ weightedStep1AffineCell W β x := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_add.mpr
    ⟨w • x, (mem_weightedValueBlock_iff W x (w • x)).2
      ⟨w, hw, rfl⟩, -β, by simp, by simp [sub_eq_add_neg]⟩

/-- Full sumset of the literal Step 1 cells on an occurrence selection. -/
noncomputable def weightedStep1AffineSumset
    (W : Set ℤ) (xs : List A) (β : A) (I : Selection xs) : Finset A :=
  selectedCellSumset
    (fun i : Occurrence xs ↦
      weightedStep1AffineCell W β (occurrenceValue xs i)) I

/-- Membership in the zero-adjoined Step 1 sumset has an honest
occurrence-labelled interpretation: after discarding precisely the cells in
which the adjoined zero was chosen, the remaining choices are allowed
weights on a literal sub-selection of `I`.

The cardinality `k` is deliberately existential.  Replacing it by `I.card`
would silently treat an adjoined zero as a genuine weighted source value and
is false in general. -/
theorem exists_weightedSelection_of_mem_weightedStep1AffineSumset
    (W : Set ℤ) (xs : List A) (β y : A) (I : Selection xs)
    (hy : y ∈ weightedStep1AffineSumset W xs β I) :
    ∃ k : ℕ, k ≤ I.card ∧
      ∃ z : HasWeightedSumOfCard W xs k (k • β + y),
        z.selected ⊆ I := by
  classical
  letI : DecidableEq (Occurrence xs) := instDecidableEqFin xs.length
  induction I using Finset.induction_on generalizing y with
  | empty =>
      have hy0 : y = 0 := by
        simpa [weightedStep1AffineSumset,
          selectedCellSumset_eq_commutativeCellSumset] using hy
      subst y
      refine ⟨0, by simp, ?_⟩
      let z : HasWeightedSumOfCard W xs 0 (0 • β + 0) := {
        selected := ∅
        weights := fun _ ↦ 0
        weights_mem := by simp
        card_selected := by simp
        weighted_sum := by simp
      }
      exact ⟨z, by simp [z]⟩
  | @insert i s hi ih =>
      let cells : Occurrence xs → Finset A := fun j ↦
        weightedStep1AffineCell W β (occurrenceValue xs j)
      have hy' : y ∈ cells i + commutativeCellSumset cells s := by
        change y ∈ selectedCellSumset cells (insert i s) at hy
        rw [selectedCellSumset_eq_commutativeCellSumset] at hy
        have hinsert : commutativeCellSumset cells (insert i s) =
            cells i + commutativeCellSumset cells s := by
          unfold commutativeCellSumset selectedCellSumset indexedCellsOn
          rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
            fullLayerSumSpectrum_eq_iteratedFinsetSum]
          calc
            iteratedFinsetSum (List.map cells (insert i s).toList) =
                iteratedFinsetSum (cells i :: List.map cells s.toList) :=
              iteratedFinsetSum_eq_of_perm_general
                ((Finset.toList_insert hi).map cells)
            _ = cells i + iteratedFinsetSum (List.map cells s.toList) := rfl
        exact Eq.mp
          (congrArg (fun T : Finset A ↦ y ∈ T) hinsert) hy
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hy'
      have hb' : b ∈ weightedStep1AffineSumset W xs β s := by
        change b ∈ selectedCellSumset cells s
        rw [selectedCellSumset_eq_commutativeCellSumset]
        exact hb
      obtain ⟨k, hk, z, hz⟩ := ih b hb'
      change a ∈ ({0} : Finset A) ∪
        (weightedValueBlock W (occurrenceValue xs i) + {-β}) at ha
      rcases Finset.mem_union.mp ha with ha0 | haWeighted
      · have haEq : a = 0 := by simpa using ha0
        have hyEq : y = b := by simpa [haEq] using hab.symm
        rw [hyEq]
        refine ⟨k, ?_, z, ?_⟩
        · have hk' : k ≤ s.card + 1 := hk.trans (Nat.le_succ _)
          simpa [hi, Nat.add_comm] using hk'
        · exact hz.trans (Finset.subset_insert i s)
      · obtain ⟨v, hv, t, ht, hvt⟩ := Finset.mem_add.mp haWeighted
        have htEq : t = -β := by simpa using ht
        obtain ⟨w, hw, hvEq⟩ :=
          (mem_weightedValueBlock_iff W (occurrenceValue xs i) v).1 hv
        have haEq : a = w • occurrenceValue xs i - β := by
          rw [← hvt, hvEq, htEq]
          rw [sub_eq_add_neg]
        let zHead : HasWeightedSumOfCard W xs 1
            (w • occurrenceValue xs i) := {
          selected := {i}
          weights := fun j ↦ if j = i then w else 0
          weights_mem := by
            intro j hj
            have hji : j = i := by simpa using hj
            simpa [hji] using hw
          card_selected := by simp
          weighted_sum := by simp
        }
        have hdis : Disjoint zHead.selected z.selected := by
          rw [Finset.disjoint_left]
          intro j hjHead hjz
          have hji : j = i := by simpa [zHead] using hjHead
          subst j
          exact hi (hz hjz)
        let zUnion := zHead.disjointUnion z hdis
        have htarget :
            w • occurrenceValue xs i + (k • β + b) =
              (1 + k) • β + y := by
          rw [← hab, haEq]
          simp only [add_nsmul, one_nsmul]
          abel
        let zFinal : HasWeightedSumOfCard W xs (1 + k)
            ((1 + k) • β + y) := {
          selected := zUnion.selected
          weights := zUnion.weights
          weights_mem := zUnion.weights_mem
          card_selected := zUnion.card_selected
          weighted_sum := zUnion.weighted_sum.trans htarget
        }
        refine ⟨1 + k, ?_, zFinal, ?_⟩
        · have hk' : 1 + k ≤ s.card + 1 := by omega
          simpa [hi, Nat.add_comm] using hk'
        · intro j hj
          dsimp [zFinal, zUnion] at hj
          rcases Finset.mem_union.mp hj with hjHead | hjTail
          · have hji : j = i := by simpa [zHead] using hjHead
            simpa [hji]
          · exact Finset.mem_insert_of_mem (hz hjTail)

/-- Quotient full sumset of the Step 1 cells modulo an already constructed
affine subgroup. -/
noncomputable def weightedStep1QuotientAffineSumset
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A)
    (I : Selection xs) : Finset (A ⧸ H) :=
  selectedCellSumset
    (fun i : Occurrence xs ↦
      quotientLayer H
        (weightedStep1AffineCell W β (occurrenceValue xs i))) I

/-- A quotient Step 1 sumset member has an honest ambient, occurrence-labelled
weighted interpretation.  Artificial zero choices are discarded, so the
returned cardinality is only bounded by `I.card`; the ambient correction
maps to the original quotient target. -/
theorem exists_weightedSelection_of_mem_weightedStep1QuotientAffineSumset
    (W : Set ℤ) (xs : List A) (H : AddSubgroup A)
    (β : A) (y : A ⧸ H) (I : Selection xs)
    (hy : y ∈ weightedStep1QuotientAffineSumset H W xs β I) :
    ∃ k : ℕ, k ≤ I.card ∧
      ∃ a : A, QuotientAddGroup.mk' H a = y ∧
        ∃ z : HasWeightedSumOfCard W xs k (k • β + a),
          z.selected ⊆ I := by
  classical
  letI : DecidableEq (Occurrence xs) := instDecidableEqFin xs.length
  letI : DecidableEq (A ⧸ H) := Classical.decEq _
  induction I using Finset.induction_on generalizing y with
  | empty =>
      have hy0 : y = 0 := by
        simpa [weightedStep1QuotientAffineSumset,
          selectedCellSumset_eq_commutativeCellSumset] using hy
      subst y
      let z : HasWeightedSumOfCard W xs 0 (0 • β + 0) := {
        selected := ∅
        weights := fun _ ↦ 0
        weights_mem := by simp
        card_selected := by simp
        weighted_sum := by simp
      }
      exact ⟨0, by simp, 0, by simp, z, by simp [z]⟩
  | @insert i s hi ih =>
      let cells : Occurrence xs → Finset (A ⧸ H) := fun j ↦
        quotientLayer H
          (weightedStep1AffineCell W β (occurrenceValue xs j))
      have hy' : y ∈ cells i + commutativeCellSumset cells s := by
        change y ∈ selectedCellSumset cells (insert i s) at hy
        rw [selectedCellSumset_eq_commutativeCellSumset] at hy
        have hinsert : commutativeCellSumset cells (insert i s) =
            cells i + commutativeCellSumset cells s := by
          unfold commutativeCellSumset selectedCellSumset indexedCellsOn
          rw [fullLayerSumSpectrum_eq_iteratedFinsetSum,
            fullLayerSumSpectrum_eq_iteratedFinsetSum]
          calc
            iteratedFinsetSum (List.map cells (insert i s).toList) =
                iteratedFinsetSum (cells i :: List.map cells s.toList) :=
              iteratedFinsetSum_eq_of_perm_general
                ((Finset.toList_insert hi).map cells)
            _ = cells i + iteratedFinsetSum (List.map cells s.toList) := rfl
        exact Eq.mp (congrArg (fun T : Finset (A ⧸ H) ↦ y ∈ T) hinsert) hy
      obtain ⟨qa, hqa, qb, hqb, hab⟩ := Finset.mem_add.mp hy'
      have hqb' :
          qb ∈ weightedStep1QuotientAffineSumset H W xs β s := by
        change qb ∈ selectedCellSumset cells s
        rw [selectedCellSumset_eq_commutativeCellSumset]
        exact hqb
      obtain ⟨k, hk, aTail, haTail, z, hz⟩ := ih qb hqb'
      obtain ⟨c, hc, hcq⟩ :=
        (mem_quotientLayer_iff H
          (weightedStep1AffineCell W β (occurrenceValue xs i)) qa).1 hqa
      change QuotientAddGroup.mk' H c = qa at hcq
      change c ∈ ({0} : Finset A) ∪
        (weightedValueBlock W (occurrenceValue xs i) + {-β}) at hc
      rcases Finset.mem_union.mp hc with hc0 | hcWeighted
      · have hcEq : c = 0 := by simpa using hc0
        have hqaEq : qa = 0 := by
          simpa [hcEq] using hcq.symm
        have hyEq : y = qb := by
          simpa [hqaEq] using hab.symm
        refine ⟨k, ?_, aTail, haTail.trans hyEq.symm, z, ?_⟩
        · have hk' : k ≤ s.card + 1 := hk.trans (Nat.le_succ _)
          simpa [hi, Nat.add_comm] using hk'
        · exact hz.trans (Finset.subset_insert i s)
      · obtain ⟨v, hv, t, ht, hvt⟩ := Finset.mem_add.mp hcWeighted
        have htEq : t = -β := by simpa using ht
        obtain ⟨w, hw, hvEq⟩ :=
          (mem_weightedValueBlock_iff W (occurrenceValue xs i) v).1 hv
        have hcEq : c = w • occurrenceValue xs i - β := by
          rw [← hvt, hvEq, htEq]
          rw [sub_eq_add_neg]
        let zHead : HasWeightedSumOfCard W xs 1
            (w • occurrenceValue xs i) := {
          selected := {i}
          weights := fun j ↦ if j = i then w else 0
          weights_mem := by
            intro j hj
            have hji : j = i := by simpa using hj
            simpa [hji] using hw
          card_selected := by simp
          weighted_sum := by simp
        }
        have hdis : Disjoint zHead.selected z.selected := by
          rw [Finset.disjoint_left]
          intro j hjHead hjz
          have hji : j = i := by simpa [zHead] using hjHead
          subst j
          exact hi (hz hjz)
        let aNew : A := c + aTail
        have haNew : QuotientAddGroup.mk' H aNew = y := by
          dsimp only [aNew]
          rw [map_add, hcq, haTail]
          exact hab
        let zUnion := zHead.disjointUnion z hdis
        have htarget :
            w • occurrenceValue xs i + (k • β + aTail) =
              (1 + k) • β + aNew := by
          dsimp only [aNew]
          rw [hcEq]
          simp only [add_nsmul, one_nsmul]
          abel
        let zFinal : HasWeightedSumOfCard W xs (1 + k)
            ((1 + k) • β + aNew) := {
          selected := zUnion.selected
          weights := zUnion.weights
          weights_mem := zUnion.weights_mem
          card_selected := zUnion.card_selected
          weighted_sum := zUnion.weighted_sum.trans htarget
        }
        refine ⟨1 + k, ?_, aNew, haNew, zFinal, ?_⟩
        · have hk' : 1 + k ≤ s.card + 1 := by omega
          simpa [hi, Nat.add_comm] using hk'
        · intro j hj
          dsimp [zFinal, zUnion] at hj
          rcases Finset.mem_union.mp hj with hjHead | hjTail
          · have hji : j = i := by simpa [zHead] using hjHead
            simpa [hji]
          · exact Finset.mem_insert_of_mem (hz hjTail)

/-- Once the affine centers satisfy equation (3) modulo `H`, a centered
weighted value is exactly the corresponding weighted source difference in
the quotient.  This is the algebraic bridge needed before applying weighted
Davenport arguments to quotient-valued source differences. -/
theorem quotient_weighted_sub_center_eq_zsmul_quotient_sub_center
    (H : AddSubgroup A) (W : Set ℤ) (α β x : A)
    (hα : ∀ w ∈ W, w • α - β ∈ H)
    {w : ℤ} (hw : w ∈ W) :
    QuotientAddGroup.mk' H (w • x - β) =
      w • QuotientAddGroup.mk' H (x - α) := by
  have hcenter :
      w • QuotientAddGroup.mk' H α = QuotientAddGroup.mk' H β := by
    rw [← map_zsmul]
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (hα w hw)
  simp only [map_sub, map_zsmul, smul_sub, hcenter]

/-- Membership version of
`quotient_weighted_sub_center_eq_zsmul_quotient_sub_center` for the full
preimage of a quotient subgroup. -/
theorem weighted_sub_center_mem_liftedAddSubgroup_iff
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (W : Set ℤ) (α β x : A)
    (hα : ∀ w ∈ W, w • α - β ∈ H)
    {w : ℤ} (hw : w ∈ W) :
    w • x - β ∈ liftedAddSubgroup H J ↔
      w • QuotientAddGroup.mk' H (x - α) ∈ J := by
  change QuotientAddGroup.mk' H (w • x - β) ∈ J ↔ _
  rw [quotient_weighted_sub_center_eq_zsmul_quotient_sub_center
    H W α β x hα hw]

/-- Complete a variable-cardinality centered weighted selection to the exact
cardinality of `pool`.  The added labels are chosen by the weighted
Davenport padding theorem from the unused part of `pool` together with a
disjoint reserve whose centered quotient values are literally zero.

The ambient correction `a' - a` therefore vanishes modulo `H`.  In
particular, this is a data-producing completion theorem: it returns an
explicit exact-cardinality weighted selection and does not assume the
desired conclusion through a provider parameter. -/
theorem exists_weightedCenteredFixedCardCompletion
    {W : Set ℤ}
    (xs : List A)
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (α β : A) (hα : ∀ w ∈ W, w • α - β ∈ H)
    (pool reserve : Selection xs)
    (hpool : ∀ i ∈ pool,
      QuotientAddGroup.mk' H (occurrenceValue xs i - α) ∈ J)
    (hreserve : ∀ i ∈ reserve,
      occurrenceValue xs i - α ∈ H)
    (hdis : Disjoint pool reserve)
    (D : ℕ) (hD : IsWeightedDavenportConstant W J D)
    (hreserveCard : D - 1 ≤ reserve.card)
    {k : ℕ} {a : A}
    (z : HasWeightedSumOfCard W xs k (k • β + a))
    (hzpool : z.selected ⊆ pool) :
    ∃ a' : A,
      QuotientAddGroup.mk' H a' = QuotientAddGroup.mk' H a ∧
      ∃ z' : HasWeightedSumOfCard W xs pool.card
          (pool.card • β + a'),
        z'.selected ⊆ pool ∪ reserve := by
  classical
  let qcenter : Occurrence xs → A ⧸ H := fun i ↦
    QuotientAddGroup.mk' H (occurrenceValue xs i - α)
  let f : Occurrence xs → J := fun i ↦
    if hi : qcenter i ∈ J then ⟨qcenter i, hi⟩ else 0
  let rem : Selection xs := pool \ z.selected
  have hremDisjoint : Disjoint rem reserve := by
    exact hdis.mono Finset.sdiff_subset (fun _ hi ↦ hi)
  have hfReserve : ∀ i ∈ reserve, f i = 0 := by
    intro i hi
    have hqzero : qcenter i = 0 := by
      exact (QuotientAddGroup.eq_zero_iff _).2 (hreserve i hi)
    simp [f, hqzero]
  obtain ⟨tail, htailSub, htailCard, weights, hweights, hzero⟩ :=
    exists_weightedZeroSum_padded_selection
      W rem reserve f D hD hremDisjoint hfReserve hreserveCard
  have hfPool : ∀ i ∈ pool, (f i : A ⧸ H) = qcenter i := by
    intro i hi
    have hqi : qcenter i ∈ J := hpool i hi
    simp [f, hqi]
  have hfTail : ∀ i ∈ tail, (f i : A ⧸ H) = qcenter i := by
    intro i hi
    rcases Finset.mem_union.mp (htailSub hi) with hiRem | hiReserve
    · exact hfPool i (Finset.sdiff_subset hiRem)
    · have hqzero : qcenter i = 0 := by
        exact (QuotientAddGroup.eq_zero_iff _).2 (hreserve i hiReserve)
      have hfzero := congrArg (fun y : J ↦ (y : A ⧸ H))
        (hfReserve i hiReserve)
      simpa [hqzero] using hfzero
  have hzTailDisjoint : Disjoint z.selected tail := by
    rw [Finset.disjoint_left]
    intro i hiz hitail
    rcases Finset.mem_union.mp (htailSub hitail) with hiRem | hiReserve
    · exact (Finset.mem_sdiff.mp hiRem).2 hiz
    · exact (Finset.disjoint_left.mp hdis) (hzpool hiz) hiReserve
  let tailSum : A :=
    ∑ i ∈ tail, weights i • occurrenceValue xs i
  let zTail : HasWeightedSumOfCard W xs tail.card tailSum := {
    selected := tail
    weights := weights
    weights_mem := hweights
    card_selected := rfl
    weighted_sum := rfl
  }
  have hkPool : k ≤ pool.card := by
    rw [← z.card_selected]
    exact Finset.card_le_card hzpool
  have hremCard : rem.card = pool.card - k := by
    dsimp only [rem]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hzpool,
      z.card_selected]
  have htotalCard : k + tail.card = pool.card := by
    rw [htailCard, hremCard]
    omega
  have hzeroQuotient :
      (∑ i ∈ tail, weights i • (f i : A ⧸ H)) = 0 := by
    have hcoerced := congrArg (fun y : J ↦ (y : A ⧸ H)) hzero
    simpa using hcoerced
  have hcenterZero :
      QuotientAddGroup.mk' H (tailSum - tail.card • β) = 0 := by
    calc
      QuotientAddGroup.mk' H (tailSum - tail.card • β) =
          ∑ i ∈ tail,
            QuotientAddGroup.mk' H
              (weights i • occurrenceValue xs i - β) := by
            simp [tailSum, Finset.sum_sub_distrib]
      _ = ∑ i ∈ tail, weights i • (f i : A ⧸ H) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [quotient_weighted_sub_center_eq_zsmul_quotient_sub_center
              H W α β (occurrenceValue xs i) hα (hweights i hi), hfTail i hi]
      _ = 0 := hzeroQuotient
  let a' : A := a + (tailSum - tail.card • β)
  have ha' : QuotientAddGroup.mk' H a' = QuotientAddGroup.mk' H a := by
    simp [a', map_add, hcenterZero]
  let zUnion := z.disjointUnion zTail hzTailDisjoint
  have htarget :
      (k • β + a) + tailSum = pool.card • β + a' := by
    dsimp only [a']
    rw [← htotalCard, add_nsmul]
    abel
  let zFinal : HasWeightedSumOfCard W xs pool.card
      (pool.card • β + a') := {
    selected := zUnion.selected
    weights := zUnion.weights
    weights_mem := zUnion.weights_mem
    card_selected := zUnion.card_selected.trans htotalCard
    weighted_sum := zUnion.weighted_sum.trans htarget
  }
  refine ⟨a', ha', zFinal, ?_⟩
  intro i hi
  change i ∈ z.selected ∪ tail at hi
  rcases Finset.mem_union.mp hi with hiz | hitail
  · exact Finset.mem_union_left reserve (hzpool hiz)
  · rcases Finset.mem_union.mp (htailSub hitail) with hiRem | hiReserve
    · exact Finset.mem_union_left reserve (Finset.sdiff_subset hiRem)
    · exact Finset.mem_union_right pool hiReserve

/-- Direct fixed-cardinality consumer for a quotient Step 1 affine-sumset
member.  The quotient member is first realized by a literal variable-card
ambient selection, then completed with genuine unused pool/reserve labels.
-/
theorem exists_weightedFixedCardSelection_of_mem_weightedStep1QuotientAffineSumset
    {W : Set ℤ}
    (xs : List A)
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (α β : A) (hα : ∀ w ∈ W, w • α - β ∈ H)
    (pool reserve : Selection xs)
    (hpool : ∀ i ∈ pool,
      QuotientAddGroup.mk' H (occurrenceValue xs i - α) ∈ J)
    (hreserve : ∀ i ∈ reserve,
      occurrenceValue xs i - α ∈ H)
    (hdis : Disjoint pool reserve)
    (D : ℕ) (hD : IsWeightedDavenportConstant W J D)
    (hreserveCard : D - 1 ≤ reserve.card)
    (y : A ⧸ H)
    (hy : y ∈ weightedStep1QuotientAffineSumset H W xs β pool) :
    ∃ a : A, QuotientAddGroup.mk' H a = y ∧
      ∃ z : HasWeightedSumOfCard W xs pool.card
          (pool.card • β + a),
        z.selected ⊆ pool ∪ reserve := by
  obtain ⟨k, _hk, a, ha, z, hz⟩ :=
    exists_weightedSelection_of_mem_weightedStep1QuotientAffineSumset
      W xs H β y pool hy
  obtain ⟨a', ha', z', hz'⟩ :=
    exists_weightedCenteredFixedCardCompletion
      (W := W) xs H J α β hα pool reserve hpool hreserve hdis
        D hD hreserveCard z hz
  exact ⟨a', ha'.trans ha, z', hz'⟩

/-- The complete labelled affine container at fixed weighted center `β`:
these and only these occurrences have a one-point zero-adjoined cell modulo
`H`. -/
noncomputable def weightedStep1AffineContainer
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A) :
    Selection xs := by
  classical
  exact Finset.univ.filter fun i ↦
    (quotientLayer H
      (weightedStep1AffineCell W β (occurrenceValue xs i))).card = 1

/-- Literal occurrences outside the complete affine container. -/
noncomputable def weightedStep1OutsideAffineContainer
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A) :
    Selection xs :=
  Finset.univ \ weightedStep1AffineContainer H W xs β

@[simp]
theorem mem_weightedStep1AffineContainer_iff
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A)
    (i : Occurrence xs) :
    i ∈ weightedStep1AffineContainer H W xs β ↔
      (quotientLayer H
        (weightedStep1AffineCell W β
          (occurrenceValue xs i))).card = 1 := by
  classical
  simp [weightedStep1AffineContainer]

@[simp]
theorem mem_weightedStep1OutsideAffineContainer_iff
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A)
    (i : Occurrence xs) :
    i ∈ weightedStep1OutsideAffineContainer H W xs β ↔
      (quotientLayer H
        (weightedStep1AffineCell W β
          (occurrenceValue xs i))).card ≠ 1 := by
  classical
  simp [weightedStep1OutsideAffineContainer]

theorem disjoint_weightedStep1AffineContainer_outside
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A) :
    Disjoint (weightedStep1AffineContainer H W xs β)
      (weightedStep1OutsideAffineContainer H W xs β) := by
  classical
  exact Finset.disjoint_sdiff

theorem weightedStep1AffineContainer_union_outside
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A) :
    weightedStep1AffineContainer H W xs β ∪
      weightedStep1OutsideAffineContainer H W xs β = Finset.univ := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

/-! ## Singleton quotient fibers containing zero -/

/-- A nonempty quotient fiber which contains zero and has cardinality one
is the zero fiber. -/
theorem finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
    (H : AddSubgroup A) (B : Finset A)
    (hzero : 0 ∈ B) (hcard : (quotientLayer H B).card = 1) :
    B ⊆ weightedStep1SubgroupFinset H := by
  classical
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have hqzero : (0 : A ⧸ H) ∈ quotientLayer H B :=
    (mem_quotientLayer_iff H B _).2 ⟨0, hzero, rfl⟩
  have hzeroq : (0 : A ⧸ H) = q := by
    rw [hq] at hqzero
    simpa using hqzero
  intro y hy
  have hqy : (y : A ⧸ H) ∈ quotientLayer H B :=
    (mem_quotientLayer_iff H B _).2 ⟨y, hy, rfl⟩
  have hyq : (y : A ⧸ H) = q := by
    rw [hq] at hqy
    simpa using hqy
  apply (mem_weightedStep1SubgroupFinset H y).2
  have heq : (y : A ⧸ H) = (0 : A ⧸ H) := hyq.trans hzeroq.symm
  have hmem := QuotientAddGroup.eq_iff_sub_mem.mp heq
  simpa using hmem

/-- A nonempty finite subset of `H` has the singleton zero quotient layer.
-/
theorem quotientLayer_card_eq_one_of_nonempty_of_subset_subgroup
    (H : AddSubgroup A) (B : Finset A)
    (hB : B.Nonempty) (hsub : ∀ x ∈ B, x ∈ H) :
    (quotientLayer H B).card = 1 := by
  classical
  obtain ⟨b, hb⟩ := hB
  apply Finset.card_eq_one.mpr
  refine ⟨(0 : A ⧸ H), ?_⟩
  ext q
  simp only [mem_quotientLayer_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (QuotientAddGroup.eq_zero_iff x).2
    exact hsub x hx
  · rintro rfl
    refine ⟨b, hb, ?_⟩
    exact (QuotientAddGroup.eq_zero_iff b).2 (hsub b hb)

/-- The one-point quotient condition for a zero-adjoined translated block
is exactly the common weighted `β+H` condition. -/
theorem quotientLayer_weightedStep1AffineCell_card_eq_one_iff
    (H : AddSubgroup A) (W : Set ℤ) (β x : A) :
    (quotientLayer H (weightedStep1AffineCell W β x)).card = 1 ↔
      ∀ w ∈ W, w • x - β ∈ H := by
  classical
  constructor
  · intro hone w hw
    have hsub :=
      finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
        H (weightedStep1AffineCell W β x)
        (zero_mem_weightedStep1AffineCell W β x) hone
    exact (mem_weightedStep1SubgroupFinset H _).1
      (hsub (weighted_sub_center_mem_weightedStep1AffineCell W β x hw))
  · intro hall
    apply quotientLayer_card_eq_one_of_nonempty_of_subset_subgroup
      H (weightedStep1AffineCell W β x)
      ⟨0, zero_mem_weightedStep1AffineCell W β x⟩
    intro y hy
    rcases Finset.mem_union.mp hy with hyzero | hyweighted
    · have : y = 0 := by simpa using hyzero
      simpa [this] using H.zero_mem
    · obtain ⟨z, hz, c, hc, rfl⟩ := Finset.mem_add.mp hyweighted
      have hc' : c = -β := by simpa using hc
      subst c
      obtain ⟨w, hw, rfl⟩ :=
        (mem_weightedValueBlock_iff W x z).1 hz
      simpa [sub_eq_add_neg] using hall w hw

/-- Outside the complete affine container, the quotient Step 1 cell has at
least two elements.  Thus `hcardTwo` is generated by the maximal-container
split rather than assumed for the whole source. -/
theorem two_le_quotientLayer_weightedStep1AffineCell_of_mem_outside
    (H : AddSubgroup A) (W : Set ℤ) (xs : List A) (β : A)
    {i : Occurrence xs}
    (hi : i ∈ weightedStep1OutsideAffineContainer H W xs β) :
    2 ≤ (quotientLayer H
      (weightedStep1AffineCell W β (occurrenceValue xs i))).card := by
  have hne :=
    (mem_weightedStep1OutsideAffineContainer_iff H W xs β i).1 hi
  have hpos :
      0 < (quotientLayer H
        (weightedStep1AffineCell W β (occurrenceValue xs i))).card := by
    apply Finset.card_pos.mpr
    exact ⟨(0 : A ⧸ H),
      (mem_quotientLayer_iff H _ _).2
        ⟨0, zero_mem_weightedStep1AffineCell
          W β (occurrenceValue xs i), rfl⟩⟩
  omega

/-- Remark B in complete-container form.  Once `α` itself has all of its
weighted values in `β+H`, primitive weights identify the complete weighted
container with the complete source coset `α+H`. -/
theorem mem_weightedStep1AffineContainer_iff_sourceCoset
    (H : AddSubgroup A) (W : Set ℤ)
    (hprimitive : IsPrimitiveWeightSet W)
    (α β : A) (hα : ∀ w ∈ W, w • α - β ∈ H)
    (xs : List A) (i : Occurrence xs) :
    i ∈ weightedStep1AffineContainer H W xs β ↔
      occurrenceValue xs i - α ∈ H := by
  rw [mem_weightedStep1AffineContainer_iff,
    quotientLayer_weightedStep1AffineCell_card_eq_one_iff]
  constructor
  · intro hi
    exact sub_mem_addSubgroup_of_common_weightCoset hprimitive hi hα
  · intro hi w hw
    have hsmul : w • (occurrenceValue xs i - α) ∈ H :=
      H.zsmul_mem hi w
    have hadd := H.add_mem hsmul (hα w hw)
    rw [show w • occurrenceValue xs i - β =
      w • (occurrenceValue xs i - α) + (w • α - β) by
        rw [smul_sub]
        abel]
    exact hadd

/-- If every selected zero-containing cell is a singleton modulo `H`, and
its selected full sumset has cardinality `|H|`, then the sumset is literally
the whole subgroup rather than merely a translate of it. -/
theorem selectedCellSumset_eq_subgroupFinset_of_zero_singleton_card
    {X : Type*} [Fintype X]
    (H : AddSubgroup A) (cells : X → Finset A) (s : Finset X)
    (hzero : ∀ i ∈ s, 0 ∈ cells i)
    (hsingle : ∀ i ∈ s, (quotientLayer H (cells i)).card = 1)
    (hcard : (selectedCellSumset cells s).card = Nat.card H) :
    selectedCellSumset cells s = weightedStep1SubgroupFinset H := by
  classical
  have hsumZero : 0 ∈ selectedCellSumset cells s := by
    rw [selectedCellSumset_eq_commutativeCellSumset]
    exact zero_mem_commutativeCellSumset cells s hzero
  have hsumSingle :
      (quotientLayer H (selectedCellSumset cells s)).card = 1 :=
    quotientLayer_selectedCellSumset_card_eq_one H cells s hsingle
  have hsubset : selectedCellSumset cells s ⊆ weightedStep1SubgroupFinset H :=
    finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
      H (selectedCellSumset cells s) hsumZero hsumSingle
  apply Finset.eq_of_subset_of_card_le hsubset
  have hHcard : (weightedStep1SubgroupFinset H).card = Nat.card H := by
    simpa [weightedStep1SubgroupFinset, Nat.card_eq_fintype_card] using
      (Fintype.card_subtype (fun x : A ↦ x ∈ H)).symm
  omega

/-! ## The honest affine profile of the existing weighted certificate -/

/-- A weighted block translated by the distinguished weighted value at the
same occurrence.  Unlike a Step 1 cell centered at one common `β`, this
center is occurrence-dependent. -/
noncomputable def weightedBaseCenteredCell
    (W : Set ℤ) (w₀ : ℤ) (x : A) : Finset A :=
  weightedValueBlock W x + {-(w₀ • x)}

/-- Full sumset of the occurrence-dependent base-centered cells. -/
noncomputable def weightedBaseCenteredSumset
    (W : Set ℤ) (w₀ : ℤ) (xs : List A)
    (I : Selection xs) : Finset A :=
  selectedCellSumset
    (fun i : Occurrence xs ↦
      weightedBaseCenteredCell W w₀ (occurrenceValue xs i)) I

/-- Strongest automatic affine information in a bare
`GeneralWeightedLemma35Certificate`: every retained block becomes a subset
of `H` after its own base-value translation, and the translated core sumset
is exactly `H`.  It intentionally does not claim that the occurrence-wise
centers agree modulo `H`; that stronger common-center fact is supplied by
the zero-adjoined Step 1 construction below. -/
structure GeneralWeightedLemma35AffineProfile
    {W : Set ℤ} {xs : List A} {R : Selection xs}
    {K : AddSubgroup A}
    (C : GeneralWeightedLemma35Certificate W xs R K)
    (w₀ : ℤ) where
  core_centered_sumset :
    weightedBaseCenteredSumset W w₀ xs C.core =
      weightedStep1SubgroupFinset C.H
  retained_weightDifference :
    ∀ i ∈ C.retained, ∀ w ∈ W,
      w • occurrenceValue xs i - w₀ • occurrenceValue xs i ∈ C.H

namespace GeneralWeightedLemma35Certificate

/-- Extract the occurrence-dependent affine profile from the already proved
general-weight Lemma 3.5 specialization. -/
theorem affineProfile
    {W : Set ℤ} {xs : List A} {R : Selection xs}
    {K : AddSubgroup A}
    (C : GeneralWeightedLemma35Certificate W xs R K)
    (w₀ : ℤ) (hw₀ : w₀ ∈ W) :
    GeneralWeightedLemma35AffineProfile C w₀ := by
  classical
  let cells : Occurrence xs → Finset A := fun i ↦
    weightedValueBlock W (occurrenceValue xs i)
  let center : Occurrence xs → A := fun i ↦
    w₀ • occurrenceValue xs i
  have hcellEq (i : Occurrence xs) :
      weightedBaseCenteredCell W w₀ (occurrenceValue xs i) =
        generalTranslatedCells cells center i := by
    rfl
  have hzero :
      ∀ i ∈ C.core,
        0 ∈ weightedBaseCenteredCell W w₀ (occurrenceValue xs i) := by
    intro i _hi
    rw [hcellEq]
    apply zero_mem_generalTranslatedCells
    exact (mem_weightedValueBlock_iff W (occurrenceValue xs i)
      (w₀ • occurrenceValue xs i)).2 ⟨w₀, hw₀, rfl⟩
  have hsingle :
      ∀ i ∈ C.retained,
        (quotientLayer C.H
          (weightedBaseCenteredCell W w₀
            (occurrenceValue xs i))).card = 1 := by
    intro i hi
    rw [hcellEq]
    simpa [cells, center] using C.retained_singleton_mod i hi
  have hsumCard :
      (weightedBaseCenteredSumset W w₀ xs C.core).card =
        Nat.card C.H := by
    calc
      (weightedBaseCenteredSumset W w₀ xs C.core).card =
          (weightedSelectedCellSumset W xs C.core).card := by
        simpa [weightedBaseCenteredSumset, weightedSelectedCellSumset,
          cells, center, hcellEq] using
          card_selectedCellSumset_generalTranslatedCells
            cells center C.core
      _ = Nat.card C.H := C.core_sumset_card
  have hexact :
      weightedBaseCenteredSumset W w₀ xs C.core =
        weightedStep1SubgroupFinset C.H := by
    apply selectedCellSumset_eq_subgroupFinset_of_zero_singleton_card
    · exact hzero
    · intro i hi
      exact hsingle i (C.core_subset_retained hi)
    · exact hsumCard
  have hdiff :
      ∀ i ∈ C.retained, ∀ w ∈ W,
        w • occurrenceValue xs i - w₀ • occurrenceValue xs i ∈ C.H := by
    intro i hi w hw
    have hsub :=
      finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
        C.H
        (weightedBaseCenteredCell W w₀ (occurrenceValue xs i))
        (by
          rw [hcellEq]
          apply zero_mem_generalTranslatedCells
          exact (mem_weightedValueBlock_iff W (occurrenceValue xs i)
            (w₀ • occurrenceValue xs i)).2 ⟨w₀, hw₀, rfl⟩)
        (hsingle i hi)
    apply (mem_weightedStep1SubgroupFinset C.H _).1
    apply hsub
    exact Finset.mem_add.mpr
      ⟨w • occurrenceValue xs i,
        (mem_weightedValueBlock_iff W (occurrenceValue xs i)
          (w • occurrenceValue xs i)).2 ⟨w, hw, rfl⟩,
        -(w₀ • occurrenceValue xs i), by simp,
        by simp [sub_eq_add_neg]⟩
  exact {
    core_centered_sumset := hexact
    retained_weightDifference := hdiff
  }

end GeneralWeightedLemma35Certificate

/-! ## The strong occurrence-faithful affine certificate -/

/-- The affine information extracted in source Step 1 from Lemma 3.5.

The core equality is stronger than the cardinality conclusion of Lemma 3.5:
adjoining zero pins the translate, so its full sumset is exactly `H`.  The
last two fields are the two common affine cosets from the manuscript. -/
structure GeneralWeightedStep1AffineCertificate
    (W : Set ℤ) (xs : List A) (R : Selection xs) (β : A)
    (K : AddSubgroup A) where
  H : AddSubgroup A
  H_le_K : H ≤ K
  H_ne_bot : H ≠ ⊥
  alpha : A
  retained : Selection xs
  core : Selection xs
  retained_subset_R : retained ⊆ R
  core_subset_retained : core ⊆ retained
  retained_card_lower :
    min R.card (R.card - Nat.card (K ⧸ H.addSubgroupOf K) + 2) ≤
      retained.card
  core_card : core.card = Nat.card H - 1
  core_affine_sumset :
    weightedStep1AffineSumset W xs β core = weightedStep1SubgroupFinset H
  retained_weightCoset :
    ∀ i ∈ retained, ∀ w ∈ W,
      w • occurrenceValue xs i - β ∈ H
  retained_sourceCoset :
    ∀ i ∈ retained, occurrenceValue xs i - alpha ∈ H

/-- Build the strong affine certificate from the general labelled Lemma 3.5.
The hypotheses are exactly its genuine cell hypotheses for the literal
zero-adjoined translated cells. -/
theorem generalWeightedStep1AffineCertificate_exists
    (W : Set ℤ) (hprimitive : IsPrimitiveWeightSet W)
    (xs : List A) (R : Selection xs) (β : A)
    (K : AddSubgroup A) (hKne : K ≠ ⊥)
    (hcardTwo :
      ∀ i ∈ R,
        2 ≤ (weightedStep1AffineCell W β
          (occurrenceValue xs i)).card)
    (hsingleK :
      ∀ i ∈ R,
        (quotientLayer K
          (weightedStep1AffineCell W β
            (occurrenceValue xs i))).card = 1)
    (hlength : Nat.card K - 1 ≤ R.card) :
    Nonempty (GeneralWeightedStep1AffineCertificate W xs R β K) := by
  classical
  let cells : ↥R → Finset A := fun j ↦
    weightedStep1AffineCell W β (occurrenceValue xs j.1)
  have hcardTwo' : ∀ j : ↥R, 2 ≤ (cells j).card := by
    intro j
    exact hcardTwo j.1 j.2
  have hsingleK' :
      ∀ j : ↥R, (quotientLayer K (cells j)).card = 1 := by
    intro j
    exact hsingleK j.1 j.2
  have hRcard : Nat.card ↥R = R.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe R
  obtain ⟨C⟩ := generalLemma35Certificate_exists
    K hKne cells hcardTwo' hsingleK'
      (by simpa [hRcard] using hlength)
  let e : ↥R ↪ Occurrence xs :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let retained : Selection xs := C.retained.map e
  let core : Selection xs := C.core.map e
  have hretainedSubset : retained ⊆ R := by
    intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
    exact j.2
  have hcoreSubset : core ⊆ retained := by
    exact Finset.map_subset_map.mpr C.core_subset_retained
  have hretainedLower :
      min R.card (R.card - Nat.card (K ⧸ C.H.addSubgroupOf K) + 2) ≤
        retained.card := by
    simpa [retained, e, hRcard] using C.retained_card_lower
  have hcoreCard : core.card = Nat.card C.H - 1 := by
    simpa [core, e] using C.core_card
  have hcoreSumsetCard :
      (weightedStep1AffineSumset W xs β core).card = Nat.card C.H := by
    change
      (selectedCellSumset
        (fun i : Occurrence xs ↦
          weightedStep1AffineCell W β (occurrenceValue xs i))
        (C.core.map e)).card = Nat.card C.H
    calc
      (selectedCellSumset
          (fun i : Occurrence xs ↦
            weightedStep1AffineCell W β (occurrenceValue xs i))
          (C.core.map e)).card =
          (selectedCellSumset cells C.core).card := by
        simpa [cells, e] using
          congrArg Finset.card
            (selectedCellSumset_subtype_map
              (fun i : Occurrence xs ↦
                weightedStep1AffineCell W β (occurrenceValue xs i))
              C.core).symm
      _ = Nat.card C.H := C.core_sumset_card
  have hsingleton :
      ∀ i ∈ retained,
        (quotientLayer C.H
          (weightedStep1AffineCell W β
            (occurrenceValue xs i))).card = 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact C.retained_singleton_mod j hj
  have hweight :
      ∀ i ∈ retained, ∀ w ∈ W,
        w • occurrenceValue xs i - β ∈ C.H := by
    intro i hi w hw
    have hsub :=
      finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
        C.H
        (weightedStep1AffineCell W β (occurrenceValue xs i))
        (zero_mem_weightedStep1AffineCell W β (occurrenceValue xs i))
        (hsingleton i hi)
    exact (mem_weightedStep1SubgroupFinset C.H _).1
      (hsub (weighted_sub_center_mem_weightedStep1AffineCell
        W β (occurrenceValue xs i) hw))
  let alpha : A := if h : retained.Nonempty then
      occurrenceValue xs h.choose else 0
  have hsource :
      ∀ i ∈ retained, occurrenceValue xs i - alpha ∈ C.H := by
    intro i hi
    by_cases hne : retained.Nonempty
    · rw [show alpha = occurrenceValue xs hne.choose by
        simp [alpha, hne]]
      exact sub_mem_addSubgroup_of_common_weightCoset hprimitive
        (hweight i hi) (hweight hne.choose hne.choose_spec)
    · exact False.elim (hne ⟨i, hi⟩)
  have hcoreExact :
      weightedStep1AffineSumset W xs β core = weightedStep1SubgroupFinset C.H := by
    apply selectedCellSumset_eq_subgroupFinset_of_zero_singleton_card
    · intro i hi
      exact zero_mem_weightedStep1AffineCell W β (occurrenceValue xs i)
    · intro i hi
      exact hsingleton i (hcoreSubset hi)
    · exact hcoreSumsetCard
  exact ⟨{
    H := C.H
    H_le_K := C.H_le_K
    H_ne_bot := C.H_ne_bot
    alpha := alpha
    retained := retained
    core := core
    retained_subset_R := hretainedSubset
    core_subset_retained := hcoreSubset
    retained_card_lower := hretainedLower
    core_card := hcoreCard
    core_affine_sumset := hcoreExact
    retained_weightCoset := hweight
    retained_sourceCoset := hsource
  }⟩

/-! ## Maximal-container enlargement in the quotient -/

/-- The exact output of source Sub-Step 1.2 before its later convolution
with an `H`-full core.  A nonzero quotient subgroup `J ≤ A/H` is lifted to
a subgroup strictly larger than the current affine subgroup `H`.  The core
sumset equality lives in the quotient, exactly as equation (23) in the
source proof. -/
structure GeneralWeightedStep1EnlargementCertificate
    (W : Set ℤ) (xs : List A) (H : AddSubgroup A) (α β : A) where
  J : AddSubgroup (A ⧸ H)
  J_ne_bot : J ≠ ⊥
  H_lt_lifted : H < liftedAddSubgroup H J
  retained : Selection xs
  core : Selection xs
  enlarged : Selection xs
  retained_subset_outside :
    retained ⊆ weightedStep1OutsideAffineContainer H W xs β
  core_subset_retained : core ⊆ retained
  enlarged_eq :
    enlarged = weightedStep1AffineContainer H W xs β ∪ retained
  base_disjoint_retained :
    Disjoint (weightedStep1AffineContainer H W xs β) retained
  enlarged_card :
    enlarged.card =
      (weightedStep1AffineContainer H W xs β).card + retained.card
  retained_card_lower :
    min (weightedStep1OutsideAffineContainer H W xs β).card
      ((weightedStep1OutsideAffineContainer H W xs β).card -
        Nat.card (A ⧸ liftedAddSubgroup H J) + 2) ≤ retained.card
  enlarged_card_lower :
    min xs.length
      (xs.length - Nat.card (A ⧸ liftedAddSubgroup H J) + 2) ≤
        enlarged.card
  enlarged_subset_lifted_container :
    enlarged ⊆ weightedStep1AffineContainer
      (liftedAddSubgroup H J) W xs β
  lifted_container_card_lower :
    min xs.length
      (xs.length - Nat.card (A ⧸ liftedAddSubgroup H J) + 2) ≤
        (weightedStep1AffineContainer
          (liftedAddSubgroup H J) W xs β).card
  core_card : core.card = Nat.card J - 1
  core_quotient_sumset :
    weightedStep1QuotientAffineSumset H W xs β core =
      weightedStep1SubgroupFinset J
  retained_weightCoset :
    ∀ i ∈ retained, ∀ w ∈ W,
      w • occurrenceValue xs i - β ∈ liftedAddSubgroup H J
  retained_sourceCoset :
    ∀ i ∈ retained,
      occurrenceValue xs i - α ∈ liftedAddSubgroup H J
  enlarged_weightCoset :
    ∀ i ∈ enlarged, ∀ w ∈ W,
      w • occurrenceValue xs i - β ∈ liftedAddSubgroup H J
  enlarged_sourceCoset :
    ∀ i ∈ enlarged,
      occurrenceValue xs i - α ∈ liftedAddSubgroup H J
  lifted_container_weightCoset :
    ∀ i ∈ weightedStep1AffineContainer
      (liftedAddSubgroup H J) W xs β, ∀ w ∈ W,
        w • occurrenceValue xs i - β ∈ liftedAddSubgroup H J
  lifted_container_sourceCoset :
    ∀ i ∈ weightedStep1AffineContainer
      (liftedAddSubgroup H J) W xs β,
        occurrenceValue xs i - α ∈ liftedAddSubgroup H J

/-- Source-faithful maximal-container enlargement.  No global two-point
hypothesis is assumed.  The complete fixed-`(H,α,β)` container is removed;
membership in its complement automatically supplies the two-point quotient
cells required by Lemma 3.5. -/
theorem generalWeightedStep1EnlargementCertificate_exists
    (W : Set ℤ) (hprimitive : IsPrimitiveWeightSet W)
    (xs : List A) (H : AddSubgroup A) (hHproper : H < ⊤)
    (α β : A) (hα : ∀ w ∈ W, w • α - β ∈ H)
    (hlength : Nat.card (A ⧸ H) - 1 ≤
      (weightedStep1OutsideAffineContainer H W xs β).card) :
    Nonempty (GeneralWeightedStep1EnlargementCertificate W xs H α β) := by
  classical
  letI : Nontrivial (A ⧸ H) :=
    QuotientAddGroup.nontrivial_iff.mpr hHproper.ne
  let outside : Selection xs :=
    weightedStep1OutsideAffineContainer H W xs β
  let cells : ↥outside → Finset (A ⧸ H) := fun j ↦
    quotientLayer H
      (weightedStep1AffineCell W β (occurrenceValue xs j.1))
  have hcardTwo : ∀ j : ↥outside, 2 ≤ (cells j).card := by
    intro j
    exact two_le_quotientLayer_weightedStep1AffineCell_of_mem_outside
      H W xs β j.2
  have hsingleTop :
      ∀ j : ↥outside,
        (quotientLayer (⊤ : AddSubgroup (A ⧸ H)) (cells j)).card = 1 := by
    intro j
    apply quotientLayer_card_eq_one_of_nonempty_of_subset_subgroup
      (⊤ : AddSubgroup (A ⧸ H)) (cells j)
    · exact ⟨(0 : A ⧸ H),
      (mem_quotientLayer_iff H _ _).2
        ⟨0, zero_mem_weightedStep1AffineCell
          W β (occurrenceValue xs j.1), rfl⟩⟩
    · intro q _hq
      trivial
  have houtsideCard : Nat.card ↥outside = outside.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe outside
  have hlengthOutside : Nat.card (A ⧸ H) - 1 ≤ outside.card := by
    simpa only [outside] using hlength
  have hlengthSubtype : Nat.card (A ⧸ H) - 1 ≤ Nat.card ↥outside := by
    rw [houtsideCard]
    exact hlengthOutside
  have hlengthTop :
      Nat.card (⊤ : AddSubgroup (A ⧸ H)) - 1 ≤ Nat.card ↥outside := by
    simpa using hlengthSubtype
  obtain ⟨C⟩ := generalLemma35Certificate_exists
    (⊤ : AddSubgroup (A ⧸ H)) top_ne_bot cells hcardTwo hsingleTop
      hlengthTop
  let e : ↥outside ↪ Occurrence xs :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let retained : Selection xs := C.retained.map e
  let core : Selection xs := C.core.map e
  have hretainedOutside : retained ⊆ outside := by
    intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
    exact j.2
  have hcoreRetained : core ⊆ retained :=
    Finset.map_subset_map.mpr C.core_subset_retained
  have hcoreCard : core.card = Nat.card C.H - 1 := by
    simpa [core, e] using C.core_card
  have hsingle :
      ∀ i ∈ retained,
        (quotientLayer C.H
          (quotientLayer H
            (weightedStep1AffineCell W β
              (occurrenceValue xs i)))).card = 1 := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact C.retained_singleton_mod j hj
  have hcoreSumsetCard :
      (weightedStep1QuotientAffineSumset H W xs β core).card =
        Nat.card C.H := by
    change
      (selectedCellSumset
        (fun i : Occurrence xs ↦ quotientLayer H
          (weightedStep1AffineCell W β (occurrenceValue xs i)))
        (C.core.map e)).card = Nat.card C.H
    calc
      (selectedCellSumset
          (fun i : Occurrence xs ↦ quotientLayer H
            (weightedStep1AffineCell W β (occurrenceValue xs i)))
          (C.core.map e)).card =
          (selectedCellSumset cells C.core).card := by
        simpa [cells, e] using
          congrArg Finset.card
            (selectedCellSumset_subtype_map
              (fun i : Occurrence xs ↦ quotientLayer H
                (weightedStep1AffineCell W β (occurrenceValue xs i)))
              C.core).symm
      _ = Nat.card C.H := C.core_sumset_card
  have hcoreExact :
      weightedStep1QuotientAffineSumset H W xs β core =
        weightedStep1SubgroupFinset C.H := by
    apply selectedCellSumset_eq_subgroupFinset_of_zero_singleton_card
    · intro i _hi
      exact (mem_quotientLayer_iff H _ _).2
        ⟨0, zero_mem_weightedStep1AffineCell
          W β (occurrenceValue xs i), rfl⟩
    · intro i hi
      exact hsingle i (hcoreRetained hi)
    · exact hcoreSumsetCard
  have hweight :
      ∀ i ∈ retained, ∀ w ∈ W,
        w • occurrenceValue xs i - β ∈ liftedAddSubgroup H C.H := by
    intro i hi w hw
    have hsub :=
      finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
        C.H
        (quotientLayer H
          (weightedStep1AffineCell W β (occurrenceValue xs i)))
        ((mem_quotientLayer_iff H _ _).2
          ⟨0, zero_mem_weightedStep1AffineCell
            W β (occurrenceValue xs i), rfl⟩)
        (hsingle i hi)
    change QuotientAddGroup.mk' H
      (w • occurrenceValue xs i - β) ∈ C.H
    exact (mem_weightedStep1SubgroupFinset C.H _).1
      (hsub ((mem_quotientLayer_iff H _ _).2
        ⟨w • occurrenceValue xs i - β,
          weighted_sub_center_mem_weightedStep1AffineCell
            W β (occurrenceValue xs i) hw, rfl⟩))
  have hsource :
      ∀ i ∈ retained,
        occurrenceValue xs i - α ∈ liftedAddSubgroup H C.H := by
    intro i hi
    apply sub_mem_addSubgroup_of_common_weightCoset hprimitive
      (hweight i hi)
    intro w hw
    exact le_liftedAddSubgroup H C.H (hα w hw)
  letI : Subsingleton
      ((A ⧸ H) ⧸ (⊤ : AddSubgroup (A ⧸ H))) :=
    quotientTop_subsingleton (A := A ⧸ H)
  letI : Unique
      ((A ⧸ H) ⧸ (⊤ : AddSubgroup (A ⧸ H))) :=
    uniqueOfSubsingleton 0
  have htopFactor := natCard_quotient_eq_mul_quotient_subgroupOf
    C.H (⊤ : AddSubgroup (A ⧸ H)) C.H_le_K
  have htopInternal :
      Nat.card ((⊤ : AddSubgroup (A ⧸ H)) ⧸
        C.H.addSubgroupOf (⊤ : AddSubgroup (A ⧸ H))) =
        Nat.card ((A ⧸ H) ⧸ C.H) := by
    simpa using htopFactor.symm
  have hlift := natCard_quotient_liftedAddSubgroup H C.H
  have hquotCard :
      Nat.card ((⊤ : AddSubgroup (A ⧸ H)) ⧸
        C.H.addSubgroupOf (⊤ : AddSubgroup (A ⧸ H))) =
        Nat.card (A ⧸ liftedAddSubgroup H C.H) :=
    htopInternal.trans hlift.symm
  have hretainedLower :
      min outside.card
        (outside.card - Nat.card (A ⧸ liftedAddSubgroup H C.H) + 2) ≤
          retained.card := by
    have h := C.retained_card_lower
    rw [houtsideCard, hquotCard] at h
    simpa [retained, e] using h
  let base : Selection xs := weightedStep1AffineContainer H W xs β
  let enlarged : Selection xs := base ∪ retained
  have hbaseOutside : Disjoint base outside := by
    simpa [base, outside] using
      disjoint_weightedStep1AffineContainer_outside H W xs β
  have hbaseRetained : Disjoint base retained :=
    hbaseOutside.mono_right hretainedOutside
  have henlargedCard : enlarged.card = base.card + retained.card := by
    simpa [enlarged] using Finset.card_union_of_disjoint hbaseRetained
  have hpartition : base ∪ outside = (Finset.univ : Selection xs) := by
    simpa [base, outside] using
      weightedStep1AffineContainer_union_outside H W xs β
  have hpartitionCard : base.card + outside.card = xs.length := by
    rw [← Finset.card_union_of_disjoint hbaseOutside, hpartition]
    simp [Occurrence]
  have hJTwo : 2 ≤ Nat.card C.H :=
    two_le_natCard_addSubgroup_of_ne_bot_step6 C.H C.H_ne_bot
  have hquotPred :
      Nat.card ((A ⧸ H) ⧸ C.H) ≤ Nat.card (A ⧸ H) - 1 := by
    have hpad := natCard_sub_one_add_quotient_le_ambient C.H
    omega
  have hquotOutsideQ :
      Nat.card ((A ⧸ H) ⧸ C.H) ≤ outside.card :=
    hquotPred.trans hlengthOutside
  have hquotOutside :
      Nat.card (A ⧸ liftedAddSubgroup H C.H) ≤ outside.card := by
    rw [hlift]
    exact hquotOutsideQ
  let q := Nat.card (A ⧸ liftedAddSubgroup H C.H)
  have hqOutside : q ≤ outside.card := by
    simpa [q] using hquotOutside
  have hretainedLowerQ :
      min outside.card (outside.card - q + 2) ≤ retained.card := by
    simpa [q] using hretainedLower
  have henlargedLower :
      min xs.length (xs.length - q + 2) ≤ enlarged.card := by
    rw [henlargedCard]
    by_cases hqSmall : q ≤ 2
    · have houtMin : min outside.card (outside.card - q + 2) =
          outside.card := min_eq_left (by omega)
      rw [houtMin] at hretainedLowerQ
      have hretainedLeOutside : retained.card ≤ outside.card :=
        Finset.card_le_card hretainedOutside
      have hretainedEq : retained.card = outside.card := by omega
      rw [hretainedEq, hpartitionCard]
      exact min_le_left _ _
    · have hqThree : 3 ≤ q := by omega
      have houtTarget : outside.card - q + 2 ≤ outside.card := by
        omega
      have htotalTarget : xs.length - q + 2 ≤ xs.length := by
        omega
      rw [min_eq_right houtTarget] at hretainedLowerQ
      rw [min_eq_right htotalTarget]
      omega
  have henlargedWeight :
      ∀ i ∈ enlarged, ∀ w ∈ W,
        w • occurrenceValue xs i - β ∈ liftedAddSubgroup H C.H := by
    intro i hi w hw
    rcases Finset.mem_union.mp hi with hibase | hiretained
    · apply le_liftedAddSubgroup H C.H
      exact
        (quotientLayer_weightedStep1AffineCell_card_eq_one_iff
          H W β (occurrenceValue xs i)).1
          ((mem_weightedStep1AffineContainer_iff H W xs β i).1 hibase)
          w hw
    · exact hweight i hiretained w hw
  have henlargedSource :
      ∀ i ∈ enlarged,
        occurrenceValue xs i - α ∈ liftedAddSubgroup H C.H := by
    intro i hi
    rcases Finset.mem_union.mp hi with hibase | hiretained
    · apply le_liftedAddSubgroup H C.H
      exact (mem_weightedStep1AffineContainer_iff_sourceCoset
        H W hprimitive α β hα xs i).1 hibase
    · exact hsource i hiretained
  have hαLift : ∀ w ∈ W,
      w • α - β ∈ liftedAddSubgroup H C.H := by
    intro w hw
    exact le_liftedAddSubgroup H C.H (hα w hw)
  have henlargedSubsetLifted :
      enlarged ⊆ weightedStep1AffineContainer
        (liftedAddSubgroup H C.H) W xs β := by
    intro i hi
    apply (mem_weightedStep1AffineContainer_iff
      (liftedAddSubgroup H C.H) W xs β i).2
    exact (quotientLayer_weightedStep1AffineCell_card_eq_one_iff
      (liftedAddSubgroup H C.H) W β (occurrenceValue xs i)).2
      (henlargedWeight i hi)
  have hliftedContainerLower :
      min xs.length (xs.length - q + 2) ≤
        (weightedStep1AffineContainer
          (liftedAddSubgroup H C.H) W xs β).card :=
    henlargedLower.trans (Finset.card_le_card henlargedSubsetLifted)
  have hliftedContainerWeight :
      ∀ i ∈ weightedStep1AffineContainer
        (liftedAddSubgroup H C.H) W xs β, ∀ w ∈ W,
          w • occurrenceValue xs i - β ∈ liftedAddSubgroup H C.H := by
    intro i hi
    exact (quotientLayer_weightedStep1AffineCell_card_eq_one_iff
      (liftedAddSubgroup H C.H) W β (occurrenceValue xs i)).1
      ((mem_weightedStep1AffineContainer_iff
        (liftedAddSubgroup H C.H) W xs β i).1 hi)
  have hliftedContainerSource :
      ∀ i ∈ weightedStep1AffineContainer
        (liftedAddSubgroup H C.H) W xs β,
          occurrenceValue xs i - α ∈ liftedAddSubgroup H C.H := by
    intro i hi
    exact (mem_weightedStep1AffineContainer_iff_sourceCoset
      (liftedAddSubgroup H C.H) W hprimitive α β hαLift xs i).1 hi
  exact ⟨{
    J := C.H
    J_ne_bot := C.H_ne_bot
    H_lt_lifted := lt_liftedAddSubgroup_of_ne_bot H C.H C.H_ne_bot
    retained := retained
    core := core
    enlarged := enlarged
    retained_subset_outside := by simpa [outside] using hretainedOutside
    core_subset_retained := hcoreRetained
    enlarged_eq := by rfl
    base_disjoint_retained := by simpa [base] using hbaseRetained
    enlarged_card := by simpa [base] using henlargedCard
    retained_card_lower := by simpa [outside] using hretainedLower
    enlarged_card_lower := by simpa [q] using henlargedLower
    enlarged_subset_lifted_container := henlargedSubsetLifted
    lifted_container_card_lower := by simpa [q] using hliftedContainerLower
    core_card := hcoreCard
    core_quotient_sumset := hcoreExact
    retained_weightCoset := hweight
    retained_sourceCoset := hsource
    enlarged_weightCoset := henlargedWeight
    enlarged_sourceCoset := henlargedSource
    lifted_container_weightCoset := hliftedContainerWeight
    lifted_container_sourceCoset := hliftedContainerSource
  }⟩

/-! ## Ambient Step 1 and the source full/concentration alternative -/

/-- Every nonempty finite set has a singleton image modulo the full
subgroup. -/
theorem quotientLayer_top_card_eq_one_of_nonempty
    (B : Finset A) (hB : B.Nonempty) :
    (quotientLayer (⊤ : AddSubgroup A) B).card = 1 := by
  classical
  letI : Subsingleton (A ⧸ (⊤ : AddSubgroup A)) :=
    quotientTop_subsingleton (A := A)
  obtain ⟨b, hb⟩ := hB
  apply Finset.card_eq_one.mpr
  refine ⟨(b : A ⧸ (⊤ : AddSubgroup A)), ?_⟩
  ext q
  simp only [mem_quotientLayer_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subsingleton.elim _ _
  · intro _hq
    exact ⟨b, hb, Subsingleton.elim _ _⟩

/-- Ambient specialization of the affine certificate.  The quotient-layer
hypothesis disappears because every zero-adjoined cell is nonempty modulo
the full group. -/
theorem generalWeightedStep1AffineCertificate_exists_top
    [Nontrivial A]
    (W : Set ℤ) (hprimitive : IsPrimitiveWeightSet W)
    (xs : List A) (R : Selection xs) (β : A)
    (hcardTwo :
      ∀ i ∈ R,
        2 ≤ (weightedStep1AffineCell W β
          (occurrenceValue xs i)).card)
    (hlength : Nat.card A - 1 ≤ R.card) :
    Nonempty (GeneralWeightedStep1AffineCertificate W xs R β ⊤) := by
  apply generalWeightedStep1AffineCertificate_exists
    W hprimitive xs R β ⊤ top_ne_bot hcardTwo
  · intro i _hi
    apply quotientLayer_top_card_eq_one_of_nonempty
    exact ⟨0, zero_mem_weightedStep1AffineCell
      W β (occurrenceValue xs i)⟩
  · simpa using hlength

namespace GeneralWeightedStep1AffineCertificate

/-- Exact labelled reserve bridge for the selection-convolution stage.
Only the genuine additive capacity is required; the reserve is chosen from
`retained \ core`, so it is automatically disjoint from the affine core and
remains inside the retained concentration pool. -/
noncomputable def extractReserve
    {W : Set ℤ} {xs : List A} {R : Selection xs} {β : A}
    {K : AddSubgroup A}
    (C : GeneralWeightedStep1AffineCertificate W xs R β K)
    (k : ℕ) (hbudget : C.core.card + k ≤ C.retained.card) :
    OccurrenceReserveExtraction xs C.retained C.core k :=
  extractOccurrenceReserveOfCoreCardAddLe
    C.retained C.core k hbudget

/-- In the ambient specialization, a proper subgroup returned by the
affine certificate is already the exact manuscript concentration witness.
The exceptional-count lower bound is discharged from the original
`min`-bound using properness, not supplied as an extra premise. -/
theorem nonempty_concentration_of_top_univ
    {W : Set ℤ} {xs : List A} {β : A}
    (C : GeneralWeightedStep1AffineCertificate
      W xs (Finset.univ : Selection xs) β ⊤)
    (hproper : C.H < ⊤)
    (hlength : Nat.card A - 1 ≤ xs.length) :
    Nonempty (WeightedGMOConcentration W xs) := by
  classical
  letI : Subsingleton (A ⧸ (⊤ : AddSubgroup A)) :=
    quotientTop_subsingleton (A := A)
  letI : Unique (A ⧸ (⊤ : AddSubgroup A)) :=
    uniqueOfSubsingleton 0
  have hfactor := natCard_quotient_eq_mul_quotient_subgroupOf
    C.H (⊤ : AddSubgroup A) C.H_le_K
  have hinternal :
      Nat.card ((⊤ : AddSubgroup A) ⧸
        C.H.addSubgroupOf (⊤ : AddSubgroup A)) =
        Nat.card (A ⧸ C.H) := by
    simpa using hfactor.symm
  have hqTwo : 2 ≤ Nat.card (A ⧸ C.H) :=
    two_le_natCard_quotient_of_lt_top C.H hproper
  have hHq := natCard_add_quotient_le_ambient_of_ne_bot_of_lt_top
    C.H C.H_ne_bot hproper
  have hHTwo := two_le_natCard_addSubgroup_of_ne_bot_step6
    C.H C.H_ne_bot
  have htargetLe :
      xs.length - Nat.card (A ⧸ C.H) + 2 ≤ xs.length := by
    omega
  have hcard :
      xs.length - Nat.card (A ⧸ C.H) + 2 ≤ C.retained.card := by
    have h := C.retained_card_lower
    have hunivCard :
        (Finset.univ : Selection xs).card = xs.length := by
      simp [Occurrence]
    rw [hunivCard, hinternal, min_eq_right htargetLe] at h
    exact h
  exact ⟨{
    K := C.H
    strict := hproper
    alpha := C.alpha
    beta := β
    selected := C.retained
    sourceCoset := C.retained_sourceCoset
    weightCoset := C.retained_weightCoset
    card_lower := hcard
  }⟩

end GeneralWeightedStep1AffineCertificate

/-- The full branch of ambient Step 1.  It records a literal labelled core
of `|A|-1` zero-adjoined translated cells whose full sumset is all of `A`.
-/
structure GeneralWeightedStep1FullAffineCore
    (W : Set ℤ) (xs : List A) (β : A) where
  core : Selection xs
  core_card : core.card = Nat.card A - 1
  core_affine_sumset :
    weightedStep1AffineSumset W xs β core = Finset.univ

/-- Strong ambient Step 1 alternative: either a literal full affine core or
the complete source concentration witness with common source and weighted
centers. -/
theorem generalWeightedStep1_fullAffineCore_or_concentration
    [Nontrivial A]
    (W : Set ℤ) (hprimitive : IsPrimitiveWeightSet W)
    (xs : List A) (β : A)
    (hcardTwo :
      ∀ i : Occurrence xs,
        2 ≤ (weightedStep1AffineCell W β
          (occurrenceValue xs i)).card)
    (hlength : Nat.card A - 1 ≤ xs.length) :
    Nonempty (GeneralWeightedStep1FullAffineCore W xs β) ∨
      Nonempty (WeightedGMOConcentration W xs) := by
  classical
  have hcardTwo' :
      ∀ i ∈ (Finset.univ : Selection xs),
        2 ≤ (weightedStep1AffineCell W β
          (occurrenceValue xs i)).card := by
    intro i _hi
    exact hcardTwo i
  obtain ⟨C⟩ := generalWeightedStep1AffineCertificate_exists_top
    W hprimitive xs (Finset.univ : Selection xs) β hcardTwo'
      (by simpa using hlength)
  rcases C.H_le_K.eq_or_lt with htop | hproper
  · left
    refine ⟨{
      core := C.core
      core_card := ?_
      core_affine_sumset := ?_
    }⟩
    · simpa [htop] using C.core_card
    · rw [C.core_affine_sumset, htop]
      ext x
      simp [weightedStep1SubgroupFinset]
  · right
    exact C.nonempty_concentration_of_top_univ hproper hlength

end GaoLean

#print axioms GaoLean.exists_weightedSelection_of_mem_weightedStep1AffineSumset
#print axioms GaoLean.exists_weightedSelection_of_mem_weightedStep1QuotientAffineSumset
#print axioms GaoLean.quotient_weighted_sub_center_eq_zsmul_quotient_sub_center
#print axioms GaoLean.weighted_sub_center_mem_liftedAddSubgroup_iff
#print axioms GaoLean.exists_weightedCenteredFixedCardCompletion
#print axioms GaoLean.exists_weightedFixedCardSelection_of_mem_weightedStep1QuotientAffineSumset
#print axioms GaoLean.finset_subset_subgroupFinset_of_zero_mem_of_quotientLayer_card_eq_one
#print axioms GaoLean.selectedCellSumset_eq_subgroupFinset_of_zero_singleton_card
#print axioms GaoLean.GeneralWeightedLemma35Certificate.affineProfile
#print axioms GaoLean.quotientLayer_weightedStep1AffineCell_card_eq_one_iff
#print axioms GaoLean.two_le_quotientLayer_weightedStep1AffineCell_of_mem_outside
#print axioms GaoLean.mem_weightedStep1AffineContainer_iff_sourceCoset
#print axioms GaoLean.generalWeightedStep1AffineCertificate_exists
#print axioms GaoLean.generalWeightedStep1EnlargementCertificate_exists
#print axioms GaoLean.quotientLayer_top_card_eq_one_of_nonempty
#print axioms GaoLean.generalWeightedStep1AffineCertificate_exists_top
#print axioms GaoLean.GeneralWeightedStep1AffineCertificate.extractReserve
#print axioms GaoLean.GeneralWeightedStep1AffineCertificate.nonempty_concentration_of_top_univ
#print axioms GaoLean.generalWeightedStep1_fullAffineCore_or_concentration
