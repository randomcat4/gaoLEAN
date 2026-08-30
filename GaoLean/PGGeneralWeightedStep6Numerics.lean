import GaoLean.PGGeneralWeightedDavenportMinimum
import GaoLean.PGGMOOrdinaryLiftedSubgroupCore
import Mathlib.GroupTheory.Coset.Card

/-!
# Numerical bridges for Step 6 of the general weighted GMO proof

This file contains only finite-cardinality and truncated-natural-number
bookkeeping.  In particular, it records exactly how much source length
remains after the subgroup or Davenport padding is removed.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-! ## Subgroup--quotient cardinal padding -/

/-- For positive natural factors, their overlap-corrected sum is bounded by
their product. -/
theorem generalWeighted_add_sub_one_le_mul_of_pos
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b - 1 ≤ a * b := by
  by_cases haOne : a = 1
  · simp [haOne]
  by_cases hbOne : b = 1
  · simp [hbOne]
  have haTwo : 2 ≤ a := by omega
  have hbTwo : 2 ≤ b := by omega
  have hab := Nat.add_le_mul haTwo hbTwo
  omega

/-- The subgroup and quotient orders fit in the ambient order after sharing
one common label.  No nontriviality assumption on `H` is needed. -/
theorem natCard_add_quotient_sub_one_le_ambient
    (H : AddSubgroup A) :
    Nat.card H + Nat.card (A ⧸ H) - 1 ≤ Nat.card A := by
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  rw [hfactor, Nat.mul_comm]
  exact generalWeighted_add_sub_one_le_mul_of_pos
    (Nat.card H) (Nat.card (A ⧸ H)) Nat.card_pos Nat.card_pos

/-- Equivalent padding form used when a full quotient witness is lifted:
`|H|-1` subgroup labels plus one representative for each quotient class fit
inside the ambient group. -/
theorem natCard_sub_one_add_quotient_le_ambient
    (H : AddSubgroup A) :
    Nat.card H - 1 + Nat.card (A ⧸ H) ≤ Nat.card A := by
  have hpad := natCard_add_quotient_sub_one_le_ambient H
  have hHpos : 1 ≤ Nat.card H := Nat.card_pos
  omega

/-- A nontrivial finite subgroup has at least two elements. -/
theorem two_le_natCard_addSubgroup_of_ne_bot_step6
    (H : AddSubgroup A) (hH : H ≠ ⊥) :
    2 ≤ Nat.card H := by
  have hHone : Nat.card H ≠ 1 := by
    simpa using hH
  have hHpos : 0 < Nat.card H := Nat.card_pos
  omega

/-- A proper finite subgroup has a quotient with at least two elements. -/
theorem two_le_natCard_quotient_of_lt_top_step6
    (H : AddSubgroup A) (hH : H < ⊤) :
    2 ≤ Nat.card (A ⧸ H) := by
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hlt : Nat.card H < Nat.card A := by
    have hlt' : Nat.card H < Nat.card (⊤ : AddSubgroup A) := by
      change (H : Set A).ncard < ((⊤ : AddSubgroup A) : Set A).ncard
      exact Set.ncard_lt_ncard hH
    simpa using hlt'
  have hQpos : 0 < Nat.card (A ⧸ H) := Nat.card_pos
  by_contra hnot
  have hQone : Nat.card (A ⧸ H) = 1 := by omega
  rw [hQone, one_mul] at hfactor
  omega

/-- A proper nontrivial subgroup supplies one extra unit of cardinal slack:
`|H| + |A/H| ≤ |A|`. -/
theorem natCard_add_quotient_le_ambient_of_ne_bot_of_lt_top
    (H : AddSubgroup A) (hHbot : H ≠ ⊥) (hHtop : H < ⊤) :
    Nat.card H + Nat.card (A ⧸ H) ≤ Nat.card A := by
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  rw [hfactor, Nat.mul_comm]
  exact Nat.add_le_mul
    (two_le_natCard_addSubgroup_of_ne_bot_step6 H hHbot)
    (two_le_natCard_quotient_of_lt_top_step6 H hHtop)

/-- If an ambient critical-length source loses `|H|-1` labelled positions,
the retained source still meets the quotient critical length with the same
Davenport parameter.  All subtraction is `Nat.sub`, including small cases.
-/
theorem quotient_critical_length_le_after_subgroup_pred_deletion
    (H : AddSubgroup A) (D L : ℕ)
    (hL : Nat.card A + D - 1 ≤ L) :
    Nat.card (A ⧸ H) + D - 1 ≤ L - (Nat.card H - 1) := by
  have hpad := natCard_add_quotient_sub_one_le_ambient H
  have hHpos : 1 ≤ Nat.card H := Nat.card_pos
  have hQpos : 1 ≤ Nat.card (A ⧸ H) := Nat.card_pos
  omega

/-- Symmetric retained-length form: deleting `|A/H|-1` positions leaves the
subgroup critical length. -/
theorem subgroup_critical_length_le_after_quotient_pred_deletion
    (H : AddSubgroup A) (D L : ℕ)
    (hL : Nat.card A + D - 1 ≤ L) :
    Nat.card H + D - 1 ≤ L - (Nat.card (A ⧸ H) - 1) := by
  have hpad := natCard_add_quotient_sub_one_le_ambient H
  have hHpos : 1 ≤ Nat.card H := Nat.card_pos
  have hQpos : 1 ≤ Nat.card (A ⧸ H) := Nat.card_pos
  omega

/-! ## Canonical weighted Davenport budgets -/

/-- The canonical weighted Davenport value of a subgroup is no larger than
the ambient value. -/
theorem weightedDavenportValue_subgroup_le_ambient
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) :
    weightedDavenportValue W H hW ≤ weightedDavenportValue W A hW := by
  have hconv := weightedDavenportValue_subgroup_quotient W A hW H
  have hQpos : 0 < weightedDavenportValue W (A ⧸ H) hW :=
    weightedDavenportConstant_pos W _
      (weightedDavenportValue_spec W (A ⧸ H) hW)
  omega

/-- The canonical weighted Davenport value of the quotient is no larger
than the ambient value. -/
theorem weightedDavenportValue_quotient_le_ambient
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) :
    weightedDavenportValue W (A ⧸ H) hW ≤
      weightedDavenportValue W A hW := by
  have hconv := weightedDavenportValue_subgroup_quotient W A hW H
  have hHpos : 0 < weightedDavenportValue W H hW :=
    weightedDavenportConstant_pos W _
      (weightedDavenportValue_spec W H hW)
  omega

/-- Step 6 quotient budget after only the `|H|-1` subgroup padding has been
removed. -/
theorem weightedStep6_quotient_length_after_subgroup_pred
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    Nat.card (A ⧸ H) + weightedDavenportValue W (A ⧸ H) hW - 1 ≤
      L - (Nat.card H - 1) := by
  have hsame := quotient_critical_length_le_after_subgroup_pred_deletion
    H (weightedDavenportValue W A hW) L hL
  have hDQle := weightedDavenportValue_quotient_le_ambient hW H
  have hQpos : 1 ≤ Nat.card (A ⧸ H) := Nat.card_pos
  omega

/-- Symmetric Step 1 budget after the quotient representative padding has
been removed. -/
theorem weightedStep1_subgroup_length_after_quotient_pred
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    Nat.card H + weightedDavenportValue W H hW - 1 ≤
      L - (Nat.card (A ⧸ H) - 1) := by
  have hsame := subgroup_critical_length_le_after_quotient_pred_deletion
    H (weightedDavenportValue W A hW) L hL
  have hDHle := weightedDavenportValue_subgroup_le_ambient hW H
  have hHpos : 1 ≤ Nat.card H := Nat.card_pos
  omega

/-- Exact combined padding budget obtained from both cardinal factorization
and the canonical subgroup--quotient Davenport convolution.  The subgroup
side spends `|H| + D_H - 2`, leaving the full quotient critical length
`|A/H| + D_Q - 1`.

Without proper-nontrivial cardinal slack, the `-2` is essential: replacing
it by `-1` is not justified by the available convolution
`D_H + D_Q ≤ D_A + 1`.  A later theorem records the sharper proper-
nontrivial form. -/
theorem weighted_subgroupPadding_add_quotientCritical_le_length
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    (Nat.card H + weightedDavenportValue W H hW - 2) +
        (Nat.card (A ⧸ H) +
          weightedDavenportValue W (A ⧸ H) hW - 1) ≤ L := by
  have hpad := natCard_add_quotient_sub_one_le_ambient H
  have hconv := weightedDavenportValue_subgroup_quotient W A hW H
  have hHcardPos : 1 ≤ Nat.card H := Nat.card_pos
  have hQcardPos : 1 ≤ Nat.card (A ⧸ H) := Nat.card_pos
  have hDHpos : 0 < weightedDavenportValue W H hW :=
    weightedDavenportConstant_pos W _ (weightedDavenportValue_spec W H hW)
  have hDQpos : 0 < weightedDavenportValue W (A ⧸ H) hW :=
    weightedDavenportConstant_pos W _
      (weightedDavenportValue_spec W (A ⧸ H) hW)
  omega

/-- Truncated-subtraction form of the preceding combined budget. -/
theorem weightedStep6_quotient_length_after_subgroupDavenportPadding
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    Nat.card (A ⧸ H) + weightedDavenportValue W (A ⧸ H) hW - 1 ≤
      L - (Nat.card H + weightedDavenportValue W H hW - 2) := by
  have hsplit :=
    weighted_subgroupPadding_add_quotientCritical_le_length hW H L hL
  omega

/-- Symmetric combined padding budget for a subgroup recursive call. -/
theorem weighted_quotientPadding_add_subgroupCritical_le_length
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    (Nat.card (A ⧸ H) +
        weightedDavenportValue W (A ⧸ H) hW - 2) +
      (Nat.card H + weightedDavenportValue W H hW - 1) ≤ L := by
  have hpad := natCard_add_quotient_sub_one_le_ambient H
  have hconv := weightedDavenportValue_subgroup_quotient W A hW H
  have hHcardPos : 1 ≤ Nat.card H := Nat.card_pos
  have hQcardPos : 1 ≤ Nat.card (A ⧸ H) := Nat.card_pos
  have hDHpos : 0 < weightedDavenportValue W H hW :=
    weightedDavenportConstant_pos W _ (weightedDavenportValue_spec W H hW)
  have hDQpos : 0 < weightedDavenportValue W (A ⧸ H) hW :=
    weightedDavenportConstant_pos W _
      (weightedDavenportValue_spec W (A ⧸ H) hW)
  omega

/-- In the proper-nontrivial recursive branch, the extra cardinal unit pays
for the otherwise missing convolution unit.  Thus the subgroup may spend
the sharper padding `|H| + D_H - 1` while the complete quotient critical
length remains available. -/
theorem weighted_properSubgroupPadding_add_quotientCritical_le_length
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A)
    (hHbot : H ≠ ⊥) (hHtop : H < ⊤) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    (Nat.card H + weightedDavenportValue W H hW - 1) +
        (Nat.card (A ⧸ H) +
          weightedDavenportValue W (A ⧸ H) hW - 1) ≤ L := by
  have hpad :=
    natCard_add_quotient_le_ambient_of_ne_bot_of_lt_top H hHbot hHtop
  have hconv := weightedDavenportValue_subgroup_quotient W A hW H
  have hHcardPos : 1 ≤ Nat.card H := Nat.card_pos
  have hQcardPos : 1 ≤ Nat.card (A ⧸ H) := Nat.card_pos
  have hDHpos : 0 < weightedDavenportValue W H hW :=
    weightedDavenportConstant_pos W _ (weightedDavenportValue_spec W H hW)
  have hDQpos : 0 < weightedDavenportValue W (A ⧸ H) hW :=
    weightedDavenportConstant_pos W _
      (weightedDavenportValue_spec W (A ⧸ H) hW)
  omega

/-- Truncated retained-length form of the sharp proper-nontrivial budget. -/
theorem weightedStep6_quotient_length_after_properSubgroupPadding
    {W : Set ℤ} (hW : W.Nonempty) (H : AddSubgroup A)
    (hHbot : H ≠ ⊥) (hHtop : H < ⊤) (L : ℕ)
    (hL : Nat.card A + weightedDavenportValue W A hW - 1 ≤ L) :
    Nat.card (A ⧸ H) + weightedDavenportValue W (A ⧸ H) hW - 1 ≤
      L - (Nat.card H + weightedDavenportValue W H hW - 1) := by
  have hsplit :=
    weighted_properSubgroupPadding_add_quotientCritical_le_length
      hW H hHbot hHtop L hL
  omega

/-! ## Internal-overgroup critical threshold -/

/-- The source-length hypotheses of the strong recursion leave enough room
for the critical weighted core of every subgroup `K ≤ G`, measured against
the internal quotient `G/K`.

This is intentionally an internal-overgroup statement.  It does not replace
`G/K` by the generally larger ambient quotient `A/K`; an overgroup-aware
Step 1 certificate is still needed before this bound can supply a lifted
affine-container lower bound in the recursive branch. -/
theorem weighted_internalCritical_le_source_retained_threshold
    {W : Set ℤ} (hW : W.Nonempty)
    (K G : AddSubgroup A) (hKG : K ≤ G)
    (DK D n L : ℕ)
    (hDK : IsWeightedDavenportConstant W K DK)
    (hD : IsWeightedDavenportConstant W G D)
    (hn : Nat.card G ≤ n)
    (hL : n + D - 1 ≤ L) :
    Nat.card K + DK - 1 ≤
      min L
        (L - Nat.card (G ⧸ K.addSubgroupOf G) + 2) := by
  letI : Fintype G := Fintype.ofFinite G
  let Ki := K.addSubgroupOf G
  let DQ := weightedDavenportValue W (G ⧸ Ki) hW
  have hKi : IsWeightedDavenportConstant W Ki DK :=
    isWeightedDavenportConstant_addEquiv W
      (AddSubgroup.addSubgroupOfEquivOfLe hKG).symm hDK
  have hDQ : IsWeightedDavenportConstant W (G ⧸ Ki) DQ :=
    weightedDavenportValue_spec W (G ⧸ Ki) hW
  have hconv : DK + DQ ≤ D + 1 :=
    weightedDavenport_subgroup_quotient W Ki D DK DQ hD hKi hDQ
  have hDQpos : 1 ≤ DQ :=
    weightedDavenportConstant_pos W DQ hDQ
  have hDKle : DK ≤ D := by omega
  have hKiCard : Nat.card Ki = Nat.card K :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hKG)
  have hcard := natCard_add_quotient_sub_one_le_ambient (A := G) Ki
  rw [hKiCard] at hcard
  have hQpos : 1 ≤ Nat.card (G ⧸ Ki) := Nat.card_pos
  change Nat.card K + DK - 1 ≤
    min L (L - Nat.card (G ⧸ Ki) + 2)
  rw [Nat.le_min]
  constructor
  · omega
  · omega

/-! ## Lifted subgroup capacity -/

/-- Exact weighted Davenport constants on `H` and `J` obey the internal
subgroup--quotient convolution after `J` is lifted back to the ambient group.
The exactness witnesses are transported through the additive equivalences in
the short exact sequence `H → lift(H,J) → J`. -/
theorem weightedDavenport_lifted_subgroup_quotient
    {W : Set ℤ} (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (DH DJ DK : ℕ)
    (hH : IsWeightedDavenportConstant W H DH)
    (hJ : IsWeightedDavenportConstant W J DJ)
    (hK : IsWeightedDavenportConstant W (liftedAddSubgroup H J) DK) :
    DH + DJ ≤ DK + 1 := by
  let K := liftedAddSubgroup H J
  let Hinside := internalAddSubgroup H K
  have hHinside : IsWeightedDavenportConstant W Hinside DH :=
    isWeightedDavenportConstant_addEquiv W
      (internalAddSubgroupEquiv H K (le_liftedAddSubgroup H J)).symm hH
  have hQ : IsWeightedDavenportConstant W (K ⧸ Hinside) DJ :=
    isWeightedDavenportConstant_addEquiv W
      (liftedInternalQuotientEquiv H J).symm hJ
  exact weightedDavenport_subgroup_quotient W Hinside DK DH DJ hK hHinside hQ

/-- The old `H`-full core, the `|J|-1` quotient pool, and a `D_J-1`
zero-reserve all fit inside the critical capacity of the lifted subgroup.
This is the carrier budget needed before choosing a filler and assembling the
parent full core. -/
theorem weighted_liftedCore_pool_reserve_capacity
    {W : Set ℤ} (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (DH DJ DK : ℕ)
    (hH : IsWeightedDavenportConstant W H DH)
    (hJ : IsWeightedDavenportConstant W J DJ)
    (hK : IsWeightedDavenportConstant W (liftedAddSubgroup H J) DK) :
    (Nat.card H + DH - 1) + (Nat.card J - 1) + (DJ - 1) ≤
      Nat.card (liftedAddSubgroup H J) + DK - 1 := by
  have hcard : Nat.card H + Nat.card J - 1 ≤
      Nat.card (liftedAddSubgroup H J) := by
    rw [natCard_liftedAddSubgroup H J]
    exact generalWeighted_add_sub_one_le_mul_of_pos
      (Nat.card H) (Nat.card J) Nat.card_pos Nat.card_pos
  have hconv := weightedDavenport_lifted_subgroup_quotient
    H J DH DJ DK hH hJ hK
  have hHcardPos : 1 ≤ Nat.card H := Nat.card_pos
  have hJcardPos : 1 ≤ Nat.card J := Nat.card_pos
  have hKcardPos : 1 ≤ Nat.card (liftedAddSubgroup H J) := Nat.card_pos
  have hDHpos := weightedDavenportConstant_pos W DH hH
  have hDJpos := weightedDavenportConstant_pos W DJ hJ
  have hDKpos := weightedDavenportConstant_pos W DK hK
  omega

/-- After reserving the old full core, quotient pool, and local zero reserve,
the fixed filler needed to raise an `|H| + |J| - 1` realization to exactly
`|lift(H,J)|` also fits in the new critical core carrier. -/
theorem weighted_liftedCore_pool_reserve_filler_capacity
    {W : Set ℤ} (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (DH DJ DK : ℕ)
    (hH : IsWeightedDavenportConstant W H DH)
    (hJ : IsWeightedDavenportConstant W J DJ)
    (hK : IsWeightedDavenportConstant W (liftedAddSubgroup H J) DK) :
    (Nat.card H + DH - 1) + (Nat.card J - 1) + (DJ - 1) +
        (Nat.card (liftedAddSubgroup H J) -
          (Nat.card H + Nat.card J - 1)) ≤
      Nat.card (liftedAddSubgroup H J) + DK - 1 := by
  have hbase : Nat.card H + Nat.card J - 1 ≤
      Nat.card (liftedAddSubgroup H J) := by
    rw [natCard_liftedAddSubgroup H J]
    exact generalWeighted_add_sub_one_le_mul_of_pos
      (Nat.card H) (Nat.card J) Nat.card_pos Nat.card_pos
  have hconv := weightedDavenport_lifted_subgroup_quotient
    H J DH DJ DK hH hJ hK
  have hHcardPos : 1 ≤ Nat.card H := Nat.card_pos
  have hJcardPos : 1 ≤ Nat.card J := Nat.card_pos
  have hDHpos := weightedDavenportConstant_pos W DH hH
  have hDJpos := weightedDavenportConstant_pos W DJ hJ
  have hDKpos := weightedDavenportConstant_pos W DK hK
  omega

end GaoLean

#print axioms GaoLean.natCard_add_quotient_sub_one_le_ambient
#print axioms GaoLean.natCard_sub_one_add_quotient_le_ambient
#print axioms GaoLean.quotient_critical_length_le_after_subgroup_pred_deletion
#print axioms GaoLean.weightedDavenportValue_subgroup_le_ambient
#print axioms GaoLean.weightedDavenportValue_quotient_le_ambient
#print axioms GaoLean.weightedStep6_quotient_length_after_subgroup_pred
#print axioms GaoLean.weightedStep1_subgroup_length_after_quotient_pred
#print axioms GaoLean.weighted_subgroupPadding_add_quotientCritical_le_length
#print axioms GaoLean.weightedStep6_quotient_length_after_subgroupDavenportPadding
#print axioms GaoLean.weighted_quotientPadding_add_subgroupCritical_le_length
#print axioms GaoLean.natCard_add_quotient_le_ambient_of_ne_bot_of_lt_top
#print axioms GaoLean.weighted_properSubgroupPadding_add_quotientCritical_le_length
#print axioms GaoLean.weighted_internalCritical_le_source_retained_threshold
#print axioms GaoLean.weightedDavenport_lifted_subgroup_quotient
#print axioms GaoLean.weighted_liftedCore_pool_reserve_capacity
#print axioms GaoLean.weighted_liftedCore_pool_reserve_filler_capacity
#print axioms GaoLean.weightedStep6_quotient_length_after_properSubgroupPadding
