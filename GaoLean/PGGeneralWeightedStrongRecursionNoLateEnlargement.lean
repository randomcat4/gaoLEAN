import GaoLean.PGCapacity
import GaoLean.PGGeneralWeightedOvergroupQuotient

/-!
# No late Lemma-3.5 enlargement from a mature strong state

A mature `GeneralWeightedStrongRecursionState` stores the exact number `r` of
occurrences outside its retained carrier, together with the strict upper bound

`r ≤ |G / H| - 2`.

Consequently, once `H < G`, no selection contained in the full outside pool
can have the `|G / H| - 1` occurrences required to trigger the corresponding
Lemma-3.5 enlargement.  This file records that obstruction; it does not
construct a strong state or repair the recursion route.

Thus the source proof's Lemma-3.5 enlargement belongs to the failure branch of
condition (5) for a maximal candidate.  It cannot be postponed until after a
mature strong state already satisfies condition (5), and then be triggered
from that state's full outside pool.

The argument does not use primitivity of the weight set, so the result applies
in particular to primitive states.  The strictness hypothesis is essential:
without it, truncated subtraction on `Nat` makes both thresholds zero when the
quotient is trivial.
-/

namespace GaoLean

universe u

variable {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]

/-- Elementary capacity obstruction.  The lower bound `2 ≤ q` is needed
because subtraction in `Nat` is truncated. -/
theorem not_pred_le_of_le_of_le_sub_two
    {q r m : ℕ} (hq : 2 ≤ q) (hmr : m ≤ r) (hrq : r ≤ q - 2) :
    ¬ (q - 1 ≤ m) := by
  omega

namespace GeneralWeightedStrongRecursionState

variable {W : Set ℤ} {G : AddSubgroup G₀} {gamma delta : G₀}
  {xs : List G₀} {n D : ℕ}

/-- Any occurrence selection contained in the complement of the retained
carrier has cardinality at most the stored residual count `r`. -/
theorem outside_card_le_r
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    {outside : Selection xs}
    (houtside :
      outside ⊆ (Finset.univ : Selection xs) \ S.retained) :
    outside.card ≤ S.r := by
  rw [S.r_eq_complement_card]
  exact Finset.card_le_card houtside

/-- If the state subgroup is proper in its recursive overgroup, no selection
inside the outside pool can reach the internal-quotient predecessor threshold.

This is the precise obstruction to applying the Lemma-3.5 enlargement only
after a mature strong state has already fixed its retained carrier. -/
theorem not_internalQuotient_pred_le_outside_card
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (hHlt : S.H < G)
    {outside : Selection xs}
    (houtside :
      outside ⊆ (Finset.univ : Selection xs) \ S.retained) :
    ¬ (Nat.card (G ⧸ S.H.addSubgroupOf G) - 1 ≤ outside.card) := by
  exact not_pred_le_of_le_of_le_sub_two
    (two_le_natCard_internal_quotient_of_lt S.H G hHlt)
    (S.outside_card_le_r houtside)
    S.r_le_quotient_sub_two

/-- The same obstruction for the full outside pool itself. -/
theorem not_internalQuotient_pred_le_fullOutside_card
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (hHlt : S.H < G) :
    ¬ (Nat.card (G ⧸ S.H.addSubgroupOf G) - 1 ≤
      ((Finset.univ : Selection xs) \ S.retained).card) := by
  exact S.not_internalQuotient_pred_le_outside_card hHlt Finset.Subset.rfl

/-- Cardinal-equivalent formulation in the quotient image
`generalWeightedQuotientSubgroup H G`.  This does not replace the recursive
overgroup by the whole ambient quotient. -/
theorem not_overgroupQuotientSubgroup_pred_le_outside_card
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (hHlt : S.H < G)
    {outside : Selection xs}
    (houtside :
      outside ⊆ (Finset.univ : Selection xs) \ S.retained) :
    ¬ (Nat.card (generalWeightedQuotientSubgroup S.H G) - 1 ≤
      outside.card) := by
  have hcard :
      Nat.card (G ⧸ S.H.addSubgroupOf G) =
        Nat.card (generalWeightedQuotientSubgroup S.H G) :=
    Nat.card_congr
      (generalWeightedInternalQuotientEquiv S.H G S.H_le_G)
  rw [← hcard]
  exact S.not_internalQuotient_pred_le_outside_card hHlt houtside

/-- Quotient-image version for the full outside pool. -/
theorem not_overgroupQuotientSubgroup_pred_le_fullOutside_card
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D)
    (hHlt : S.H < G) :
    ¬ (Nat.card (generalWeightedQuotientSubgroup S.H G) - 1 ≤
      ((Finset.univ : Selection xs) \ S.retained).card) := by
  exact S.not_overgroupQuotientSubgroup_pred_le_outside_card
    hHlt Finset.Subset.rfl

end GeneralWeightedStrongRecursionState

end GaoLean

#print axioms GaoLean.not_pred_le_of_le_of_le_sub_two
#print axioms GaoLean.GeneralWeightedStrongRecursionState.outside_card_le_r
#print axioms GaoLean.GeneralWeightedStrongRecursionState.not_internalQuotient_pred_le_outside_card
#print axioms GaoLean.GeneralWeightedStrongRecursionState.not_internalQuotient_pred_le_fullOutside_card
#print axioms GaoLean.GeneralWeightedStrongRecursionState.not_overgroupQuotientSubgroup_pred_le_outside_card
#print axioms GaoLean.GeneralWeightedStrongRecursionState.not_overgroupQuotientSubgroup_pred_le_fullOutside_card
