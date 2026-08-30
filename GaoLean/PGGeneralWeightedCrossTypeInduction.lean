import GaoLean.PGGeneralWeightedOvergroupQuotient

/-!
# Cross-type cardinal induction for the strong general-weight recursion

The fixed-ambient engine in `PGGeneralWeightedStrongRecursionState` is useful
for recursive calls to strict subgroups of one ambient group.  The source GMO
proof also recurses after changing the ambient type, most notably to quotient
groups.  Consequently, strict-subgroup induction inside one fixed `G₀` is not
by itself a sufficient scheduler.

This file records the honest cross-type scheduler.  Its induction rank is the
cardinality of the recursive subgroup, not the cardinality of the ambient
overgroup.  The local mathematical step remains an explicit input: no value of
the engine is constructed here.
-/

namespace GaoLean

universe u

/-! ## Cross-type hypotheses and their honest specializations -/

/-- The recursion hypothesis available at a subgroup `G`: the strong theorem
may be used for a subgroup of any finite additive overgroup of the same
universe, provided that its cardinality is strictly smaller than `|G|`.

This is deliberately stronger in scope than
`GeneralWeightedStrictSubgroupRecursionHypothesis G`, whose recursive groups
must all live in the original fixed ambient type. -/
def GeneralWeightedCrossTypeSmallerCardRecursionHypothesis
    {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]
    (G : AddSubgroup G₀) : Prop :=
  ∀ (G₁ : Type u) [AddCommGroup G₁] [Fintype G₁]
    (K : AddSubgroup G₁),
      Nat.card K < Nat.card G → GeneralWeightedStrongRecursionAt K

namespace GeneralWeightedCrossTypeSmallerCardRecursionHypothesis

/-- A cross-type smaller-card hypothesis contains the old fixed-ambient
strict-subgroup hypothesis.  The only extra fact used is that strict inclusion
of finite additive subgroups strictly lowers cardinality. -/
theorem toFixedAmbientStrictSubgroup
    {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]
    {G : AddSubgroup G₀}
    (ih : GeneralWeightedCrossTypeSmallerCardRecursionHypothesis G) :
    GeneralWeightedStrictSubgroupRecursionHypothesis G := by
  intro K hKG
  exact ih G₀ K (natCard_lt_of_addSubgroup_lt hKG)

/-- A strict subgroup `K < G` may itself be used as the new ambient type.
The recursive target is its top subgroup, whose cardinality is exactly
`Nat.card K`; hence the cross-type hypothesis applies without changing the
mathematical rank. -/
theorem applySubgroupTop
    {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]
    {G : AddSubgroup G₀}
    (ih : GeneralWeightedCrossTypeSmallerCardRecursionHypothesis G)
    (K : AddSubgroup G₀) [Fintype K] (hKG : K < G) :
    GeneralWeightedStrongRecursionAt (⊤ : AddSubgroup K) := by
  apply ih K (⊤ : AddSubgroup K)
  rw [AddSubgroup.card_top]
  exact natCard_lt_of_addSubgroup_lt hKG

/-- Generic quotient-type entrance for the cross-type induction hypothesis.

The caller must prove the honest rank decrease for the particular recursive
subgroup `K` of `G₀ ⧸ L`.  This lemma supplies no mathematical quotient step;
it only makes explicit that changing the ambient type is permitted once that
decrease is known. -/
theorem applyQuotient
    {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]
    {G : AddSubgroup G₀}
    (ih : GeneralWeightedCrossTypeSmallerCardRecursionHypothesis G)
    (L : AddSubgroup G₀) [Fintype (G₀ ⧸ L)]
    (K : AddSubgroup (G₀ ⧸ L))
    (hKcard : Nat.card K < Nat.card G) :
    GeneralWeightedStrongRecursionAt K :=
  ih (G₀ ⧸ L) K hKcard

/-- Apply the cross-type induction hypothesis to the image of `G` in the
ambient quotient by a nontrivial `L ≤ G`.

Unlike `applyQuotient`, this entry point proves the rank decrease internally;
the caller supplies only the mathematical subgroup hypotheses. -/
theorem applyGeneralWeightedQuotient
    {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]
    {G L : AddSubgroup G₀}
    (ih : GeneralWeightedCrossTypeSmallerCardRecursionHypothesis G)
    [Fintype (G₀ ⧸ L)]
    (hLG : L ≤ G) (hL : ⊥ < L) :
    GeneralWeightedStrongRecursionAt
      (generalWeightedQuotientSubgroup L G) :=
  ih.applyQuotient L (generalWeightedQuotientSubgroup L G)
    (natCard_generalWeightedQuotientSubgroup_lt hLG hL)

end GeneralWeightedCrossTypeSmallerCardRecursionHypothesis

/-! ## Ranked propositions and the local-step boundary -/

/-- The cross-type strong theorem at one exact recursive-subgroup cardinality.
The ambient overgroup is universally quantified and need not have cardinality
`m`; only the recursive subgroup does. -/
def GeneralWeightedStrongRecursionAtCard (m : ℕ) : Prop :=
  ∀ (G₀ : Type u) [AddCommGroup G₀] [Fintype G₀]
    (G : AddSubgroup G₀),
      Nat.card G = m → GeneralWeightedStrongRecursionAt G

/-- Interface for the substantive local proof at one subgroup.  Its only
recursive input is the cross-type strictly-smaller-card strong theorem. -/
structure GeneralWeightedCrossTypeRecursionStepInterface
    {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]
    (G : AddSubgroup G₀) : Prop where
  run : GeneralWeightedCrossTypeSmallerCardRecursionHypothesis G →
    GeneralWeightedStrongRecursionAt G

/-- A uniform family of honest cross-type local steps.  This structure is an
unproved mathematical obligation; the present module never constructs it. -/
structure GeneralWeightedCrossTypeRecursionEngine : Prop where
  step : ∀ (G₀ : Type u) [AddCommGroup G₀] [Fintype G₀]
    (G : AddSubgroup G₀),
      GeneralWeightedCrossTypeRecursionStepInterface G

/-! ## The scheduler -/

/-- An honest cross-type engine proves the strong theorem at every exact
recursive-subgroup cardinality.  `Nat.strong_induction_on` is the sole
well-founded scheduler; all substantive mathematics remains in `engine.step`.
-/
theorem generalWeightedStrongRecursionAtCard_of_crossTypeEngine
    (engine : GeneralWeightedCrossTypeRecursionEngine.{u}) :
    ∀ m, GeneralWeightedStrongRecursionAtCard.{u} m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro G₀ _instGroup _instFintype G hGcard
      refine (engine.step G₀ G).run ?_
      intro G₁ _instGroup₁ _instFintype₁ K hKcard
      exact (ih (Nat.card K) (by simpa [hGcard] using hKcard))
        G₁ K rfl

/-- Eliminate the exact-card index after the cross-type engine has supplied
every local step.  This theorem is conditional on the engine and therefore is
not itself an implementation of the GMO local recursion step. -/
theorem generalWeightedStrongRecursionAt_of_crossTypeEngine
    (engine : GeneralWeightedCrossTypeRecursionEngine.{u}) :
    ∀ (G₀ : Type u) [AddCommGroup G₀] [Fintype G₀]
      (G : AddSubgroup G₀), GeneralWeightedStrongRecursionAt G := by
  intro G₀ _instGroup _instFintype G
  exact generalWeightedStrongRecursionAtCard_of_crossTypeEngine engine
    (Nat.card G) G₀ G rfl

end GaoLean

#print axioms GaoLean.GeneralWeightedCrossTypeSmallerCardRecursionHypothesis.toFixedAmbientStrictSubgroup
#print axioms GaoLean.GeneralWeightedCrossTypeSmallerCardRecursionHypothesis.applySubgroupTop
#print axioms GaoLean.GeneralWeightedCrossTypeSmallerCardRecursionHypothesis.applyQuotient
#print axioms GaoLean.GeneralWeightedCrossTypeSmallerCardRecursionHypothesis.applyGeneralWeightedQuotient
#print axioms GaoLean.generalWeightedStrongRecursionAtCard_of_crossTypeEngine
#print axioms GaoLean.generalWeightedStrongRecursionAt_of_crossTypeEngine
