import GaoLean.PGGMOClaimBSaturation

/-!
# Final ordinary GMO Claim B Case-1 driver

This module mechanically joins the source-faithful counting, subgroup,
indexing, saturation, and labelled-occurrence assembly layers.  Neither the
saturation equality nor the remaining-occurrence estimate is assumed by the
driver: both are produced by the imported verified constructions.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- In the odd-prime p-group setting, the non-large `N ≥ 2` branch of a
source-faithful Theorem-E output produces the complete, occurrence-faithful
Claim-B payload.

The two-cell condition needed by counting is derived internally from the
nontrivial odd-primary ambient group and its canonical `d*` budget;
nontriviality of the period and of the intermediate subgroup, the `d*(K)`
embedding bound, saturation, and the exact reserve count are likewise all
derived rather than exposed as hypotheses. -/
theorem GMOTheoremESourceOutput.nonempty_ordinaryGMOClaimBOutput_case1
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hambient : pGroupDStar A ≤ n)
    (hN : 2 ≤ out.partition.commonCosetCount out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    Nonempty (OrdinaryGMOClaimBOutput xs seed n) := by
  classical
  have hH : out.H ≠ ⊥ := out.period_ne_bot_of_not_large hnotLarge
  letI : Nontrivial out.H :=
    (AddSubgroup.nontrivial_iff_ne_bot out.H).2 hH
  letI : Nontrivial A :=
    Function.Injective.nontrivial out.H.subtype_injective
  have hnTwo : 2 ≤ n :=
    (two_le_pGroupDStar_of_odd_pGroup p hp hpTwo hA).trans hambient
  obtain ⟨g, hg, j, k, hjk, hthick⟩ :=
    out.exists_commonCore_two_cells_large_slice hnTwo hN hnotLarge
  let K := claimBIntermediateSubgroup out.partition out.H g
  have hK : K ≠ ⊥ := by
    dsimp [K]
    exact claimBIntermediateSubgroup_ne_bot_of_two_le_commonCosetCount
      out.partition out.H g hN
  have hr : pGroupDStar K ≤ n := by
    dsimp [K]
    exact pGroupDStar_claimBIntermediateSubgroup_le_of_ambient_budget
      out.partition out.H g hambient
  obtain ⟨e, hne, hfront, hsaturation⟩ :=
    out.partition.exists_pairFrontEmbedding_exact_saturation
      p hp hpTwo hA out.H hH g hg j k hjk hthick (by
        simpa [K] using hr)
  let choice : out.partition.CellCosetOccurrenceChoice K g := by
    dsimp [K]
    exact out.partition.claimBCellCosetOccurrenceChoice out.H g hg
  have hselected :
      ∀ (q : Fin (pGroupDStar K)) (i : Occurrence xs),
        i ∈ out.partition.insideCoreCell out.H (e q) →
          occurrenceValue xs i ∈ addCosetFinset K g := by
    intro q i hi
    dsimp [K]
    exact out.partition.insideCoreCell_value_mem_claimBCoset
      out.H g hg (e q) i hi
  have hallUnused :
      ∀ i : Occurrence xs, i ∉ out.partition.support →
        occurrenceValue xs i ∈ addCosetFinset K g := by
    intro i hi
    dsimp [K]
    exact out.unused_value_mem_claimBCoset g hg hnotLarge i hi
  refine ⟨ordinaryGMOClaimBOutput_of_insideCoreEmbeddedPartition
    out.partition out.H K hK g e ?_ choice hselected hallUnused ?_⟩
  · simpa [K] using hne
  · simpa [K] using hsaturation

end GaoLean

#print axioms GaoLean.GMOTheoremESourceOutput.nonempty_ordinaryGMOClaimBOutput_case1
