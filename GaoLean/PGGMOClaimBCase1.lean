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

The two-cell condition needed by counting is derived internally from
`N ≤ |A/H| ≤ |A| ≤ n`; nontriviality of the period and of the intermediate
subgroup, the `d*(K)` embedding bound, saturation, and the exact reserve
count are likewise all derived rather than exposed as hypotheses. -/
theorem GMOTheoremESourceOutput.nonempty_ordinaryGMOClaimBOutput_case1
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hnA : Nat.card A ≤ n)
    (hN : 2 ≤ out.partition.commonCosetCount out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    Nonempty (OrdinaryGMOClaimBOutput xs seed n) := by
  classical
  letI : Fintype (A ⧸ out.H) := Fintype.ofFinite (A ⧸ out.H)
  have hNquot : out.partition.commonCosetCount out.H ≤
      Nat.card (A ⧸ out.H) := by
    rw [← out.partition.card_quotientLayer_commonCore_eq_commonCosetCount
      out.H]
    simpa using Finset.card_le_univ
      (quotientLayer out.H (out.partition.commonCore out.H))
  have hquotA : Nat.card (A ⧸ out.H) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos out.H.card_quotient_dvd_card
  have hnTwo : 2 ≤ n :=
    hN.trans (hNquot.trans (hquotA.trans hnA))
  obtain ⟨g, hg, j, k, hjk, hthick⟩ :=
    out.exists_commonCore_two_cells_large_slice hnTwo hN hnotLarge
  let K := claimBIntermediateSubgroup out.partition out.H g
  have hH : out.H ≠ ⊥ := out.period_ne_bot_of_not_large hnotLarge
  have hK : K ≠ ⊥ := by
    dsimp [K]
    exact claimBIntermediateSubgroup_ne_bot_of_two_le_commonCosetCount
      out.partition out.H g hN
  have hr : pGroupDStar K ≤ n := by
    dsimp [K]
    exact pGroupDStar_claimBIntermediateSubgroup_le_of_natCard_le
      out.partition out.H g hnA
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
