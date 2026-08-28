import GaoLean.PGGMOClaimBTarget

/-!
# The top-subgroup terminal branch of ordinary GMO Claim B

When the honest Claim-B subgroup is the whole ambient group, its exact
`d*(K)` saturation can absorb an arbitrary displacement.  We choose the
remaining labels from the literal unused-occurrence reserve and then use
the labelled sumset extraction theorem for the complementary target.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A genuine Claim-B witness with top subgroup fills the entire ordinary
exact spectrum at the prescribed length.  The proof retains the literal
occurrence ledger: the first `d*(K)` labels lie in the replacement support,
the remaining `n-d*(K)` labels lie in `unusedInAddCoset`, and the two parts
are disjoint. -/
theorem OrdinaryGMOClaimBOutput.ordinarySpectrumFull_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hrn : pGroupDStar W.K ≤ n)
    (hKtop : W.K = ⊤) :
    OrdinarySpectrumFull xs n := by
  classical
  intro y
  let r : ℕ := pGroupDStar W.K
  let U : Selection xs := W.partition.unusedInAddCoset W.K W.g
  have htailLe : n - r ≤ U.card := by
    dsimp [r, U]
    exact le_trans (Nat.le_add_right (n - pGroupDStar W.K)
      (xs.length - seed.card)) W.remaining_in_coset
  obtain ⟨tail, htailSub, htailCard⟩ :=
    Finset.exists_subset_card_eq (s := U) htailLe
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i
  let firstTarget : A := y - tailSum
  have hfirstTargetSumset : firstTarget ∈ W.partition.sumset := by
    rw [W.saturation]
    simp [hKtop]
  obtain ⟨first, hfirstSub, hfirstCard, hfirstSum⟩ :=
    W.partition.exists_selection_subset_support_of_mem_sumset
      hfirstTargetSumset
  have hdisj : Disjoint first tail := by
    rw [Finset.disjoint_left]
    intro i hiFirst hiTail
    have hiUnused := (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1
      (htailSub hiTail)
    exact hiUnused.1 (hfirstSub hiFirst)
  refine ⟨first ∪ tail, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hfirstCard, htailCard]
    exact Nat.add_sub_of_le hrn
  · rw [Finset.sum_union hdisj, hfirstSum]
    dsimp [firstTarget, tailSum]
    abel

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.ordinarySpectrumFull_of_K_eq_top
