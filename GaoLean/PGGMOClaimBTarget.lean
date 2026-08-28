import GaoLean.PGGMOClaimBAssembly

/-!
# Closing ordinary GMO Claim B at the prescribed length

This module turns the occurrence-faithful Claim-B payload into the exact
prescribed-length target.  The construction keeps the two labelled pieces
separate: a tail is cut from the literal unused-occurrence complement, and
the saturated first block is then chosen to cancel its subgroup displacement.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Membership in the full layer sumset lifts to one labelled occurrence
from every cell.  Besides the cardinality and sum ledger, the selected
occurrences are retained inside the literal replacement support. -/
theorem Theorem21SetPartition.exists_selection_subset_support_of_mem_sumset
    {xs : List A} {r m : ℕ} (P : Theorem21SetPartition xs r m)
    {y : A} (hy : y ∈ P.sumset) :
    ∃ I : Selection xs,
      I ⊆ P.support ∧ I.card = r ∧
        (∑ i ∈ I, occurrenceValue xs i) = y := by
  classical
  rw [Theorem21SetPartition.sumset] at hy
  rw [mem_fullLayerSumSpectrum_iff_exists_choice] at hy
  obtain ⟨a, ha, hsum⟩ := hy
  let e : Fin r ≃ Fin P.valueCells.length :=
    finCongr P.length_valueCells.symm
  let a' : Fin r → A := fun c ↦ a (e c)
  have ha' : ∀ c : Fin r, a' c ∈ P.valueCell c := by
    intro c
    have hc := ha (e c)
    simp only [Theorem21SetPartition.valueCells, List.get_ofFn] at hc
    dsimp only [a']
    convert hc using 1
    · congr 1
    · rfl
  have hsum' : (∑ c, a' c) = y := (e.sum_comp a).trans hsum
  have hpick : ∀ c : Fin r, ∃ i : Occurrence xs,
      i ∈ P.cells c ∧ occurrenceValue xs i = a' c := by
    intro c
    simpa [Theorem21SetPartition.valueCell] using ha' c
  let pick : Fin r → Occurrence xs := fun c ↦ Classical.choose (hpick c)
  have pick_mem (c : Fin r) : pick c ∈ P.cells c :=
    (Classical.choose_spec (hpick c)).1
  have pick_value (c : Fin r) : occurrenceValue xs (pick c) = a' c :=
    (Classical.choose_spec (hpick c)).2
  have pick_injective : Function.Injective pick := by
    intro c d hcd
    by_contra hne
    have hdisj := P.cells_pairwise_disjoint hne
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (pick_mem c) (hcd ▸ pick_mem d)
  let I : Selection xs := Finset.univ.image pick
  refine ⟨I, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_biUnion.mpr
      ⟨c, Finset.mem_univ c, pick_mem c⟩
  · simp [I, Finset.card_image_of_injective, pick_injective]
  · unfold I
    rw [Finset.sum_image]
    · simp only [pick_value]
      simpa using hsum'
    · intro c _ d _ hcd
      exact pick_injective hcd

/-- A labelled selection whose values all lie in `g + K` has total
displacement from `card I • g` in `K`. -/
theorem selection_sum_sub_card_nsmul_mem
    {xs : List A} (K : AddSubgroup A) (g : A) (I : Selection xs)
    (hI : ∀ i ∈ I,
      occurrenceValue xs i ∈ addCosetFinset K g) :
    (∑ i ∈ I, occurrenceValue xs i) - I.card • g ∈ K := by
  classical
  have hsum :
      (∑ i ∈ I, (occurrenceValue xs i - g)) ∈ K := by
    exact K.toAddSubmonoid.sum_mem fun i hi ↦
      (mem_addCosetFinset_iff K g (occurrenceValue xs i)).1 (hI i hi)
  simpa [Finset.sum_sub_distrib] using hsum

/-- Exact labelled completion of a genuine Claim-B witness.  The first
`d*(K)` labels come from its saturated replacement partition, the remaining
`n-d*(K)` labels come from `unusedInAddCoset`, and their union sums to the
specific centre `n • W.g`. -/
theorem OrdinaryGMOClaimBOutput.exists_selection_sum_eq_nsmul_g
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hrn : pGroupDStar W.K ≤ n) :
    ∃ I : Selection xs,
      I.card = n ∧
        (∑ i ∈ I, occurrenceValue xs i) = n • W.g := by
  classical
  let r : ℕ := pGroupDStar W.K
  let U : Selection xs := W.partition.unusedInAddCoset W.K W.g
  have htailLe : n - r ≤ U.card := by
    dsimp [r, U]
    exact le_trans (Nat.le_add_right (n - pGroupDStar W.K)
      (xs.length - seed.card)) W.remaining_in_coset
  obtain ⟨tail, htailSub, htailCard⟩ :=
    Finset.exists_subset_card_eq (s := U) htailLe
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i
  have htailCoset : ∀ i ∈ tail,
      occurrenceValue xs i ∈ addCosetFinset W.K W.g := by
    intro i hi
    exact (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1
      (htailSub hi) |>.2
  have htailDiff : tailSum - (n - r) • W.g ∈ W.K := by
    have h := selection_sum_sub_card_nsmul_mem W.K W.g tail htailCoset
    simpa [tailSum, htailCard] using h
  let y : A := n • W.g - tailSum
  have hyCoset : y ∈ addCosetFinset W.K (r • W.g) := by
    apply (mem_addCosetFinset_iff W.K (r • W.g) y).2
    have hneg := W.K.neg_mem htailDiff
    have hrsplit : r + (n - r) = n := Nat.add_sub_of_le hrn
    have hnsmul : n • W.g = r • W.g + (n - r) • W.g := by
      calc
        n • W.g = (r + (n - r)) • W.g :=
          congrArg (fun t : ℕ ↦ t • W.g) hrsplit.symm
        _ = r • W.g + (n - r) • W.g := by rw [add_nsmul]
    convert hneg using 1
    dsimp [y]
    rw [hnsmul]
    abel
  have hySumset : y ∈ W.partition.sumset := by
    rw [W.saturation]
    exact hyCoset
  obtain ⟨first, hfirstSub, hfirstCard, hfirstSum⟩ :=
    W.partition.exists_selection_subset_support_of_mem_sumset hySumset
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
    dsimp [y, tailSum]
    abel

/-- Claim B closes the ordinary prescribed-length target whenever its honest
subgroup constant is at most the prescribed length.  The target centre used
by the construction is exactly `W.g`. -/
theorem ordinaryGMOTargetOutput_nonempty_of_claimB
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hrn : pGroupDStar W.K ≤ n) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  obtain ⟨I, hIcard, hIsum⟩ := W.exists_selection_sum_eq_nsmul_g hrn
  exact ⟨{
    selected := I
    card_selected := hIcard
    sum_mem_target := ⟨W.g, hIsum⟩
  }⟩

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.exists_selection_subset_support_of_mem_sumset
#print axioms GaoLean.selection_sum_sub_card_nsmul_mem
#print axioms GaoLean.OrdinaryGMOClaimBOutput.exists_selection_sum_eq_nsmul_g
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_claimB
