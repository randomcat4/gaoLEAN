import GaoLean.PGGMOClaimBQuotientFullNormalize
import GaoLean.PGGMOClaimBTarget

/-!
# Lifting a full quotient spectrum through an honest Claim-B ledger

The padded quotient theorem is used only after normalization to a genuine
selection in `R`.  That quotient selection is pulled back through the literal
source-position embedding.  A fixed tail is chosen from the unused coset
positions outside `R`, and the saturated Claim-B support supplies the final
`d*(K)` labels.

The sole length hypothesis is the canonical convolution bound
`d*(K) + dQ ≤ n`.  No artificial padded occurrence is ever mapped to the
original source.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientFullLiftFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- The genuine coset tail positions not already reserved by `R`. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientFullTailPool
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) : Selection xs :=
  W.partition.unusedInAddCoset W.K W.g \ W.quotientRSource hzero

/-- The literal source tail pool is exactly the pullback of the genuine
quotient positions omitted from `R`. -/
theorem OrdinaryGMOClaimBOutput.quotientFullTailPool_eq_map_compl_quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    W.quotientFullTailPool hzero =
      ((Finset.univ : Selection W.quotientDisplacementSequence) \
          W.quotientR hzero).map W.quotientSourceEmbedding := by
  classical
  ext i
  constructor
  · intro hi
    have hiParts := Finset.mem_sdiff.mp hi
    have hiUnused :=
      (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1 hiParts.1
    have hiRemaining : i ∈ W.remainingOccurrences :=
      (W.mem_remainingOccurrences_iff i).2 hiUnused.1
    have hiRange : i ∈
        (Finset.univ : Selection W.quotientDisplacementSequence).map
          W.quotientSourceEmbedding := by
      rw [W.map_univ_quotientSourceEmbedding]
      exact hiRemaining
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hiRange
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, hqi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ q, ?_⟩
    intro hqR
    apply hiParts.2
    change i ∈ (W.quotientR hzero).map W.quotientSourceEmbedding
    exact Finset.mem_map.mpr ⟨q, hqR, hqi⟩
  · intro hi
    obtain ⟨q, hqCompl, rfl⟩ := Finset.mem_map.mp hi
    have hqParts := Finset.mem_sdiff.mp hqCompl
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (W.partition.mem_unusedInAddCoset_iff W.K W.g _).2
      constructor
      · exact (W.mem_remainingOccurrences_iff _).1
          (W.quotientSourceOccurrence_mem_remaining q)
      · apply (W.occurrenceValue_quotient_eq_zero_iff q).1
        exact W.occurrenceValue_eq_zero_of_mem_compl_quotientR
          hzero q hqCompl
    · intro hqSource
      change W.quotientSourceOccurrence q ∈
        (W.quotientR hzero).map W.quotientSourceEmbedding at hqSource
      obtain ⟨r, hrR, hrq⟩ := Finset.mem_map.mp hqSource
      have hrq' : r = q := W.quotientSourceEmbedding.injective hrq
      exact hqParts.2 (hrq' ▸ hrR)

@[simp]
theorem OrdinaryGMOClaimBOutput.card_quotientFullTailPool
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.quotientFullTailPool hzero).card =
      (W.quotientFiber 0).card - dQ := by
  classical
  rw [W.quotientFullTailPool_eq_map_compl_quotientR hzero]
  simp [W.card_compl_quotientR hzero]

theorem OrdinaryGMOClaimBOutput.quotientFullTailPool_subset_unusedInAddCoset
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    W.quotientFullTailPool hzero ⊆
      W.partition.unusedInAddCoset W.K W.g := by
  intro i hi
  exact (Finset.mem_sdiff.mp hi).1

theorem OrdinaryGMOClaimBOutput.quotientFullTailPool_disjoint_quotientRSource
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Disjoint (W.quotientFullTailPool hzero) (W.quotientRSource hzero) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiPool hiR
  exact (Finset.mem_sdiff.mp hiPool).2 hiR

/-- A quotient selection contained in `R` pulls back inside the literal
source copy of `R`. -/
theorem OrdinaryGMOClaimBOutput.pullbackQuotientSelection_subset_quotientRSource
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (J : Selection W.quotientDisplacementSequence)
    (hJ : J ⊆ W.quotientR hzero) :
    W.pullbackQuotientSelection J ⊆ W.quotientRSource hzero := by
  intro i hi
  obtain ⟨q, hqJ, rfl⟩ := Finset.mem_map.mp hi
  apply Finset.mem_map.mpr
  exact ⟨q, hJ hqJ, rfl⟩

/-- The quotient sum of a genuine quotient selection is the quotient of
the sum of its pulled-back values, centered once per selected label. -/
theorem OrdinaryGMOClaimBOutput.mk_sum_pullbackQuotientSelection_sub_nsmul
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (J : Selection W.quotientDisplacementSequence) :
    QuotientAddGroup.mk' W.K
        ((∑ i ∈ W.pullbackQuotientSelection J, occurrenceValue xs i) -
          (W.pullbackQuotientSelection J).card • W.g) =
      ∑ q ∈ J, occurrenceValue W.quotientDisplacementSequence q := by
  classical
  have hcenter :
      (∑ i ∈ W.pullbackQuotientSelection J, occurrenceValue xs i) -
          (W.pullbackQuotientSelection J).card • W.g =
        ∑ i ∈ W.pullbackQuotientSelection J,
          (occurrenceValue xs i - W.g) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hcenter, map_sum]
  simp only [OrdinaryGMOClaimBOutput.pullbackQuotientSelection,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro q hq
  rw [W.occurrenceValue_quotientDisplacementSequence q]
  rfl

/-- A full exact spectrum on the padded quotient `R`-list lifts to the full
ordinary exact spectrum on the original source.  The three source pieces
are, respectively, the saturated old support, the normalized genuine `R`
selection, and a fixed tail outside `R`. -/
theorem OrdinaryGMOClaimBOutput.ordinarySpectrumFull_of_paddedQuotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (hfull : OrdinarySpectrumFull (W.paddedQuotientRValues hzero) dQ)
    (hlen : pGroupDStar W.K + dQ ≤ n) :
    OrdinarySpectrumFull xs n := by
  classical
  intro y
  let dK : ℕ := pGroupDStar W.K
  let tailLength : ℕ := n - dK - dQ
  let tailPool : Selection xs := W.quotientFullTailPool hzero
  have hdQLeAfterK : dQ ≤ n - dK := by
    dsimp [dK]
    omega
  have htailLe : tailLength ≤ tailPool.card := by
    have hzeroLower := W.zeroQuotientFiber_lower
    have hbase : n - dK ≤ (W.quotientFiber 0).card := by
      dsimp [dK]
      omega
    dsimp [tailLength, tailPool]
    rw [W.card_quotientFullTailPool hzero]
    exact Nat.sub_le_sub_right hbase dQ
  obtain ⟨tail, htailSub, htailCard⟩ :=
    Finset.exists_subset_card_eq (s := tailPool) htailLe
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i
  have htailUnused : tail ⊆
      W.partition.unusedInAddCoset W.K W.g := by
    exact htailSub.trans
      (W.quotientFullTailPool_subset_unusedInAddCoset hzero)
  have htailNotR : Disjoint tail (W.quotientRSource hzero) :=
    (W.quotientFullTailPool_disjoint_quotientRSource hzero).mono_left
      htailSub
  let quotientTarget : A ⧸ W.K :=
    QuotientAddGroup.mk' W.K
      (y - tailSum - (dK + dQ) • W.g)
  obtain ⟨J, hJR, hJcard, hJsum⟩ :=
    W.exists_quotientR_selection_of_padded_spectrumFull
      hzero hdQpos hfull quotientTarget
  let sourceJ : Selection xs := W.pullbackQuotientSelection J
  have hsourceJSubR : sourceJ ⊆ W.quotientRSource hzero := by
    exact W.pullbackQuotientSelection_subset_quotientRSource
      hzero J hJR
  have hsourceJCard : sourceJ.card = dQ := by
    dsimp [sourceJ]
    rw [W.card_pullbackQuotientSelection, hJcard]
  have hsourceJDisjointTail : Disjoint sourceJ tail := by
    exact (htailNotR.mono_right hsourceJSubR).symm
  let sourceJSum : A := ∑ i ∈ sourceJ, occurrenceValue xs i
  have hsourceJQuotient :
      QuotientAddGroup.mk' W.K (sourceJSum - dQ • W.g) =
        quotientTarget := by
    have htransport := W.mk_sum_pullbackQuotientSelection_sub_nsmul J
    dsimp [sourceJSum, sourceJ] at htransport ⊢
    rw [W.card_pullbackQuotientSelection, hJcard] at htransport
    exact htransport.trans hJsum
  let firstTarget : A := y - tailSum - sourceJSum
  have hfirstTargetCoset :
      firstTarget ∈ addCosetFinset W.K (dK • W.g) := by
    apply (mem_addCosetFinset_iff W.K (dK • W.g) firstTarget).2
    rw [← QuotientAddGroup.eq_zero_iff]
    change QuotientAddGroup.mk' W.K
      (firstTarget - dK • W.g) = 0
    calc
      QuotientAddGroup.mk' W.K (firstTarget - dK • W.g) =
          quotientTarget -
            QuotientAddGroup.mk' W.K (sourceJSum - dQ • W.g) := by
        dsimp [firstTarget, quotientTarget]
        simp only [add_nsmul]
        abel
      _ = 0 := by rw [hsourceJQuotient]; simp
  have hfirstTargetSumset : firstTarget ∈ W.partition.sumset := by
    rw [W.saturation]
    simpa [dK] using hfirstTargetCoset
  obtain ⟨first, hfirstSub, hfirstCard, hfirstSum⟩ :=
    W.partition.exists_selection_subset_support_of_mem_sumset
      hfirstTargetSumset
  have hfirstDisjointSourceJ : Disjoint first sourceJ := by
    rw [Finset.disjoint_left]
    intro i hiFirst hiJ
    exact (Finset.disjoint_left.mp
      (W.quotientRSource_disjoint_partition_support hzero))
        (hsourceJSubR hiJ) (hfirstSub hiFirst)
  have hfirstDisjointTail : Disjoint first tail := by
    rw [Finset.disjoint_left]
    intro i hiFirst hiTail
    have hiUnused :=
      (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1
        (htailUnused hiTail)
    exact hiUnused.1 (hfirstSub hiFirst)
  have hfirstDisjointRest : Disjoint first (sourceJ ∪ tail) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hfirstDisjointSourceJ, hfirstDisjointTail⟩
  refine ⟨first ∪ (sourceJ ∪ tail), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hfirstDisjointRest,
      Finset.card_union_of_disjoint hsourceJDisjointTail,
      hfirstCard, hsourceJCard, htailCard]
    dsimp [dK, tailLength]
    omega
  · rw [Finset.sum_union hfirstDisjointRest,
      Finset.sum_union hsourceJDisjointTail,
      hfirstSum]
    dsimp [firstTarget, sourceJSum, tailSum]
    abel

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.quotientFullTailPool_eq_map_compl_quotientR
#print axioms GaoLean.OrdinaryGMOClaimBOutput.mk_sum_pullbackQuotientSelection_sub_nsmul
#print axioms GaoLean.OrdinaryGMOClaimBOutput.ordinarySpectrumFull_of_paddedQuotientR
