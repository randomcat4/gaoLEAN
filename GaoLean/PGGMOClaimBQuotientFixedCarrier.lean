import GaoLean.PGGMOClaimBQuotientFullLift

/-!
# Fixed-carrier lift of a full quotient spectrum

The ordinary quotient-full lift produces its exact-cardinality witness one
target at a time.  This module retains the occurrence ledger shared by all
those witnesses.  Its carrier consists of the saturated Claim-B support, the
whole genuine source copy of `R`, and a fixed part of the remaining zero
quotient fiber.  In particular, the carrier has the original seed
cardinality; it is not asserted to be the support of a setpartition.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientFixedCarrierFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- A full exact spectrum whose witnesses all lie in one occurrence-labelled
carrier of a prescribed cardinality.  This deliberately records no cell
decomposition of the carrier. -/
structure OrdinaryFixedCarrierSpectrumFull
    (xs : List A) (carrierCard n : ℕ) where
  carrier : Selection xs
  card_carrier : carrier.card = carrierCard
  spectrumFull :
    ∀ y : A, ∃ I : Selection xs,
      I ⊆ carrier ∧ I.card = n ∧
        (∑ i ∈ I, occurrenceValue xs i) = y

/-- Forgetting the common carrier gives the ordinary exact full spectrum. -/
theorem OrdinaryFixedCarrierSpectrumFull.toOrdinarySpectrumFull
    {xs : List A} {carrierCard n : ℕ}
    (h : OrdinaryFixedCarrierSpectrumFull xs carrierCard n) :
    OrdinarySpectrumFull xs n := by
  intro y
  obtain ⟨I, _hIcarrier, hIcard, hIsum⟩ := h.spectrumFull y
  exact ⟨I, hIcard, hIsum⟩

/-- A full padded quotient spectrum lifts to a parent full spectrum on one
fixed carrier of cardinality `seed.card`.

The fixed carrier is the disjoint union of the old Claim-B support, the
literal source copy of all of `R`, and a fixed selection from the remaining
zero-quotient tail pool.  A smaller fixed tail is chosen inside the last
piece before the target value is introduced. -/
theorem OrdinaryGMOClaimBOutput.exists_fixedCarrier_spectrumFull_of_paddedQuotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (hfull : OrdinarySpectrumFull (W.paddedQuotientRValues hzero) dQ)
    (hlen : pGroupDStar W.K + dQ ≤ n) :
    Nonempty (OrdinaryFixedCarrierSpectrumFull xs seed.card n) := by
  classical
  let dK : ℕ := pGroupDStar W.K
  let tailLength : ℕ := n - dK - dQ
  let tailPool : Selection xs := W.quotientFullTailPool hzero

  have hseedLe : seed.card ≤ xs.length := by
    simpa using Finset.card_le_univ seed
  have hsupportLe : W.supportCard ≤ xs.length := by
    rw [← W.partition.card_support_eq]
    simpa using Finset.card_le_univ W.partition.support
  have hdecomp := W.card_nonzero_add_card_zeroFiber
  rw [W.length_quotientDisplacementSequence_eq] at hdecomp
  have hzeroLower := W.zeroQuotientFiber_lower
  have hdQLeAfterK : dQ ≤ n - dK := by
    dsimp only [dK]
    omega
  have hcarrierBudget :
      W.supportCard + W.quotientRExceptionCount + (n - dK) ≤
        seed.card := by
    dsimp only [dK]
    omega
  have hcarrierBase :
      W.supportCard + W.quotientRExceptionCount + dQ ≤ seed.card := by
    omega

  let carrierTailLength : ℕ :=
    seed.card -
      (W.supportCard + W.quotientRExceptionCount + dQ)
  have hcarrierTailLe : carrierTailLength ≤ tailPool.card := by
    dsimp only [carrierTailLength, tailPool]
    rw [W.card_quotientFullTailPool hzero]
    omega
  obtain ⟨carrierTail, hcarrierTailSub, hcarrierTailCard⟩ :=
    Finset.exists_subset_card_eq (s := tailPool) hcarrierTailLe
  have htailLeCarrier : tailLength ≤ carrierTail.card := by
    rw [hcarrierTailCard]
    dsimp only [tailLength, carrierTailLength]
    omega
  obtain ⟨tail, htailSub, htailCard⟩ :=
    Finset.exists_subset_card_eq (s := carrierTail) htailLeCarrier

  have hcarrierTailUnused : carrierTail ⊆
      W.partition.unusedInAddCoset W.K W.g :=
    hcarrierTailSub.trans
      (W.quotientFullTailPool_subset_unusedInAddCoset hzero)
  have hsupportDisjointR :
      Disjoint W.partition.support (W.quotientRSource hzero) :=
    (W.quotientRSource_disjoint_partition_support hzero).symm
  have hsupportDisjointCarrierTail :
      Disjoint W.partition.support carrierTail := by
    rw [Finset.disjoint_left]
    intro i hiSupport hiTail
    have hiUnused :=
      (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1
        (hcarrierTailUnused hiTail)
    exact hiUnused.1 hiSupport
  have hRDisjointCarrierTail :
      Disjoint (W.quotientRSource hzero) carrierTail :=
    ((W.quotientFullTailPool_disjoint_quotientRSource hzero).mono_left
      hcarrierTailSub).symm
  have hsupportDisjointRest :
      Disjoint W.partition.support
        (W.quotientRSource hzero ∪ carrierTail) := by
    rw [Finset.disjoint_union_right]
    exact ⟨hsupportDisjointR, hsupportDisjointCarrierTail⟩

  let carrier : Selection xs :=
    W.partition.support ∪ (W.quotientRSource hzero ∪ carrierTail)
  have hcarrierCard : carrier.card = seed.card := by
    dsimp only [carrier]
    rw [Finset.card_union_of_disjoint hsupportDisjointRest,
      Finset.card_union_of_disjoint hRDisjointCarrierTail,
      W.partition.card_support_eq, W.card_quotientRSource,
      hcarrierTailCard]
    dsimp only [carrierTailLength]
    omega

  have htailUnused : tail ⊆
      W.partition.unusedInAddCoset W.K W.g :=
    htailSub.trans hcarrierTailUnused
  have htailNotR : Disjoint tail (W.quotientRSource hzero) :=
    (hRDisjointCarrierTail.mono_right htailSub).symm
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i

  refine ⟨{
    carrier := carrier
    card_carrier := hcarrierCard
    spectrumFull := ?_
  }⟩
  intro y
  let quotientTarget : A ⧸ W.K :=
    QuotientAddGroup.mk' W.K
      (y - tailSum - (dK + dQ) • W.g)
  obtain ⟨J, hJR, hJcard, hJsum⟩ :=
    W.exists_quotientR_selection_of_padded_spectrumFull
      hzero hdQpos hfull quotientTarget
  let sourceJ : Selection xs := W.pullbackQuotientSelection J
  have hsourceJSubR : sourceJ ⊆ W.quotientRSource hzero :=
    W.pullbackQuotientSelection_subset_quotientRSource hzero J hJR
  have hsourceJCard : sourceJ.card = dQ := by
    dsimp only [sourceJ]
    rw [W.card_pullbackQuotientSelection, hJcard]
  have hsourceJDisjointTail : Disjoint sourceJ tail :=
    (htailNotR.mono_right hsourceJSubR).symm
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
  let witness : Selection xs := first ∪ (sourceJ ∪ tail)
  have hwitnessSub : witness ⊆ carrier := by
    intro i hi
    change i ∈ first ∪ (sourceJ ∪ tail) at hi
    change i ∈ W.partition.support ∪
      (W.quotientRSource hzero ∪ carrierTail)
    rcases Finset.mem_union.mp hi with hiFirst | hiRest
    · exact Finset.mem_union.mpr (Or.inl (hfirstSub hiFirst))
    · rcases Finset.mem_union.mp hiRest with hiJ | hiTail
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inl (hsourceJSubR hiJ))))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inr (htailSub hiTail))))
  refine ⟨witness, hwitnessSub, ?_, ?_⟩
  · dsimp only [witness]
    rw [Finset.card_union_of_disjoint hfirstDisjointRest,
      Finset.card_union_of_disjoint hsourceJDisjointTail,
      hfirstCard, hsourceJCard, htailCard]
    dsimp only [dK, tailLength]
    omega
  · dsimp only [witness]
    rw [Finset.sum_union hfirstDisjointRest,
      Finset.sum_union hsourceJDisjointTail, hfirstSum]
    dsimp [firstTarget, sourceJSum, tailSum]
    abel

/-- Complement duality for a common fixed occurrence carrier.  Unlike the
setpartition bridge, this consumes only the explicitly retained carrier and
does not claim that the carrier admits a simultaneous cell decomposition. -/
theorem OrdinaryFixedCarrierSpectrumFull.ordinarySpectrumFull_complement
    {xs : List A} {carrierCard r target : ℕ}
    (h : OrdinaryFixedCarrierSpectrumFull xs carrierCard r)
    (hcard : carrierCard = target + r) :
    OrdinarySpectrumFull xs target := by
  classical
  intro y
  let total : A := ∑ i ∈ h.carrier, occurrenceValue xs i
  obtain ⟨D, hDsub, hDcard, hDsum⟩ := h.spectrumFull (total - y)
  let I : Selection xs := h.carrier \ D
  refine ⟨I, ?_, ?_⟩
  · dsimp only [I]
    rw [Finset.card_sdiff_of_subset hDsub, h.card_carrier,
      hDcard, hcard]
    omega
  · have hsplit :=
      h.carrier.sum_inter_add_sum_sdiff D (occurrenceValue xs)
    rw [Finset.inter_eq_right.mpr hDsub, hDsum] at hsplit
    dsimp only [I]
    dsimp only [total] at hsplit
    have hcancel :=
      congrArg (fun z : A ↦ z - (total - y)) hsplit
    dsimp only [total] at hcancel
    calc
      _ = (∑ i ∈ h.carrier, occurrenceValue xs i) -
          ((∑ i ∈ h.carrier, occurrenceValue xs i) - y) := by
        simpa only [add_sub_cancel_left] using hcancel
      _ = y := by abel

end GaoLean

#print axioms GaoLean.OrdinaryFixedCarrierSpectrumFull.toOrdinarySpectrumFull
#print axioms GaoLean.OrdinaryGMOClaimBOutput.exists_fixedCarrier_spectrumFull_of_paddedQuotientR
#print axioms GaoLean.OrdinaryFixedCarrierSpectrumFull.ordinarySpectrumFull_complement
