import GaoLean.PGGMOOrdinaryPairGreedy
import GaoLean.PGCapacity

/-!
# Proper-stabilizer induction for ordinary pair certificates

This module contains only the recursion-ready bridges for the proper
stabilizer branch of the ordinary specialization of GMO Lemma 3.5.  It does
not postulate certificate existence.  The final constructor consumes the
certificate returned by strong induction on the retained subtype and maps it
back to the ambient group.

The top-stabilizer leaf is supplied by the separate greedy module.  Combining
that leaf with the honest proper-stabilizer lift below gives the unconditional
well-founded existence theorem at the end of this file.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {Q : Type u} [AddCommGroup Q] [Fintype Q]
variable {ι : Type v} [Fintype ι]
noncomputable local instance pairInductionDecidableEq {α : Type*} :
    DecidableEq α :=
  Classical.decEq α
noncomputable local instance pairInductionPropDecidable (p : Prop) :
    Decidable p :=
  Classical.propDecidable p
noncomputable local instance pairInductionSubgroupFintype
    (H : AddSubgroup Q) : Fintype H :=
  Fintype.ofFinite H

/-! ## The exact full-DGM stabilizer ledger -/

/-- At full weight, the stabilizer-capped incidence of the pair layers is
exactly one contribution per label plus one more for every label outside the
stabilizer. -/
theorem pairIndexStabilizerCappedIncidence
    (v : ι → Q) :
    stabilizerDgmCappedMultiplicitySum
        (pairIndexFullSumset v) (pairIndexSetpartition v)
        (pairIndexSetpartition v).length =
      Nat.card ι +
        (pairIndicesOutsideSubgroup v (pairIndexStabilizer v)).card := by
  classical
  rw [stabilizerDgmCappedMultiplicitySum_length]
  calc
    ((pairIndexSetpartition v).map fun B ↦
        (stabilizerQuotientLayer (pairIndexFullSumset v) B).card).sum =
        ((pairIndexSetpartition v).map fun B ↦
          (quotientLayer (pairIndexStabilizer v) B).card).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro B hB
      unfold pairIndexStabilizer
      rw [quotientLayer_eq_stabilizerQuotientLayer]
    _ = Nat.card ι +
        (pairIndicesOutsideSubgroup v (pairIndexStabilizer v)).card :=
      sum_card_quotientLayer_pairIndexSetpartition v
        (pairIndexStabilizer v)

/-- The full DGM endpoint gives the exact lower bound used in the proper
stabilizer branch. -/
theorem pairIndexDgm_stabilizer_lower
    (v : ι → Q) :
    ((pairIndicesOutsideSubgroup v (pairIndexStabilizer v)).card + 1) *
        Nat.card (pairIndexStabilizer v) ≤
      (pairIndexFullSumset v).card := by
  classical
  have hdgm := pairIndexSetpartition_dgmBound v
  unfold DGMSetpartitionBound at hdgm
  rw [← length_pairIndexSetpartition v] at hdgm
  change
    (stabilizerDgmCappedMultiplicitySum
          (pairIndexFullSumset v) (pairIndexSetpartition v)
          (pairIndexSetpartition v).length -
        (pairIndexSetpartition v).length + 1) *
        (pairIndexFullSumset v).addStab.card ≤
      (pairIndexFullSumset v).card at hdgm
  rw [pairIndexStabilizerCappedIncidence v,
    length_pairIndexSetpartition] at hdgm
  have hnonempty := pairIndexFullSumset_nonempty v
  rw [card_addStab_eq_natCard_stabilizer _ hnonempty] at hdgm
  simpa [pairIndexStabilizer, Nat.add_sub_cancel_left] using hdgm

/-- Under the source length and nonzero-label hypotheses, the full-spectrum
stabilizer cannot be bottom.  In the bottom case DGM forces the finite
spectrum to be all of `Q`, whose stabilizer is top. -/
theorem pairIndexStabilizer_ne_bot
    [Nontrivial Q] (v : ι → Q)
    (hv : ∀ i, v i ≠ 0)
    (hlen : Nat.card Q - 1 ≤ Nat.card ι) :
    pairIndexStabilizer v ≠ ⊥ := by
  classical
  intro hbot
  have houtside :
      (pairIndicesOutsideSubgroup v (pairIndexStabilizer v)).card =
        Nat.card ι := by
    rw [hbot]
    simp [pairIndicesOutsideSubgroup, pairIndicesInSubgroup, hv,
      Nat.card_eq_fintype_card]
  have hdgm := pairIndexDgm_stabilizer_lower v
  rw [houtside, hbot] at hdgm
  have hsource : Nat.card Q ≤ Nat.card ι + 1 := by omega
  have hlarge : Nat.card Q ≤ (pairIndexFullSumset v).card := by
    exact hsource.trans (by simpa using hdgm)
  have hfull : pairIndexFullSumset v = Finset.univ := by
    apply Finset.eq_univ_of_card
    apply Nat.le_antisymm
    · simpa [Nat.card_eq_fintype_card] using
        Finset.card_le_card (Finset.subset_univ (pairIndexFullSumset v))
    · simpa [Nat.card_eq_fintype_card] using hlarge
  have htop : pairIndexStabilizer v = ⊤ := by
    simp [pairIndexStabilizer, hfull]
  exact (show (⊥ : AddSubgroup Q) ≠ ⊤ from bot_ne_top) (hbot.symm.trans htop)

/-- A proper full-spectrum stabilizer leaves at most `|Q/H|-2` literal
labels outside it. -/
theorem card_pairIndicesOutsideStabilizer_le_quotient_sub_two
    (v : ι → Q) (hproper : pairIndexStabilizer v < ⊤) :
    (pairIndicesOutsideSubgroup v (pairIndexStabilizer v)).card ≤
      Nat.card (Q ⧸ pairIndexStabilizer v) - 2 := by
  classical
  let H := pairIndexStabilizer v
  let T := pairIndexFullSumset v
  have hTne : T ≠ (Finset.univ : Finset Q) := by
    intro hfull
    have : H = ⊤ := by simp [H, pairIndexStabilizer, T, hfull]
    exact hproper.ne this
  have hTle : T.card ≤ Nat.card Q := by
    simpa [Nat.card_eq_fintype_card] using
      Finset.card_le_card (Finset.subset_univ T)
  have hTlt : T.card < Nat.card Q := by
    have hcardne : T.card ≠ Nat.card Q := by
      intro hcard
      apply hTne
      apply Finset.eq_univ_of_card
      simpa [Nat.card_eq_fintype_card] using hcard
    omega
  have hdgm := pairIndexDgm_stabilizer_lower v
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hmul :
      ((pairIndicesOutsideSubgroup v H).card + 1) * Nat.card H <
        Nat.card (Q ⧸ H) * Nat.card H := by
    apply lt_of_le_of_lt
    · simpa [H, T] using hdgm
    · exact hTlt.trans_eq hfactor
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have houtlt :
      (pairIndicesOutsideSubgroup v H).card + 1 < Nat.card (Q ⧸ H) := by
    exact (Nat.mul_lt_mul_right hHpos).mp hmul
  simpa [H] using (show
    (pairIndicesOutsideSubgroup v H).card ≤ Nat.card (Q ⧸ H) - 2 by omega)

/-! ## Mapping a recursive retained-subtype certificate -/

/-- The subgroup returned recursively inside `H`, viewed in `Q`. -/
noncomputable def mappedPairCertificateSubgroup
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    AddSubgroup Q :=
  C.J.map H.subtype

/-- The recursive labelled core, transported to the original index type. -/
noncomputable def liftedPairCertificateCore
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    Finset ι :=
  C.core.image Subtype.val

/-- The labels discarded recursively inside `H`, transported to the
original index type. -/
noncomputable def liftedPairCertificateInnerOmitted
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    Finset ι :=
  ((Finset.univ : Finset (PairRetainedIndex v H)).filter fun j ↦
      pairRetainedValue v H j ∉ C.J).image Subtype.val

theorem mappedPairCertificateSubgroup_le
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    mappedPairCertificateSubgroup v H C ≤ H := by
  exact AddSubgroup.map_subtype_le C.J

theorem mappedPairCertificateSubgroup_ne_bot
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    mappedPairCertificateSubgroup v H C ≠ ⊥ := by
  intro hbot
  apply C.J_ne_bot
  apply (AddSubgroup.map_injective H.subtype_injective)
  simpa [mappedPairCertificateSubgroup] using hbot

/-- Exact subset-sum transport along the retained-subtype embedding. -/
theorem pairIndexSubsetSums_image_retainedSubtype
    (v : ι → Q) (H : AddSubgroup Q)
    (s : Finset (PairRetainedIndex v H)) :
    pairIndexSubsetSums v (s.image Subtype.val) =
      (pairIndexSubsetSums (pairRetainedValue v H) s).image H.subtype := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hsum⟩ :=
      (mem_pairIndexSubsetSums_iff v (s.image Subtype.val) x).1 hx
    let u : Finset (PairRetainedIndex v H) :=
      s.filter fun j ↦ j.1 ∈ t
    have hu : u ⊆ s := Finset.filter_subset _ _
    have huImage : u.image Subtype.val = t := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_filter.mp hj).2
      · intro hi
        obtain ⟨j, hj, hjval⟩ := Finset.mem_image.mp (ht hi)
        subst i
        exact Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨hj, hi⟩, rfl⟩
    let y : H := ∑ j ∈ u, pairRetainedValue v H j
    have hy : y ∈ pairIndexSubsetSums (pairRetainedValue v H) s :=
      (mem_pairIndexSubsetSums_iff _ s y).2 ⟨u, hu, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨y, hy, ?_⟩
    change (y : Q) = x
    calc
      (y : Q) = ∑ j ∈ u, v j.1 := by
        simp [y, pairRetainedValue]
      _ = ∑ i ∈ t, v i := by
        rw [← huImage, Finset.sum_image]
        · rfl
        · exact Subtype.val_injective.injOn
      _ = x := hsum
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, hsum⟩ :=
      (mem_pairIndexSubsetSums_iff (pairRetainedValue v H) s y).1 hy
    refine (mem_pairIndexSubsetSums_iff v (s.image Subtype.val) x).2
      ⟨u.image Subtype.val, Finset.image_mono Subtype.val hu, ?_⟩
    calc
      (∑ i ∈ u.image Subtype.val, v i) =
          ∑ j ∈ u, v j.1 := by
        rw [Finset.sum_image]
        · rfl
        · exact Subtype.val_injective.injOn
      _ = (y : Q) := by
        rw [← hsum]
        simp [pairRetainedValue]
      _ = x := hyx

theorem image_subgroupFinset_subtype
    (H : AddSubgroup Q) (J : AddSubgroup H) :
    (subgroupFinset J).image H.subtype =
      subgroupFinset (J.map H.subtype) := by
  classical
  ext x
  simp [mem_subgroupFinset, AddSubgroup.mem_map]

theorem liftedPairCertificateCore_subset_retained
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    liftedPairCertificateCore v H C ⊆
      pairIndicesInSubgroup v (mappedPairCertificateSubgroup v H C) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  apply (mem_pairIndicesInSubgroup_iff _ _ _).2
  change v j.1 ∈ C.J.map H.subtype
  exact ⟨pairRetainedValue v H j, C.core_value_mem j hj, rfl⟩

theorem card_liftedPairCertificateCore
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    (liftedPairCertificateCore v H C).card = C.core.card := by
  exact Finset.card_image_of_injective C.core Subtype.val_injective

theorem natCard_mappedPairCertificateSubgroup
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    Nat.card (mappedPairCertificateSubgroup v H C) = Nat.card C.J := by
  exact (Nat.card_congr
    (C.J.equivMapOfInjective H.subtype H.subtype_injective).toEquiv).symm

theorem liftedPairCertificateCore_sumset
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    pairIndexSubsetSums v (liftedPairCertificateCore v H C) =
      subgroupFinset (mappedPairCertificateSubgroup v H C) := by
  rw [liftedPairCertificateCore,
    pairIndexSubsetSums_image_retainedSubtype, C.core_sumset,
    image_subgroupFinset_subtype]
  rfl

/-! ## Exact omitted-label decomposition -/

theorem card_liftedPairCertificateInnerOmitted
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    (liftedPairCertificateInnerOmitted v H C).card =
      ((Finset.univ : Finset (PairRetainedIndex v H)) \ C.retained).card := by
  rw [liftedPairCertificateInnerOmitted,
    Finset.card_image_of_injective _ Subtype.val_injective]
  apply congrArg Finset.card
  ext j
  rw [C.mem_omitted_iff]
  simp

/-- Membership in the recursively omitted labels, stated without exposing the
`Finset.sdiff` instance chosen inside the transport definition. -/
theorem mem_liftedPairCertificateInnerOmitted_iff
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H))
    (i : ι) :
    i ∈ liftedPairCertificateInnerOmitted v H C ↔
      ∃ j : PairRetainedIndex v H,
        pairRetainedValue v H j ∉ C.J ∧ j.1 = i := by
  unfold liftedPairCertificateInnerOmitted
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact ⟨j, (Finset.mem_filter.mp hj).2, hji⟩
  · rintro ⟨j, hjNot, hji⟩
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, hji⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjNot⟩

theorem pairOutside_mappedCertificate_decomposition
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    pairIndicesOutsideSubgroup v (mappedPairCertificateSubgroup v H C) =
      pairIndicesOutsideSubgroup v H ∪
        liftedPairCertificateInnerOmitted v H C := by
  ext i
  constructor
  · intro hi
    have hiL := (mem_pairIndicesOutsideSubgroup_iff _ _ _).1 hi
    letI : Decidable (v i ∈ H) := Classical.propDecidable _
    by_cases hiH : v i ∈ H
    · apply Finset.mem_union_right
      let j : PairRetainedIndex v H := ⟨i, hiH⟩
      apply (mem_liftedPairCertificateInnerOmitted_iff v H C i).2
      refine ⟨j, ?_, rfl⟩
      intro hjJ
      exact hiL ⟨pairRetainedValue v H j, hjJ, rfl⟩
    · exact Finset.mem_union_left _
        ((mem_pairIndicesOutsideSubgroup_iff _ _ _).2 hiH)
  · intro hi
    apply (mem_pairIndicesOutsideSubgroup_iff _ _ _).2
    rcases Finset.mem_union.mp hi with hiOutside | hiInner
    · intro hiL
      exact (mem_pairIndicesOutsideSubgroup_iff _ _ _).1 hiOutside
        ((mappedPairCertificateSubgroup_le v H C) hiL)
    · obtain ⟨j, hjNot, rfl⟩ :=
        (mem_liftedPairCertificateInnerOmitted_iff v H C i).1 hiInner
      intro hjL
      obtain ⟨y, hyJ, hyval⟩ := hjL
      have hy : y = pairRetainedValue v H j := by
        apply Subtype.ext
        exact hyval
      exact hjNot (by simpa [hy] using hyJ)

theorem pairOutside_disjoint_liftedInnerOmitted
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    Disjoint (pairIndicesOutsideSubgroup v H)
      (liftedPairCertificateInnerOmitted v H C) := by
  rw [Finset.disjoint_left]
  intro i hiOutside hiInner
  have hiNotH := (mem_pairIndicesOutsideSubgroup_iff _ _ _).1 hiOutside
  obtain ⟨j, _hj, hjval⟩ :=
    (mem_liftedPairCertificateInnerOmitted_iff v H C i).1 hiInner
  subst i
  exact hiNotH j.2

theorem card_pairOutside_mappedCertificate
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    (pairIndicesOutsideSubgroup v
        (mappedPairCertificateSubgroup v H C)).card =
      (pairIndicesOutsideSubgroup v H).card +
        ((Finset.univ : Finset (PairRetainedIndex v H)) \
          C.retained).card := by
  rw [pairOutside_mappedCertificate_decomposition,
    Finset.card_union_of_disjoint
      (pairOutside_disjoint_liftedInnerOmitted v H C),
    card_liftedPairCertificateInnerOmitted]

/-! ## Quotient-card composition and the proper lift constructor -/

theorem natCard_internalQuotient_mappedPairCertificate
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    Nat.card (H ⧸ C.J) =
      Nat.card
        (H ⧸ (mappedPairCertificateSubgroup v H C).addSubgroupOf H) := by
  have hmapcard :
      Nat.card (mappedPairCertificateSubgroup v H C) = Nat.card C.J :=
    natCard_mappedPairCertificateSubgroup v H C
  have hsubcard :
      Nat.card
          ((mappedPairCertificateSubgroup v H C).addSubgroupOf H) =
        Nat.card (mappedPairCertificateSubgroup v H C) :=
    Nat.card_congr
      (AddSubgroup.addSubgroupOfEquivOfLe
        (mappedPairCertificateSubgroup_le v H C))
  have hleft := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C.J
  have hright := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((mappedPairCertificateSubgroup v H C).addSubgroupOf H)
  rw [hsubcard, hmapcard] at hright
  exact Nat.mul_right_cancel Nat.card_pos (hleft.symm.trans hright)

theorem natCard_quotient_mappedPairCertificate
    (v : ι → Q) (H : AddSubgroup Q)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    Nat.card (Q ⧸ mappedPairCertificateSubgroup v H C) =
      Nat.card (Q ⧸ H) * Nat.card (H ⧸ C.J) := by
  rw [natCard_quotient_eq_mul_quotient_subgroupOf
    (mappedPairCertificateSubgroup v H C) H
    (mappedPairCertificateSubgroup_le v H C)]
  rw [← natCard_internalQuotient_mappedPairCertificate v H C]

omit [AddCommGroup Q] [Fintype Q] [Fintype ι] in
theorem sub_two_add_sub_two_le_mul_sub_two
    (a b : ℕ) (ha : 2 ≤ a) (hb : 1 ≤ b) :
    (a - 2) + (b - 2) ≤ a * b - 2 := by
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp
  · have hb2 : 2 ≤ b := by omega
    have hmul : a + b ≤ a * b := by nlinarith
    omega

/-- Honest proper-stabilizer recursion lift.  Its only certificate input is
the result of recursion on the strictly smaller retained ambient subgroup;
no global existence interface is accepted. -/
noncomputable def ordinaryPairSubgroupCertificate_of_retained
    (v : ι → Q) (H : AddSubgroup Q) (hproper : H < ⊤)
    (houtside :
      (pairIndicesOutsideSubgroup v H).card ≤ Nat.card (Q ⧸ H) - 2)
    (C : OrdinaryPairSubgroupCertificate (pairRetainedValue v H)) :
    OrdinaryPairSubgroupCertificate v := by
  classical
  let L := mappedPairCertificateSubgroup v H C
  let core := liftedPairCertificateCore v H C
  refine {
    J := L
    J_ne_bot := mappedPairCertificateSubgroup_ne_bot v H C
    retained := pairIndicesInSubgroup v L
    retained_eq := rfl
    omitted_bound := ?_
    core := core
    core_subset_retained := liftedPairCertificateCore_subset_retained v H C
    core_card := ?_
    core_sumset := liftedPairCertificateCore_sumset v H C
  }
  · change (pairIndicesOutsideSubgroup v L).card ≤ Nat.card (Q ⧸ L) - 2
    rw [show L = mappedPairCertificateSubgroup v H C from rfl,
      card_pairOutside_mappedCertificate,
      natCard_quotient_mappedPairCertificate]
    apply le_trans (Nat.add_le_add houtside C.omitted_bound)
    exact sub_two_add_sub_two_le_mul_sub_two _ _
      (two_le_natCard_quotient_of_lt_top H hproper) Nat.card_pos
  · change core.card = Nat.card L - 1
    rw [show core = liftedPairCertificateCore v H C from rfl,
      card_liftedPairCertificateCore, C.core_card,
      show Nat.card L = Nat.card C.J from
        natCard_mappedPairCertificateSubgroup v H C]

/-- Specialization of the previous constructor to the canonical stabilizer.
This is the exact branch consumed by the later strong-induction driver. -/
noncomputable def ordinaryPairSubgroupCertificate_of_properStabilizer
    (v : ι → Q) (hproper : pairIndexStabilizer v < ⊤)
    (C : OrdinaryPairSubgroupCertificate
      (pairRetainedValue v (pairIndexStabilizer v))) :
    OrdinaryPairSubgroupCertificate v :=
  ordinaryPairSubgroupCertificate_of_retained v (pairIndexStabilizer v)
    hproper
    (card_pairIndicesOutsideStabilizer_le_quotient_sub_two v hproper) C

/-! ## The two recursive branches and the well-founded driver -/

/-- The top-stabilizer greedy carrier is already a complete certificate,
with ambient subgroup `Q` and no omitted labels. -/
theorem ordinaryPairSubgroupCertificate_of_stabilizer_eq_top
    [Nontrivial Q] (v : ι → Q)
    (hlen : Nat.card Q - 1 ≤ Nat.card ι)
    (htop : pairIndexStabilizer v = ⊤) :
    Nonempty (OrdinaryPairSubgroupCertificate v) := by
  classical
  obtain ⟨core, hcoreCard, hcoreSum⟩ :=
    exists_pairIndexSubsetSums_core_of_stabilizer_eq_top v hlen htop
  refine ⟨{
    J := ⊤
    J_ne_bot := top_ne_bot
    retained := pairIndicesInSubgroup v ⊤
    retained_eq := rfl
    omitted_bound := ?_
    core := core
    core_subset_retained := ?_
    core_card := by simpa using hcoreCard
    core_sumset := ?_
  }⟩
  · simp [pairIndicesInSubgroup]
  · intro i hi
    simpa [pairIndicesInSubgroup] using hi
  · simpa [subgroupFinset] using hcoreSum

/-- The proper stabilizer retains enough nonzero labels to meet the same
`|H|-1` recursion threshold inside `H`.  This is the source-deficit
calculation which must not be omitted from the induction. -/
theorem card_sub_one_le_natCard_pairRetainedIndex_of_properStabilizer
    [Nontrivial Q] (v : ι → Q)
    (hv : ∀ i, v i ≠ 0)
    (hlen : Nat.card Q - 1 ≤ Nat.card ι)
    (hproper : pairIndexStabilizer v < ⊤) :
    Nat.card (pairIndexStabilizer v) - 1 ≤
      Nat.card (PairRetainedIndex v (pairIndexStabilizer v)) := by
  classical
  let H := pairIndexStabilizer v
  change Nat.card H - 1 ≤ Nat.card (PairRetainedIndex v H)
  have hHne : H ≠ ⊥ := by
    simpa [H] using pairIndexStabilizer_ne_bot v hv hlen
  letI : Nontrivial H := (AddSubgroup.nontrivial_iff_ne_bot H).2 hHne
  have hq2 : 2 ≤ Nat.card (Q ⧸ H) :=
    two_le_natCard_quotient_of_lt_top H (by simpa [H] using hproper)
  have hH2 : 2 ≤ Nat.card H := by
    exact (Finite.one_lt_card_iff_nontrivial).2 (inferInstance : Nontrivial H)
  have hout :
      (pairIndicesOutsideSubgroup v H).card ≤ Nat.card (Q ⧸ H) - 2 := by
    simpa [H] using
      card_pairIndicesOutsideStabilizer_le_quotient_sub_two v hproper
  have hpartition := card_pairIndicesInSubgroup_add_outside v H
  have hfactor := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  rw [natCard_pairRetainedIndex]
  by_contra hnot
  have hinSmall : (pairIndicesInSubgroup v H).card + 2 ≤ Nat.card H := by
    omega
  have houtSmall :
      (pairIndicesOutsideSubgroup v H).card + 2 ≤ Nat.card (Q ⧸ H) := by
    omega
  have htotal :
      Nat.card Q ≤
        (pairIndicesInSubgroup v H).card +
          (pairIndicesOutsideSubgroup v H).card + 1 := by
    omega
  rw [hfactor] at htotal
  nlinarith

/-- Universe-polymorphic outer induction predicate for honest pair
certificates. -/
def OrdinaryPairCertificateAtGroupCard (m : ℕ) : Prop :=
  ∀ (B : Type u) [AddCommGroup B] [Fintype B] [Nontrivial B],
    Nat.card B = m →
    ∀ (κ : Type v) [Fintype κ] (w : κ → B),
      (∀ i, w i ≠ 0) →
      Nat.card B - 1 ≤ Nat.card κ →
      Nonempty (OrdinaryPairSubgroupCertificate w)

/-- Ordinary Lemma 3.5 for honest labelled nonzero pairs.  The proof is
strong induction on the ambient group cardinality.  A top stabilizer is the
proved greedy leaf; a proper stabilizer recurses on the literal retained
index subtype in the nontrivial subgroup and then uses the exact omitted
ledger above. -/
theorem ordinaryPairSubgroupCertificate_exists
    [Nontrivial Q] (v : ι → Q)
    (hv : ∀ i, v i ≠ 0)
    (hlen : Nat.card Q - 1 ≤ Nat.card ι) :
    Nonempty (OrdinaryPairSubgroupCertificate v) := by
  classical
  have outer : ∀ m : ℕ, OrdinaryPairCertificateAtGroupCard.{u, v} m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro B instGroup instFintype instNontrivial hm
        intro κ instIndexFintype w hw hlength
        let H := pairIndexStabilizer w
        by_cases htop : H = ⊤
        · exact ordinaryPairSubgroupCertificate_of_stabilizer_eq_top
            w hlength (by simpa [H] using htop)
        · have hproper : H < ⊤ := lt_top_iff_ne_top.mpr htop
          have hHne : H ≠ ⊥ := by
            simpa [H] using pairIndexStabilizer_ne_bot w hw hlength
          letI : Nontrivial H :=
            (AddSubgroup.nontrivial_iff_ne_bot H).2 hHne
          have hsmall : Nat.card H < m := by
            rw [← hm]
            simpa using natCard_lt_of_addSubgroup_lt hproper
          have hretainedLength :
              Nat.card H - 1 ≤ Nat.card (PairRetainedIndex w H) := by
            simpa [H] using
              card_sub_one_le_natCard_pairRetainedIndex_of_properStabilizer
                w hw hlength (by simpa [H] using hproper)
          have hrecursive :=
            ih (Nat.card H) hsmall H rfl
              (PairRetainedIndex w H) (pairRetainedValue w H)
              (pairRetainedValue_ne_zero w H hw) hretainedLength
          obtain ⟨C⟩ := hrecursive
          exact ⟨ordinaryPairSubgroupCertificate_of_properStabilizer w
            (by simpa [H] using hproper) C⟩
  exact outer (Nat.card Q) Q rfl ι v hv hlen

#print axioms pairIndexStabilizerCappedIncidence
#print axioms pairIndexDgm_stabilizer_lower
#print axioms pairIndexStabilizer_ne_bot
#print axioms card_pairIndicesOutsideStabilizer_le_quotient_sub_two
#print axioms mappedPairCertificateSubgroup_le
#print axioms mappedPairCertificateSubgroup_ne_bot
#print axioms pairIndexSubsetSums_image_retainedSubtype
#print axioms image_subgroupFinset_subtype
#print axioms liftedPairCertificateCore_subset_retained
#print axioms card_liftedPairCertificateCore
#print axioms natCard_mappedPairCertificateSubgroup
#print axioms liftedPairCertificateCore_sumset
#print axioms card_liftedPairCertificateInnerOmitted
#print axioms mem_liftedPairCertificateInnerOmitted_iff
#print axioms pairOutside_mappedCertificate_decomposition
#print axioms pairOutside_disjoint_liftedInnerOmitted
#print axioms card_pairOutside_mappedCertificate
#print axioms natCard_internalQuotient_mappedPairCertificate
#print axioms natCard_quotient_mappedPairCertificate
#print axioms sub_two_add_sub_two_le_mul_sub_two
#print axioms ordinaryPairSubgroupCertificate_of_retained
#print axioms ordinaryPairSubgroupCertificate_of_properStabilizer
#print axioms ordinaryPairSubgroupCertificate_of_stabilizer_eq_top
#print axioms card_sub_one_le_natCard_pairRetainedIndex_of_properStabilizer
#print axioms ordinaryPairSubgroupCertificate_exists

end GaoLean
