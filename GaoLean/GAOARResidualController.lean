import GaoLean.GAOARRankThreeCompletion
import GaoLean.PGControllerClosure

/-!
# Structural-GMO residual controller

This module translates the published ordinary and signed structural GMO
alternatives themselves into the two simultaneous residual-controller steps.
It removes the older source-specific `RotationChannelGMOProvider` and
`ReflectionChannelGMOProvider` assumptions from the final proof boundary.
-/

namespace GaoLean

open ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The internal quotient by `H ≤ K`, and the quotient by the same subgroup
after mapping it into the ambient group and restricting back to `K`, have the
same cardinality. -/
theorem natCard_internalQuotient_eq_mappedSubtype
    (K : AddSubgroup A) [Fintype K] (H : AddSubgroup K) :
    Nat.card (K ⧸ H) =
      Nat.card (K ⧸ (H.map K.subtype).addSubgroupOf K) := by
  have hmapcard : Nat.card (H.map K.subtype) = Nat.card H :=
    natCard_map_subtype K H
  have hsubcard :
      Nat.card ((H.map K.subtype).addSubgroupOf K) =
        Nat.card (H.map K.subtype) :=
    Nat.card_congr
      (AddSubgroup.addSubgroupOfEquivOfLe
        (AddSubgroup.map_subtype_le H))
  have hleft := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hright := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((H.map K.subtype).addSubgroupOf K)
  rw [hsubcard, hmapcard] at hright
  exact Nat.mul_right_cancel Nat.card_pos (hleft.symm.trans hright)

/-- Coordinate sum of an inside-`K` coordinate selection after transporting
its occurrence labels back to the source. -/
theorem coordinateSum_rotationInSourceSelection
    (s : List (ConcreteGDihedral.Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) :
    coordinateSum s (rotationInSourceSelection s K I) =
      ((∑ i ∈ I,
        occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) := by
  classical
  unfold coordinateSum rotationInSourceSelection
  rw [Finset.sum_image]
  · have hcoe :
        ((∑ i ∈ I,
          occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) =
        ∑ i ∈ I,
          ((occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) := by
      simp
    rw [hcoe]
    apply Finset.sum_congr rfl
    intro i hi
    exact (occurrenceValue_rotationInCoordinateSequence s K i).symm
  · intro i hi j hj hij
    exact rotationInSourceOccurrence_injective s K hij

namespace ConcreteGDihedral

set_option maxHeartbeats 1000000 in
/-- Direct ordinary structural-GMO closure of one positive rotation channel.
The full branch keeps the chosen `M-d` source occurrences and adjoins the
literal extracted outside block; the non-full branch maps its strict subgroup
back into the ambient group and invokes only a strictly smaller `ZR` state. -/
theorem hasAllRotationProductOneSubsequence_of_rotationPreGMO_structural
    (s : List (Group A)) (Q D a b Dk : ℕ)
    (K : AddSubgroup A) [Fintype K] (hKtop : K < ⊤)
    (h : RotationChannelPreGMOData s Q D a b K)
    (hordinary : OrdinaryDavenportAtMost K Dk)
    (hGMO : OrdinaryGMOStructuralProvider K)
    (htarget : Nat.card K ≤ h.M - h.d)
    (hthreshold : (h.M - h.d) + (Dk - 1) ≤ h.M)
    (hsmallZR : ∀ (H : AddSubgroup A), H < K →
      ∀ Y : List (Group A), ConcreteZRStatement Y Q D a b H)
    (hlen : s.length = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hguard : QuotientNoReflection s K)
    (hQ : Q = Nat.card A) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  classical
  let xs := rotationInCoordinateSequence s K
  have hxslen : xs.length = h.M := by
    calc
      xs.length = (rotationOccurrencesIn s K).card := by
        simp [xs, rotationInCoordinateSequence]
      _ = h.C.card := by rw [h.C_eq]
      _ = h.M := h.Ccard
  have hthreshold' : (h.M - h.d) + Dk - 1 ≤ xs.length := by
    rw [hxslen]
    omega
  rcases hGMO xs (h.M - h.d) Dk htarget hordinary hthreshold' with
      hfull | hnonfull
  · have hBmem : coordinateSum s h.Bprime ∈ K :=
      h.coordinateSum_Bprime_mem
    obtain ⟨I, hIcard, hIsum⟩ :=
      hfull (-⟨coordinateSum s h.Bprime, hBmem⟩ : K)
    let E : Selection s := rotationInSourceSelection s K I
    have hEsub : E ⊆ h.C := by
      rw [h.C_eq]
      exact rotationInSourceSelection_subset s K I
    have hEcard : E.card = h.M - h.d := by
      rw [card_rotationInSourceSelection s K I]
      exact hIcard
    have hEsum : coordinateSum s E = -coordinateSum s h.Bprime := by
      rw [coordinateSum_rotationInSourceSelection]
      simpa using congrArg Subtype.val hIsum
    have hdis : Disjoint E h.Bprime :=
      h.CBprime_disjoint.mono_left hEsub
    apply hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
      s (E ∪ h.Bprime) (2 * Q)
    · rw [Finset.card_union_of_disjoint hdis, hEcard, h.exactSize]
    · intro i hi
      rcases Finset.mem_union.mp hi with hiE | hiB
      · exact h.allC i (hEsub hiE)
      · exact h.allBprime i hiB
    · rw [coordinateSum_union s E h.Bprime hdis, hEsum]
      exact neg_add_cancel _
  · obtain ⟨hc⟩ := hnonfull
    let H : AddSubgroup A := hc.K.map K.subtype
    let α : A := hc.alpha
    let X : Selection s := rotationInSourceSelection s K hc.selected
    have hHltK : H < K := by
      simpa [H] using map_subtype_lt_of_lt_top K hc.K hc.strict
    have hquot : Nat.card (K ⧸ H.addSubgroupOf K) =
        Nat.card (K ⧸ hc.K) := by
      exact (natCard_internalQuotient_eq_mappedSubtype K hc.K).symm
    have hXsub : X ⊆ h.C := by
      rw [h.C_eq]
      exact rotationInSourceSelection_subset s K hc.selected
    have hXcard : X.card = hc.selected.card :=
      card_rotationInSourceSelection s K hc.selected
    have hXcoset : ∀ i ∈ X,
        coordinate (occurrenceValue s i) - α ∈ H := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjcoset := hc.sourceCoset j hj
      change coordinate
          (occurrenceValue s (rotationInSourceOccurrence s K j)) -
            (hc.alpha : A) ∈ hc.K.map K.subtype
      refine ⟨occurrenceValue xs j - hc.alpha, hjcoset, ?_⟩
      have hval := occurrenceValue_rotationInCoordinateSequence s K j
      change ((occurrenceValue xs j : K) : A) = _ at hval
      rw [← hval]
      rfl
    have hM : b - Nat.card (A ⧸ K) + 2 ≤ h.M := by
      rw [← h.Ccard, h.C_eq]
      exact hcapacity
    have hXlower : h.M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ X.card := by
      rw [hquot, hXcard, ← hxslen]
      exact hc.card_lower
    have hα : α ∈ K := hc.alpha.property
    have hX : ∀ i ∈ X,
        IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) - α ∈ H := by
      intro i hi
      exact ⟨h.allC i (hXsub hi), hXcoset i hi⟩
    exact hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR
      α s Q D a b h.M H K hHltK hKtop X hX hM hXlower
        (hsmallZR H hHltK (translatedSequence α s)) hlen href hrot hα
          hguard hQ

set_option maxHeartbeats 1000000 in
/-- Direct signed structural-GMO closure of one positive reflection channel.
The full spectrum cancels the lifted quotient defect literally.  The
non-full spectrum is transported back to a strict ambient subgroup and calls
only the smaller fixed-source controller. -/
theorem hasProductOneSubsequence_of_reflectionPreGMO_structural
    (s : List (Group A)) (Q D a b Dk : ℕ)
    (K : AddSubgroup A) [Fintype K] (hKtop : K < ⊤)
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (hpm : PlusMinusDavenportAtMost K Dk)
    (hGMO : PlusMinusGMOStructuralProvider K)
    (htarget : Nat.card K ≤ h.m)
    (hthreshold : h.m + (Dk - 1) ≤ h.M)
    (hsmallRC : ∀ H : AddSubgroup A, H < K → RCStatement s Q b H)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hAodd : Odd (Nat.card A)) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  classical
  let xs := rotationInCoordinateSequence s K
  have hxslen : xs.length = h.M := by
    calc
      xs.length = (rotationOccurrencesIn s K).card := by
        simp [xs, rotationInCoordinateSequence]
      _ = h.C.card := by rw [h.C_eq]
      _ = h.M := h.Ccard
  have hthreshold' : h.m + Dk - 1 ≤ xs.length := by
    rw [hxslen]
    omega
  rcases hGMO xs h.m Dk htarget hpm hthreshold' with hfull | hnonfull
  · obtain ⟨hout⟩ := hfull (-⟨h.z, h.z_mem⟩ : K)
    exact (ReflectionChannelDirectFullOutput.ofSpectrum h hout).hasProductOneSubsequence
  · obtain ⟨hc⟩ := hnonfull
    let H : AddSubgroup A := hc.K.map K.subtype
    let X : Selection s := rotationInSourceSelection s K hc.selected
    have hHltK : H < K := by
      simpa [H] using map_subtype_lt_of_lt_top K hc.K hc.strict
    have hquot : Nat.card (K ⧸ H.addSubgroupOf K) =
        Nat.card (K ⧸ hc.K) := by
      exact (natCard_internalQuotient_eq_mappedSubtype K hc.K).symm
    have hKdvd : Nat.card K ∣ Nat.card A := by
      refine ⟨Nat.card (A ⧸ K), ?_⟩
      simpa [Nat.mul_comm] using
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
    have hoddK : Odd (Nat.card K) := Odd.of_dvd_nat hAodd hKdvd
    have hXcard : X.card = hc.selected.card :=
      card_rotationInSourceSelection s K hc.selected
    have hXsub : X ⊆ rotationOccurrencesIn s H := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjmem : occurrenceValue xs j ∈ hc.K :=
        hc.value_mem_subgroup
          (odd_natCard_quotient_of_odd_natCard hc.K hoddK) j hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Finset.mem_filter.mp
          (rotationInSourceOccurrence_mem s K j)).2.1
      · change coordinate
          (occurrenceValue s (rotationInSourceOccurrence s K j)) ∈
            hc.K.map K.subtype
        refine ⟨occurrenceValue xs j, hjmem, ?_⟩
        exact occurrenceValue_rotationInCoordinateSequence s K j
    have hM : b - Nat.card (A ⧸ K) + 2 ≤ h.M := by
      rw [← h.Ccard, h.C_eq]
      exact hcapacity
    have hXlower : h.M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ X.card := by
      rw [hquot, hXcard, ← hxslen]
      exact hc.card_lower
    have hXcapacity : b - Nat.card (A ⧸ H) + 2 ≤ X.card :=
      residual_capacity_composition_of_strict H K hHltK hKtop
        b h.M X.card hM hXlower
    have hHcapacity : b - Nat.card (A ⧸ H) + 2 ≤
        (rotationOccurrencesIn s H).card :=
      hXcapacity.trans (Finset.card_le_card hXsub)
    exact hsmallRC H hHltK hHcapacity

end ConcreteGDihedral

set_option maxHeartbeats 1000000 in
/-- Rank-free simultaneous residual controller produced directly from the
published structural GMO interfaces, quotient small-Davenport bounds, and
the Davenport concatenation inequality. -/
theorem concretePGO3ControllerSkeleton_of_structuralGMO
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (href : (reflectionOccurrences S).card = a)
    (hrot : (rotationOccurrences S).card = b)
    (hQ : Q = Nat.card A) (hAodd : Odd (Nat.card A))
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (htotal : a + b = 2 * Q + D)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (ConcreteGDihedral.Group A) D)
    (Dker Dquot : AddSubgroup A → ℕ)
    (hsmallQuotient : ∀ K : AddSubgroup A,
      QuotientSmallDavenportProductOneFreeAtMost K (Dquot K))
    (hDquotLe : ∀ K : AddSubgroup A, Dquot K ≤ D)
    (hconvolution : ∀ K : AddSubgroup A, ⊥ < K → K < ⊤ →
      Dker K + Dquot K ≤ D + 1)
    (hordinary : ∀ (K : AddSubgroup A) [Fintype K], ⊥ < K → K < ⊤ →
      OrdinaryDavenportAtMost K (Dker K))
    (hplusMinus : ∀ (K : AddSubgroup A) [Fintype K], ⊥ < K → K < ⊤ →
      PlusMinusDavenportAtMost K (Dker K))
    (hordinaryGMO : ∀ (K : AddSubgroup A) [Fintype K],
      OrdinaryGMOStructuralProvider K)
    (hplusMinusGMO : ∀ (K : AddSubgroup A) [Fintype K],
      PlusMinusGMOStructuralProvider K) :
    PGO3ControllerSkeleton ConcreteGDihedral.QuotientNoReflection
      S Q D a b := by
  classical
  have hDb : D ≤ b - Q + 2 :=
    middle_controller_base_bound hDQ haD htotal
  have hRCpos : ConcreteRCPositiveStep S Q D a b := by
    intro K hKpos hKtop hsmallRC hsmallZR
    intro hcapacity
    by_cases hguard : ConcreteGDihedral.QuotientNoReflection S K
    · obtain ⟨hpre⟩ :=
        ConcreteGDihedral.exists_rotationChannelPreGMOData
          S Q D a b (Dquot K) K htotal href hrot
            (hsmallQuotient K) (hDquotLe K) hQ hcapacity hguard
      have hfree : a + hpre.B0.card ≤ Dquot K :=
        hpre.free_remainder_bound href (hsmallQuotient K) hguard
      have hdefect : Dker K - 1 ≤ hpre.d :=
        hpre.defect_ge_of_davenport_bound (Dker K) (Dquot K)
          (hconvolution K hKpos hKtop) hfree
      have hthreshold : (hpre.M - hpre.d) + (Dker K - 1) ≤ hpre.M :=
        hpre.reservoir_threshold hdefect
      have htarget : Nat.card K ≤ hpre.M - hpre.d :=
        hpre.target_ge_card_subgroup htotal hQ hKtop hcapacity
      obtain ⟨I, hIcard, hIprod, _hallI⟩ :=
        ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_rotationPreGMO_structural
        S Q D a b (Dker K) K hKtop hpre
          (hordinary K hKpos hKtop) (hordinaryGMO K) htarget hthreshold
            hsmallZR hlen href hrot hcapacity hguard hQ
      exact ⟨I, hIcard, hIprod⟩
    · obtain ⟨hpre⟩ :=
        ConcreteGDihedral.exists_reflectionChannelPreGMOData
          S Q D a b (Dquot K) K href hrot htotal hDQ haD hQ hcapacity
            (hsmallQuotient K) (hDquotLe K) hguard
      have hRsmall : hpre.R.card ≤ Dquot K :=
        hsmallQuotient K S hpre.R hpre.R_free
      have htau : Dker K - 1 ≤ hpre.tau :=
        hpre.tau_ge_of_davenport_bound
          (hconvolution K hKpos hKtop) hRsmall
      have hthreshold : hpre.m + (Dker K - 1) ≤ hpre.M :=
        hpre.signed_reservoir_threshold htau
      have htarget : Nat.card K ≤ hpre.m :=
        hpre.target_ge_card_subgroup hQ hDQ hKpos hKtop hcapacity
          haD htotal
      exact ConcreteGDihedral.hasProductOneSubsequence_of_reflectionPreGMO_structural
        S Q D a b (Dker K) K hKtop hpre
          (hplusMinus K hKpos hKtop) (hplusMinusGMO K) htarget
            hthreshold hsmallRC hcapacity hAodd
  have hZRpos : ConcreteZRPositiveStep S Q D a b := by
    intro K X hKpos hKtop _hsmallRC hsmallZR
    intro hlenX hrefX hrotX hcapacity hguard
    obtain ⟨hpre⟩ :=
      ConcreteGDihedral.exists_rotationChannelPreGMOData
        X Q D a b (Dquot K) K htotal hrefX hrotX
          (hsmallQuotient K) (hDquotLe K) hQ hcapacity hguard
    have hfree : a + hpre.B0.card ≤ Dquot K :=
      hpre.free_remainder_bound hrefX (hsmallQuotient K) hguard
    have hdefect : Dker K - 1 ≤ hpre.d :=
      hpre.defect_ge_of_davenport_bound (Dker K) (Dquot K)
        (hconvolution K hKpos hKtop) hfree
    have hthreshold : (hpre.M - hpre.d) + (Dker K - 1) ≤ hpre.M :=
      hpre.reservoir_threshold hdefect
    have htarget : Nat.card K ≤ hpre.M - hpre.d :=
      hpre.target_ge_card_subgroup htotal hQ hKtop hcapacity
    exact ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_rotationPreGMO_structural
      X Q D a b (Dker K) K hKtop hpre
        (hordinary K hKpos hKtop) (hordinaryGMO K) htarget hthreshold
          hsmallZR hlenX hrefX hrotX hcapacity hguard hQ
  exact concretePGO3ControllerSkeleton_of_positiveSteps
    S Q D a b hlen hQ hDb hsmall hRCpos hZRpos

end GaoLean

#print axioms GaoLean.natCard_internalQuotient_eq_mappedSubtype
#print axioms GaoLean.coordinateSum_rotationInSourceSelection
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_rotationPreGMO_structural
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequence_of_reflectionPreGMO_structural
#print axioms GaoLean.concretePGO3ControllerSkeleton_of_structuralGMO
