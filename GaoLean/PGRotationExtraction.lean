import GaoLean.PGRotationChannel

/-!
# Occurrence-labelled quotient extraction for the rotation channel

This module formalizes the source's extraction
`B = B0 ⊔ Bprime` from A-R6 (5.12).  Instead of fixing a procedural greedy
order, it chooses a maximum-cardinality quotient-zero-sum subselection
`Bprime`.  Its complement `B0` is quotient-zero-sum-free.  These are exactly
the labelled postconditions used by the proof, and no occurrence is collapsed.

The final prescribed-length spectrum alternative remains an explicit GMO
provider.  Thus this module moves the formal boundary up to the external GMO
output; it does not assert that output.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Sum of the selected rotation coordinates in the additive quotient `A/K`.
The definition remains meaningful for arbitrary selected occurrences. -/
def quotientCoordinateSum
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s) : A ⧸ K :=
  ∑ i ∈ I, QuotientAddGroup.mk' K (coordinate (occurrenceValue s i))

theorem quotientCoordinateSum_eq_mk_coordinateSum
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s) :
    quotientCoordinateSum s K I =
      QuotientAddGroup.mk' K (coordinateSum s I) := by
  classical
  simp [quotientCoordinateSum, coordinateSum, map_sum]

theorem quotientCoordinateSum_union
    (s : List (Group A)) (K : AddSubgroup A) (I J : Selection s)
    (hIJ : Disjoint I J) :
    quotientCoordinateSum s K (I ∪ J) =
      quotientCoordinateSum s K I + quotientCoordinateSum s K J := by
  classical
  exact Finset.sum_union hIJ

/-- No nonempty occurrence subselection has coordinate sum zero modulo `K`. -/
def IsQuotientZeroSumFreeSelection
    (s : List (Group A)) (K : AddSubgroup A) (R : Selection s) : Prop :=
  ∀ I : Selection s, I ⊆ R → I.Nonempty → quotientCoordinateSum s K I ≠ 0

/-- The exact labelled partition produced by the quotient extraction. -/
structure RotationQuotientExtraction
    (s : List (Group A)) (K : AddSubgroup A) (B : Selection s) where
  B0 : Selection s
  Bprime : Selection s
  B0_subset : B0 ⊆ B
  Bprime_subset : Bprime ⊆ B
  disjoint : Disjoint B0 Bprime
  partition : B0 ∪ Bprime = B
  B0_free : IsQuotientZeroSumFreeSelection s K B0
  Bprime_zero : quotientCoordinateSum s K Bprime = 0

/-- Maximum-cardinality zero-sum extraction supplies the same postconditions
as the source's greedy removal of disjoint zero-sum blocks. -/
theorem exists_rotationQuotientExtraction
    (s : List (Group A)) (K : AddSubgroup A) (B : Selection s) :
    Nonempty (RotationQuotientExtraction s K B) := by
  classical
  let candidates : Finset (Selection s) :=
    B.powerset.filter fun I => quotientCoordinateSum s K I = 0
  have hempty : quotientCoordinateSum s K (∅ : Selection s) = 0 := by
    simp [quotientCoordinateSum]
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, hempty]
  obtain ⟨Bprime, hBprimeCand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hBprimeSub : Bprime ⊆ B :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hBprimeCand).1
  have hBprimeZero : quotientCoordinateSum s K Bprime = 0 :=
    (Finset.mem_filter.mp hBprimeCand).2
  let B0 : Selection s := B \ Bprime
  have hB0Sub : B0 ⊆ B := Finset.sdiff_subset
  have hdis : Disjoint B0 Bprime := Finset.disjoint_sdiff.symm
  have hpartition : B0 ∪ Bprime = B := by
    exact Finset.sdiff_union_of_subset hBprimeSub
  have hB0free : IsQuotientZeroSumFreeSelection s K B0 := by
    intro J hJsub hJne hJzero
    have hBJ : Disjoint Bprime J := by
      rw [Finset.disjoint_left]
      intro i hiBprime hiJ
      exact (Finset.mem_sdiff.mp (hJsub hiJ)).2 hiBprime
    have hJsubB : J ⊆ B := fun i hi =>
      (Finset.mem_sdiff.mp (hJsub hi)).1
    have hunionSub : Bprime ∪ J ⊆ B :=
      Finset.union_subset hBprimeSub hJsubB
    have hunionZero : quotientCoordinateSum s K (Bprime ∪ J) = 0 := by
      rw [quotientCoordinateSum_union s K Bprime J hBJ,
        hBprimeZero, hJzero, zero_add]
    have hunionCand : Bprime ∪ J ∈ candidates := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hunionSub, hunionZero⟩
    have hle : (Bprime ∪ J).card ≤ Bprime.card :=
      hmax (Bprime ∪ J) hunionCand
    have hcard := Finset.card_union_of_disjoint hBJ
    have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
    omega
  exact ⟨{
    B0 := B0
    Bprime := Bprime
    B0_subset := hB0Sub
    Bprime_subset := hBprimeSub
    disjoint := hdis
    partition := hpartition
    B0_free := hB0free
    Bprime_zero := hBprimeZero
  }⟩

theorem RotationQuotientExtraction.card_partition
    {s : List (Group A)} {K : AddSubgroup A} {B : Selection s}
    (h : RotationQuotientExtraction s K B) :
    h.B0.card + h.Bprime.card = B.card := by
  calc
    h.B0.card + h.Bprime.card = (h.B0 ∪ h.Bprime).card :=
      (Finset.card_union_of_disjoint h.disjoint).symm
    _ = B.card := congrArg Finset.card h.partition

theorem RotationQuotientExtraction.coordinateSum_Bprime_mem
    {s : List (Group A)} {K : AddSubgroup A} {B : Selection s}
    (h : RotationQuotientExtraction s K B) :
    coordinateSum s h.Bprime ∈ K := by
  apply (QuotientAddGroup.eq_zero_iff (coordinateSum s h.Bprime)).1
  calc
    QuotientAddGroup.mk' K (coordinateSum s h.Bprime) =
        quotientCoordinateSum s K h.Bprime :=
      (quotientCoordinateSum_eq_mk_coordinateSum s K h.Bprime).symm
    _ = 0 := h.Bprime_zero

/-- The source's outside-`K` rotation reservoir. -/
noncomputable def rotationOccurrencesOutside
    (s : List (Group A)) (K : AddSubgroup A) : Selection s :=
  rotationOccurrences s \ rotationOccurrencesIn s K

theorem mem_rotationOccurrencesOutside_iff
    (s : List (Group A)) (K : AddSubgroup A) (i : Occurrence s) :
    i ∈ rotationOccurrencesOutside s K ↔
      IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) ∉ K := by
  classical
  constructor
  · intro hi
    have hi' := Finset.mem_sdiff.mp hi
    have hrot : IsRotation (occurrenceValue s i) := by
      simpa [rotationOccurrencesOutside, rotationOccurrences] using hi'.1
    have hout : coordinate (occurrenceValue s i) ∉ K := by
      intro hmem
      apply hi'.2
      simp [rotationOccurrencesIn, hrot, hmem]
    exact ⟨hrot, hout⟩
  · rintro ⟨hrot, hout⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [rotationOccurrences, hrot]
    · intro hin
      have hin' : IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) ∈ K := by
        simpa [rotationOccurrencesIn] using hin
      exact hout hin'.2

theorem rotationOccurrencesIn_union_outside
    (s : List (Group A)) (K : AddSubgroup A) :
    rotationOccurrencesIn s K ∪ rotationOccurrencesOutside s K =
      rotationOccurrences s := by
  classical
  apply le_antisymm
  · intro i hi
    rcases Finset.mem_union.mp hi with hiK | hiOut
    · have hiK' : IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) ∈ K := by
        simpa [rotationOccurrencesIn] using hiK
      simpa [rotationOccurrences] using hiK'.1
    · exact (Finset.mem_sdiff.mp hiOut).1
  · intro i hi
    by_cases hiK : i ∈ rotationOccurrencesIn s K
    · exact Finset.mem_union_left _ hiK
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hiK⟩)

theorem card_rotationOccurrencesIn_add_outside
    (s : List (Group A)) (K : AddSubgroup A) :
    (rotationOccurrencesIn s K).card +
        (rotationOccurrencesOutside s K).card =
      (rotationOccurrences s).card := by
  calc
    (rotationOccurrencesIn s K).card +
        (rotationOccurrencesOutside s K).card =
        (rotationOccurrencesIn s K ∪
          rotationOccurrencesOutside s K).card :=
      (Finset.card_union_of_disjoint
        (Finset.disjoint_sdiff : Disjoint
          (rotationOccurrencesIn s K)
          (rotationOccurrences s \ rotationOccurrencesIn s K))).symm
    _ = (rotationOccurrences s).card :=
      congrArg Finset.card (rotationOccurrencesIn_union_outside s K)

/-- Product-one-freeness after quotient projection, still quantified over the
original occurrence labels. -/
def IsQuotientProductOneFreeSelection
    (s : List (Group A)) (K : AddSubgroup A) (R : Selection s) : Prop :=
  ∀ I : Selection s, I ⊆ R → I.Nonempty →
    ¬HasProductOneOrdering
      ((selectedMultiset s I).map (quotientMap K))

/-- External small-Davenport interface in the quotient group, phrased on
source occurrence labels. -/
def QuotientSmallDavenportProductOneFreeAtMost
    (K : AddSubgroup A) (Dq : ℕ) : Prop :=
  ∀ (s : List (Group A)) (R : Selection s),
    IsQuotientProductOneFreeSelection s K R → R.card ≤ Dq

/-- A quotient product-one ordering of rotations has zero additive quotient
coordinate sum. -/
theorem quotientCoordinateSum_eq_zero_of_allRotation_productOne
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s)
    (hall : ∀ i ∈ I, IsRotation (occurrenceValue s i))
    (hprod : HasProductOneOrdering
      ((selectedMultiset s I).map (quotientMap K))) :
    quotientCoordinateSum s K I = 0 := by
  classical
  rcases hprod with ⟨word, hword, hprod⟩
  have hallWord : ∀ g ∈ word, IsRotation g := by
    intro g hg
    have hgMapped : g ∈ (selectedMultiset s I).map (quotientMap K) := by
      rw [← hword]
      simpa using hg
    rcases Multiset.mem_map.mp hgMapped with ⟨x, hx, rfl⟩
    have hxSelected : x ∈ selectedMultiset s I := hx
    rw [selectedMultiset] at hxSelected
    rcases Multiset.mem_map.mp hxSelected with ⟨i, hi, rfl⟩
    exact (quotientMap_isRotation_iff K _).2 (hall i hi)
  have hwordSum : (word.map coordinate).sum = 0 :=
    sum_coordinate_eq_zero_of_prod_one word hallWord hprod
  have hsumEq := congrArg
    (fun M : Multiset (Group (A ⧸ K)) => (M.map coordinate).sum) hword
  have hEq : (word.map coordinate).sum = quotientCoordinateSum s K I := by
    simpa [selectedMultiset, quotientCoordinateSum,
      coordinate_quotientMap] using hsumEq
  rw [← hEq]
  exact hwordSum

/-- The quotient sequence consisting of all reflections and the zero-sum-free
outside-rotation remainder is product-one-free.  Reflection-containing blocks
contradict the channel guard; rotation-only blocks contradict zero-sum-freeness
of `B0`. -/
theorem reflection_union_B0_quotientProductOneFree
    (s : List (Group A)) (K : AddSubgroup A)
    (B0 : Selection s)
    (hB0sub : B0 ⊆ rotationOccurrencesOutside s K)
    (hB0free : IsQuotientZeroSumFreeSelection s K B0)
    (hguard : QuotientNoReflection s K) :
    IsQuotientProductOneFreeSelection s K
      (reflectionOccurrences s ∪ B0) := by
  intro I hIsub hIne hIprod
  by_cases hrefI : ∃ i ∈ I, ¬IsRotation (occurrenceValue s i)
  · apply hguard
    refine ⟨I, ?_, hrefI, hIprod⟩
    intro i hi
    rw [mem_quotientCarrierOccurrences_iff_reflection_or_rotation_outside]
    rcases Finset.mem_union.mp (hIsub hi) with hiRefl | hiB0
    · left
      simpa [reflectionOccurrences] using hiRefl
    · right
      exact (mem_rotationOccurrencesOutside_iff s K i).1
        (hB0sub hiB0) |>.2
  · have hallI : ∀ i ∈ I, IsRotation (occurrenceValue s i) := by
      intro i hi
      by_contra hnot
      exact hrefI ⟨i, hi, hnot⟩
    have hIsubB0 : I ⊆ B0 := by
      intro i hi
      rcases Finset.mem_union.mp (hIsub hi) with hiRefl | hiB0
      · have hnotrot : ¬IsRotation (occurrenceValue s i) := by
          simpa [reflectionOccurrences] using hiRefl
        exact False.elim (hnotrot (hallI i hi))
      · exact hiB0
    have hzero : quotientCoordinateSum s K I = 0 :=
      quotientCoordinateSum_eq_zero_of_allRotation_productOne
        s K I hallI hIprod
    exact hB0free I hIsubB0 hIne hzero

/-- All internal, non-GMO data for the source rotation channel. -/
structure RotationChannelPreGMOData
    (s : List (Group A)) (Q D a b : ℕ) (K : AddSubgroup A) where
  M : ℕ
  d : ℕ
  C : Selection s
  B : Selection s
  B0 : Selection s
  Bprime : Selection s
  C_eq : C = rotationOccurrencesIn s K
  B_eq : B = rotationOccurrencesOutside s K
  Ccard : C.card = M
  B0_subset : B0 ⊆ B
  Bprime_subset : Bprime ⊆ B
  B0_Bprime_disjoint : Disjoint B0 Bprime
  B_partition : B0 ∪ Bprime = B
  B0_free : IsQuotientZeroSumFreeSelection s K B0
  Bprime_quotient_zero : quotientCoordinateSum s K Bprime = 0
  d_eq : d = D - a - B0.card
  a_B0_le_D : a + B0.card ≤ D
  d_le_M : d ≤ M
  CBprime_disjoint : Disjoint C Bprime
  allC : ∀ i ∈ C, IsRotation (occurrenceValue s i)
  allBprime : ∀ i ∈ Bprime, IsRotation (occurrenceValue s i)
  BprimeOutside : ∀ i ∈ Bprime,
    coordinate (occurrenceValue s i) ∉ K
  exactSize : M - d + Bprime.card = 2 * Q

theorem RotationChannelPreGMOData.coordinateSum_Bprime_mem
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K) :
    coordinateSum s h.Bprime ∈ K := by
  apply (QuotientAddGroup.eq_zero_iff (coordinateSum s h.Bprime)).1
  calc
    QuotientAddGroup.mk' K (coordinateSum s h.Bprime) =
        quotientCoordinateSum s K h.Bprime :=
      (quotientCoordinateSum_eq_mk_coordinateSum s K h.Bprime).symm
    _ = 0 := h.Bprime_quotient_zero

/-- Recover the precise quotient small-Davenport bound
`a+|B0|≤Dq` from the stored extraction data. -/
theorem RotationChannelPreGMOData.free_remainder_bound
    {s : List (Group A)} {Q D a b Dq : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K)
    (href : (reflectionOccurrences s).card = a)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hguard : QuotientNoReflection s K) :
    a + h.B0.card ≤ Dq := by
  have hB0out : h.B0 ⊆ rotationOccurrencesOutside s K := by
    rw [← h.B_eq]
    exact h.B0_subset
  have hfreeT : IsQuotientProductOneFreeSelection s K
      (reflectionOccurrences s ∪ h.B0) :=
    reflection_union_B0_quotientProductOneFree s K h.B0
      hB0out h.B0_free hguard
  have hTle : (reflectionOccurrences s ∪ h.B0).card ≤ Dq :=
    hsmall s _ hfreeT
  have hdis : Disjoint (reflectionOccurrences s) h.B0 := by
    rw [Finset.disjoint_left]
    intro i hiRefl hiB0
    have hnotrot : ¬IsRotation (occurrenceValue s i) := by
      simpa [reflectionOccurrences] using hiRefl
    have hrot : IsRotation (occurrenceValue s i) :=
      (mem_rotationOccurrencesOutside_iff s K i).1 (hB0out hiB0) |>.1
    exact hnotrot hrot
  calc
    a + h.B0.card =
        (reflectionOccurrences s).card + h.B0.card := by rw [href]
    _ = (reflectionOccurrences s ∪ h.B0).card :=
      (Finset.card_union_of_disjoint hdis).symm
    _ ≤ Dq := hTle

/-- Source equation (5.13), isolated from the external Davenport convolution
identity.  The subtraction-free form `D+1=Dk+Dq` is equivalent to the source
formula in the positive Davenport range. -/
theorem RotationChannelPreGMOData.defect_ge_of_davenport_split
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K)
    (Dk Dq : ℕ) (hsplit : D + 1 = Dk + Dq)
    (hfreeBound : a + h.B0.card ≤ Dq) :
    Dk - 1 ≤ h.d := by
  rw [h.d_eq]
  omega

/-- Inequality form used by the manuscript's concatenation bound
`D(K)+D(A/K)-1 ≤ D(A)`. -/
theorem RotationChannelPreGMOData.defect_ge_of_davenport_bound
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K)
    (Dk Dq : ℕ) (hbound : Dk + Dq ≤ D + 1)
    (hfreeBound : a + h.B0.card ≤ Dq) :
    Dk - 1 ≤ h.d := by
  rw [h.d_eq]
  omega

/-- The first half of the source's GMO length threshold:
`M ≥ (M-d)+(Dk-1)`. -/
theorem RotationChannelPreGMOData.reservoir_threshold
    {s : List (Group A)} {Q D a b Dk : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K)
    (hdefect : Dk - 1 ≤ h.d) :
    (h.M - h.d) + (Dk - 1) ≤ h.M := by
  have hdM := h.d_le_M
  omega

/-- Source equation (5.16): the GMO target `m=M-d` is at least `|K|`.
This uses the actual controller capacity, the exact total count, and the
finite quotient-cardinality factorization. -/
theorem RotationChannelPreGMOData.target_ge_card_subgroup
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K)
    (htotal : a + b = 2 * Q + D)
    (hQ : Q = Nat.card A) (hKtop : K < ⊤)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card) :
    Nat.card K ≤ h.M - h.d := by
  have hcapM : b - Nat.card (A ⧸ K) + 2 ≤ h.M := by
    rw [← h.Ccard, h.C_eq]
    exact hcapacity
  have hdUpper : h.d ≤ D - a := by
    rw [h.d_eq]
    omega
  have haB0D := h.a_B0_le_D
  have haD : a ≤ D := by omega
  have hquotientLeA : Nat.card (A ⧸ K) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
  have hquotientLeQ : Nat.card (A ⧸ K) ≤ Q := by
    simpa [hQ] using hquotientLeA
  have hmLower :
      2 * Q - Nat.card (A ⧸ K) + 2 ≤ h.M - h.d := by
    apply Nat.le_sub_of_add_le
    calc
      (2 * Q - Nat.card (A ⧸ K) + 2) + h.d ≤
          (2 * Q - Nat.card (A ⧸ K) + 2) + (D - a) :=
        Nat.add_le_add_left hdUpper _
      _ = b - Nat.card (A ⧸ K) + 2 := by omega
      _ ≤ h.M := hcapM
  have hfactor : Q = Nat.card (A ⧸ K) * Nat.card K := by
    calc
      Q = Nat.card A := hQ
      _ = Nat.card (A ⧸ K) * Nat.card K :=
        K.card_eq_card_quotient_mul_card_addSubgroup
  have hquotientTwo : 2 ≤ Nat.card (A ⧸ K) :=
    two_le_natCard_quotient_of_lt_top K hKtop
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hquotientPos : 0 < Nat.card (A ⧸ K) := by omega
  have hKleQ : Nat.card K ≤ Q := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_left _ hquotientPos
  have hquotientLeQ' : Nat.card (A ⧸ K) ≤ Q := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ hKpos
  have hKleTarget :
      Nat.card K ≤ 2 * Q - Nat.card (A ⧸ K) + 2 := by
    omega
  exact hKleTarget.trans hmLower

def RotationChannelPreGMOData.toPrepared
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreGMOData s Q D a b K)
    (hAlt : RotationChannelAlternative s h.C h.Bprime K h.M h.d) :
    RotationChannelPreparedData s Q K where
  M := h.M
  d := h.d
  C := h.C
  Bprime := h.Bprime
  C_eq := h.C_eq
  Ccard := h.Ccard
  CBdisjoint := h.CBprime_disjoint
  allC := h.allC
  allBprime := h.allBprime
  BprimeOutside := h.BprimeOutside
  exactSize := h.exactSize
  alternative := hAlt

/-- The remaining external ordinary-GMO obligation, now quantified only over
the completely extracted source data. -/
def RotationChannelGMOProvider
    (s : List (Group A)) (Q D a b : ℕ) (K : AddSubgroup A) : Prop :=
  ∀ h : RotationChannelPreGMOData s Q D a b K,
    RotationChannelAlternative s h.C h.Bprime K h.M h.d

/-- Construct all pre-GMO rotation-channel data from labelled extraction and
the explicit quotient small-Davenport bound. -/
theorem exists_rotationChannelPreGMOData
    (s : List (Group A)) (Q D a b Dq : ℕ) (K : AddSubgroup A)
    (htotal : a + b = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hDqD : Dq ≤ D)
    (hQ : Q = Nat.card A)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hguard : QuotientNoReflection s K) :
    Nonempty (RotationChannelPreGMOData s Q D a b K) := by
  classical
  let C := rotationOccurrencesIn s K
  let B := rotationOccurrencesOutside s K
  rcases exists_rotationQuotientExtraction s K B with ⟨hex⟩
  have hfreeT : IsQuotientProductOneFreeSelection s K
      (reflectionOccurrences s ∪ hex.B0) :=
    reflection_union_B0_quotientProductOneFree s K hex.B0
      (by simpa [B] using hex.B0_subset) hex.B0_free hguard
  have hTle : (reflectionOccurrences s ∪ hex.B0).card ≤ Dq :=
    hsmall s _ hfreeT
  have hrefB0dis : Disjoint (reflectionOccurrences s) hex.B0 := by
    rw [Finset.disjoint_left]
    intro i hiRefl hiB0
    have hnotrot : ¬IsRotation (occurrenceValue s i) := by
      simpa [reflectionOccurrences] using hiRefl
    have hrotI : IsRotation (occurrenceValue s i) :=
      (mem_rotationOccurrencesOutside_iff s K i).1
        ((by simpa [B] using hex.B0_subset hiB0)) |>.1
    exact hnotrot hrotI
  have haB0Dq : a + hex.B0.card ≤ Dq := by
    rw [← href, ← Finset.card_union_of_disjoint hrefB0dis]
    exact hTle
  have haB0D : a + hex.B0.card ≤ D := haB0Dq.trans hDqD
  have hCBdis : Disjoint C B := by
    simpa [C, B, rotationOccurrencesOutside] using
      (Finset.disjoint_sdiff : Disjoint
        (rotationOccurrencesIn s K)
        (rotationOccurrences s \ rotationOccurrencesIn s K))
  have hCBprime : Disjoint C hex.Bprime :=
    hCBdis.mono_right (by simpa [B] using hex.Bprime_subset)
  have hCplusB : C.card + B.card = b := by
    simpa [C, B, hrot] using
      card_rotationOccurrencesIn_add_outside s K
  have hBparts : hex.B0.card + hex.Bprime.card = B.card := by
    simpa [B] using hex.card_partition
  let M := C.card
  let d := D - a - hex.B0.card
  have hquotientLeA : Nat.card (A ⧸ K) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
  have hquotientLeQ : Nat.card (A ⧸ K) ≤ Q := by
    simpa [hQ] using hquotientLeA
  have hdM : D - a - hex.B0.card ≤ C.card := by
    have hcapC : b - Nat.card (A ⧸ K) + 2 ≤ C.card := by
      simpa [C] using hcapacity
    omega
  have hexact : M - d + hex.Bprime.card = 2 * Q := by
    dsimp only [M, d]
    omega
  refine ⟨{
    M := M
    d := d
    C := C
    B := B
    B0 := hex.B0
    Bprime := hex.Bprime
    C_eq := rfl
    B_eq := rfl
    Ccard := rfl
    B0_subset := by simpa [B] using hex.B0_subset
    Bprime_subset := by simpa [B] using hex.Bprime_subset
    B0_Bprime_disjoint := hex.disjoint
    B_partition := by simpa [B] using hex.partition
    B0_free := hex.B0_free
    Bprime_quotient_zero := hex.Bprime_zero
    d_eq := rfl
    a_B0_le_D := haB0D
    d_le_M := by simpa [M, d] using hdM
    CBprime_disjoint := hCBprime
    allC := by
      intro i hi
      have hi' : IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) ∈ K := by
        simpa [C, rotationOccurrencesIn] using hi
      exact hi'.1
    allBprime := by
      intro i hi
      exact (mem_rotationOccurrencesOutside_iff s K i).1
        ((by simpa [B] using hex.Bprime_subset hi)) |>.1
    BprimeOutside := by
      intro i hi
      exact (mem_rotationOccurrencesOutside_iff s K i).1
        ((by simpa [B] using hex.Bprime_subset hi)) |>.2
    exactSize := hexact
  }⟩

/-- The former rotation preparation now follows from mechanically extracted
data plus only the explicit quotient small-Davenport and GMO providers. -/
theorem rotationChannelPreparation_of_extraction
    (s : List (Group A)) (Q D a b Dq : ℕ) (K : AddSubgroup A)
    (htotal : a + b = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hDqD : Dq ≤ D)
    (hQ : Q = Nat.card A)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hguard : QuotientNoReflection s K)
    (hGMO : RotationChannelGMOProvider s Q D a b K) :
    RotationChannelPreparation s Q K := by
  rcases exists_rotationChannelPreGMOData s Q D a b Dq K
      htotal href hrot hsmall hDqD hQ hcapacity hguard with ⟨hdata⟩
  exact ⟨hdata.toPrepared (hGMO hdata)⟩

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.exists_rotationQuotientExtraction
#print axioms GaoLean.ConcreteGDihedral.RotationQuotientExtraction.coordinateSum_Bprime_mem
#print axioms GaoLean.ConcreteGDihedral.reflection_union_B0_quotientProductOneFree
#print axioms GaoLean.ConcreteGDihedral.exists_rotationChannelPreGMOData
#print axioms GaoLean.ConcreteGDihedral.RotationChannelPreGMOData.coordinateSum_Bprime_mem
#print axioms GaoLean.ConcreteGDihedral.RotationChannelPreGMOData.free_remainder_bound
#print axioms GaoLean.ConcreteGDihedral.RotationChannelPreGMOData.defect_ge_of_davenport_split
#print axioms GaoLean.ConcreteGDihedral.RotationChannelPreGMOData.defect_ge_of_davenport_bound
#print axioms GaoLean.ConcreteGDihedral.RotationChannelPreGMOData.target_ge_card_subgroup
#print axioms GaoLean.ConcreteGDihedral.rotationChannelPreparation_of_extraction
