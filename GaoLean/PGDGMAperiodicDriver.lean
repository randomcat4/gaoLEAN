import GaoLean.PGDGMCore
import GaoLean.PGDGMAmbientQuotient

/-!
# Boundary utilities for the aperiodic generalized DGM driver

This module contains genuine endpoint and labelled-layer reduction lemmas,
then assembles them with the proved full-weight crossed endpoint into the
unconditional nested driver.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [DecidableEq A]

/-- The generalized prescribed-pattern inequality at weight zero. -/
theorem dgmPatternBound_zero [Fintype A]
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K 0) :
    DGMPatternBound P μ := by
  classical
  unfold DGMPatternBound
  rw [patternSubsumSpectrum_zero_eq_singleton P μ]
  simp [stabilizerDgmCappedMultiplicitySum,
    dgmCappedMultiplicitySum, stabilizerLayerMultiplicity,
    quotientLayerMultiplicity]

/-- A quotient coset is met by at least one labelled layer exactly when its
layer multiplicity is positive. -/
theorem quotientLayerMultiplicity_pos_iff_mem_layerUnion
    (K : AddSubgroup A) [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (q : A ⧸ K) :
    0 < quotientLayerMultiplicity K P q ↔
      q ∈ quotientLayer K (layerUnion P) := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity, layerUnion, quotientLayer]
  | cons B P ih =>
      by_cases hq : q ∈ quotientLayer K B
      · rw [quotientLayerMultiplicity_cons_of_mem K B P q hq]
        obtain ⟨x, hx, hxq⟩ := (mem_quotientLayer_iff K B q).1 hq
        constructor
        · intro _
          exact (mem_quotientLayer_iff K _ q).2
            ⟨x, Finset.mem_union_left _ hx, hxq⟩
        · intro _
          omega
      · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hq, ih]
        constructor
        · intro htail
          obtain ⟨x, hx, hxq⟩ :=
            (mem_quotientLayer_iff K (layerUnion P) q).1 htail
          exact (mem_quotientLayer_iff K _ q).2
            ⟨x, Finset.mem_union_right _ hx, hxq⟩
        · intro hunion
          obtain ⟨x, hx, hxq⟩ :=
            (mem_quotientLayer_iff K (layerUnion (B :: P)) q).1 hunion
          rcases Finset.mem_union.mp hx with hxB | hxP
          · exact False.elim
              (hq ((mem_quotientLayer_iff K B q).2 ⟨x, hxB, hxq⟩))
          · exact (mem_quotientLayer_iff K (layerUnion P) q).2
              ⟨x, hxP, hxq⟩

/-- At weight one the capped quotient incidence is the number of quotient
cosets met by the union of all labelled layers. -/
theorem dgmCappedMultiplicitySum_one
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) :
    dgmCappedMultiplicitySum K P 1 =
      (quotientLayer K (layerUnion P)).card := by
  classical
  rw [dgmCappedMultiplicitySum]
  change (∑ q ∈ (@Finset.univ (A ⧸ K) (Fintype.ofFinite (A ⧸ K))),
      min 1 (quotientLayerMultiplicity K P q)) =
    (quotientLayer K (layerUnion P)).card
  have huniv : (@Finset.univ (A ⧸ K) (Fintype.ofFinite (A ⧸ K))) =
      (@Finset.univ (A ⧸ K) inferInstance) := by
    ext q
    simp
  rw [huniv]
  calc
    _ = ∑ q : A ⧸ K,
          if q ∈ quotientLayer K (layerUnion P) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : q ∈ quotientLayer K (layerUnion P)
      · have hm : 1 ≤ quotientLayerMultiplicity K P q :=
          (quotientLayerMultiplicity_pos_iff_mem_layerUnion K P q).2 hq
        simp [hq, min_eq_left hm]
      · have hm : quotientLayerMultiplicity K P q = 0 := by
          have := not_lt.mp (mt
            (quotientLayerMultiplicity_pos_iff_mem_layerUnion K P q).1 hq)
          omega
        simp [hq, hm]
    _ = (quotientLayer K (layerUnion P)).card := by
      rw [← Finset.card_eq_sum_ite
        (s := quotientLayer K (layerUnion P))
        (t := (Finset.univ : Finset (A ⧸ K)))
        (Finset.subset_univ _)]

/-- A pattern of total weight one is the indicator of its unique quotient
coset, which is also its multiplicity-weighted quotient sum. -/
theorem QuotientPattern.eq_indicator_quotientSum_of_weight_one
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (μ : QuotientPattern K 1) (q : A ⧸ K) :
    μ q = if μ.quotientSum = q then 1 else 0 := by
  classical
  have hex : ∃ q₀ : A ⧸ K, μ q₀ ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : (∑ r : A ⧸ K, μ r) = 0 := by simp [h]
    rw [μ.weight_eq] at hsum
    omega
  obtain ⟨q₀, hq₀⟩ := hex
  have hq₀one : μ q₀ = 1 := by
    have hle : μ q₀ ≤ ∑ r : A ⧸ K, μ r :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ q₀)
    rw [μ.weight_eq] at hle
    omega
  have hother : ∀ r : A ⧸ K, r ≠ q₀ → μ r = 0 := by
    intro r hr
    have hpair : (∑ x ∈ ({q₀, r} : Finset (A ⧸ K)), μ x) ≤
        ∑ x : A ⧸ K, μ x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [μ.weight_eq] at hpair
    simp [Ne.symm hr, hq₀one] at hpair
    omega
  have hsum : μ.quotientSum = q₀ := by
    unfold QuotientPattern.quotientSum
    calc
      (∑ r : A ⧸ K, μ r • r) =
          ∑ r : A ⧸ K, (if r = q₀ then 1 else 0) • r := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : r = q₀
        · subst r
          simp [hq₀one]
        · simp [hr, hother r hr]
      _ = q₀ := by simp
  rw [hsum]
  by_cases hq : q = q₀
  · subst q
    simp [hq₀one]
  · simp [Ne.symm hq, hother q hq]

/-- A proof-relevant weight-one choice has one quotient occurrence, at the
quotient of its chosen sum. -/
theorem LayerSubsumChoice.quotientMultiplicity_eq_indicator_of_weight_one
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {y : A} (h : LayerSubsumChoice P 1 y)
    (q : A ⧸ K) :
    h.quotientMultiplicity K q = if (y : A ⧸ K) = q then 1 else 0 := by
  change h.quotientPattern K q = _
  rw [QuotientPattern.eq_indicator_quotientSum_of_weight_one]
  rw [← h.coe_eq_pattern_quotientSum (h.realizes_quotientPattern K)]

/-- After choosing one realizing sum `y`, the entire weight-one pattern
spectrum is exactly the slice of the layer union through the `K`-coset of
`y`. -/
theorem patternSubsumSpectrum_one_eq_cosetSlice_layerUnion
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K 1)
    {y : A} (hy : y ∈ patternSubsumSpectrum P μ) :
    patternSubsumSpectrum P μ = dgmCosetSlice K (layerUnion P) y := by
  ext z
  constructor
  · intro hz
    have hzU : z ∈ layerUnion P := by
      have hzraw := patternSubsumSpectrum_subset_layerSubsumSpectrum P μ hz
      simpa [layerSubsumSpectrum_one] using hzraw
    have hzq := patternSubsumSpectrum_quotient_eq P μ hz
    have hyq := patternSubsumSpectrum_quotient_eq P μ hy
    exact (mem_dgmCosetSlice_iff K (layerUnion P) y z).2
      ⟨hzU, hzq.trans hyq.symm⟩
  · intro hz
    have hzdata := (mem_dgmCosetSlice_iff K (layerUnion P) y z).1 hz
    have hzraw : z ∈ layerSubsumSpectrum P 1 := by
      simpa [layerSubsumSpectrum_one] using hzdata.1
    obtain ⟨h⟩ := (nonempty_layerSubsumChoice_iff_mem P 1 z).2 hzraw
    apply (mem_patternSubsumSpectrum_iff P μ z).2
    refine ⟨⟨h, ?_⟩⟩
    intro q
    calc
      h.quotientMultiplicity K q =
          (if (z : A ⧸ K) = q then 1 else 0) :=
        h.quotientMultiplicity_eq_indicator_of_weight_one K q
      _ = (if μ.quotientSum = q then 1 else 0) := by
        rw [hzdata.2, patternSubsumSpectrum_quotient_eq P μ hy]
      _ = μ q :=
        (QuotientPattern.eq_indicator_quotientSum_of_weight_one K μ q).symm

/-- The first positive endpoint of the generalized prescribed-pattern DGM
inequality.  Quotient cosets outside the prescribed one are paid for by the
`K` correction term. -/
theorem dgmPatternBound_one [Fintype A]
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K 1)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty) :
    DGMPatternBound P μ := by
  classical
  let T : Finset A := patternSubsumSpectrum P μ
  let H : AddSubgroup A := AddAction.stabilizer A (T : Set A)
  have hT : T.Nonempty := by simpa [T] using hTarget
  obtain ⟨y, hy⟩ := hTarget
  have hyU : y ∈ layerUnion P := by
    have hyraw := patternSubsumSpectrum_subset_layerSubsumSpectrum P μ hy
    simpa [layerSubsumSpectrum_one] using hyraw
  have hspec : T = dgmCosetSlice K (layerUnion P) y := by
    simpa [T] using
      patternSubsumSpectrum_one_eq_cosetSlice_layerUnion K P μ hy
  have hHK : H ≤ K := by
    simpa [H, T] using
      patternSpectrum_stabilizer_le_patternSubgroup K 1 P μ (by
        simpa [T] using hT)
  have hweighted :=
    fullCosetSlice_weighted_incidence_le H K hHK (layerUnion P) hyU
  rw [← hspec] at hweighted
  have hperiodCard :
      Nat.card H * (quotientLayer H T).card = T.card := by
    have hstabFin : T.addStab = dgmSubgroupFinset H := by
      ext a
      rw [← Finset.mem_coe, Finset.coe_addStab hT]
      change a ∈ H ↔ a ∈ dgmSubgroupFinset H
      exact (mem_dgmSubgroupFinset_iff H a).symm
    have hadd : T + dgmSubgroupFinset H = T := by
      rw [← hstabFin, Finset.add_addStab]
    have hcard := card_add_dgmSubgroupFinset_eq H T
    rw [hadd] at hcard
    exact hcard.symm
  rw [hperiodCard] at hweighted
  have hHcap := dgmCappedMultiplicitySum_one H P
  have hKcap := dgmCappedMultiplicitySum_one K P
  have hTargetCap := dgmCappedMultiplicitySum_stabilizer_eq T P 1
  have hHpos : 1 ≤ (quotientLayer H (layerUnion P)).card :=
    Finset.one_le_card.mpr
      ⟨(y : A ⧸ H), (mem_quotientLayer_iff H _ _).2 ⟨y, hyU, rfl⟩⟩
  have hKpos : 1 ≤ (quotientLayer K (layerUnion P)).card :=
    Finset.one_le_card.mpr
      ⟨(y : A ⧸ K), (mem_quotientLayer_iff K _ _).2 ⟨y, hyU, rfl⟩⟩
  have hKsplit : Nat.card K * (quotientLayer K (layerUnion P)).card =
      Nat.card K * ((quotientLayer K (layerUnion P)).card - 1) +
        Nat.card K := by
    conv_lhs =>
      rw [show (quotientLayer K (layerUnion P)).card =
          (quotientLayer K (layerUnion P)).card - 1 + 1 by omega]
    simp [Nat.mul_add]
  unfold DGMPatternBound
  dsimp only
  change Nat.card H *
      (stabilizerDgmCappedMultiplicitySum T P 1 - 1 + 1) ≤
    T.card + Nat.card K * (dgmCappedMultiplicitySum K P 1 - 1)
  rw [← hTargetCap, hHcap, hKcap]
  have hHsimp : (quotientLayer H (layerUnion P)).card - 1 + 1 =
      (quotientLayer H (layerUnion P)).card := by omega
  rw [hHsimp]
  rw [hKsplit] at hweighted
  omega

/-- A proof-relevant choice which selects as many occurrences as the source
has labelled layers cannot skip a layer; consequently every source layer is
nonempty. -/
theorem LayerSubsumChoice.isNonemptySetPartition_of_weight_eq_length
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (hfull : n = P.length) :
    IsNonemptySetPartition P := by
  induction h with
  | zero P =>
      have hP : P = [] := List.length_eq_zero_iff.mp hfull.symm
      subst P
      intro C hC
      simp at hC
  | @skip B P n y h ih =>
      have hle := h.weight_le_length
      simp only [List.length_cons] at hfull
      omega
  | @take B P n b y hb h ih =>
      have htail : n = P.length := by
        simpa using Nat.succ.inj hfull
      have hP := ih htail
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hCP
      · exact ⟨b, hb⟩
      · exact hP C hCP

/-- A nonempty full-weight prescribed-pattern spectrum supplies an actual
full choice, and hence proves nonemptiness of every labelled source layer. -/
theorem isNonemptySetPartition_of_patternSubsumSpectrum_full
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K P.length)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty) :
    IsNonemptySetPartition P := by
  obtain ⟨y, hy⟩ := hTarget
  obtain ⟨⟨h, _⟩⟩ := (mem_patternSubsumSpectrum_iff P μ y).1 hy
  exact h.isNonemptySetPartition_of_weight_eq_length rfl

/-- A nonempty pattern spectrum with an empty leading labelled layer has
weight strictly below the source length: no realizing choice can take the
empty occurrence. -/
theorem patternSubsumSpectrum_cons_empty_nonempty_weight_lt_length
    (K : AddSubgroup A) {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n)
    (hTarget : (patternSubsumSpectrum (∅ :: P) μ).Nonempty) :
    n < (∅ :: P).length := by
  obtain ⟨y, hy⟩ := hTarget
  obtain ⟨⟨h, _⟩⟩ :=
    (mem_patternSubsumSpectrum_iff (∅ :: P) μ y).1 hy
  cases h with
  | zero => simp
  | skip htail =>
      have hle := htail.weight_le_length
      simp only [List.length_cons]
      omega
  | take hb _ => simp at hb

/-- Removing an empty leading layer strictly lowers the faithful inner
measure whenever the prescribed-pattern spectrum is unchanged.  The first
two coordinates agree and the bounded square defect drops in the third. -/
theorem dgmPatternInnerMeasure_tail_lt_cons_empty
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n)
    (hspec : patternSubsumSpectrum (∅ :: P) μ =
      patternSubsumSpectrum P μ) :
    DGMPatternInnerLt (dgmPatternInnerMeasure P μ)
      (dgmPatternInnerMeasure (∅ :: P) μ) := by
  have htotal : dgmTotalLayerCard P = dgmTotalLayerCard (∅ :: P) := by
    simp [dgmTotalLayerCard]
  have hbound := dgmLayerSquareSum_le_bound (A := A) P
  have hcardpos : 0 < (Fintype.card A) ^ 2 := by positivity
  have hmul : (P.length + 1) * (Fintype.card A) ^ 2 =
      P.length * (Fintype.card A) ^ 2 + (Fintype.card A) ^ 2 := by
    ring
  have hdefect : dgmLayerSquareDefect P <
      dgmLayerSquareDefect (∅ :: P) := by
    unfold dgmLayerSquareSum at hbound
    unfold dgmLayerSquareDefect
    simp only [List.length_cons, dgmLayerSquareSum, List.map_cons,
      List.sum_cons, Finset.card_empty, zero_pow (by omega : 2 ≠ 0),
      zero_add]
    rw [hmul]
    omega
  unfold dgmPatternInnerMeasure
  rw [hspec, htotal]
  exact Prod.Lex.right _
    (Prod.Lex.right _ (Prod.Lex.left _ _ hdefect))

/-- An explicit empty labelled occurrence can be deleted using only a
strictly smaller inner-measure instance.  Spectrum and both capped incidence
terms are transported exactly; no aperiodicity or full-cross hypothesis is
used. -/
theorem dgmPatternBound_of_mem_empty_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K n)
    (hEmpty : (∅ : Finset A) ∈ Q)
    (hmeasure : dgmPatternInnerMeasure Q μ = M)
    (hTarget : (patternSubsumSpectrum Q μ).Nonempty) :
    DGMPatternBound Q μ := by
  classical
  let P := Q.erase (∅ : Finset A)
  have hperm : Q.Perm ((∅ : Finset A) :: P) := by
    simpa [P] using List.perm_cons_erase hEmpty
  have hspectrumPerm := patternSubsumSpectrum_eq_of_perm hperm μ
  have hTargetHead :
      (patternSubsumSpectrum ((∅ : Finset A) :: P) μ).Nonempty := by
    rw [← hspectrumPerm]
    exact hTarget
  have hlt : n < ((∅ : Finset A) :: P).length :=
    patternSubsumSpectrum_cons_empty_nonempty_weight_lt_length
      K P μ hTargetHead
  have hall : ∀ C ∈ P, (∅ : Finset A) ⊆ C := by simp
  have hspec : patternSubsumSpectrum ((∅ : Finset A) :: P) μ =
      patternSubsumSpectrum P μ :=
    patternSubsumSpectrum_cons_eq_tail_of_head_subset_all
      (∅ : Finset A) P μ hall hlt
  have hmeasureLt : DGMPatternInnerLt
      (dgmPatternInnerMeasure P μ)
      (dgmPatternInnerMeasure ((∅ : Finset A) :: P) μ) :=
    dgmPatternInnerMeasure_tail_lt_cons_empty P μ hspec
  have hmeasureHead :
      dgmPatternInnerMeasure ((∅ : Finset A) :: P) μ = M :=
    (dgmPatternInnerMeasure_eq_of_perm hperm μ).symm.trans hmeasure
  have hltM : DGMPatternInnerLt (dgmPatternInnerMeasure P μ) M := by
    rw [← hmeasureHead]
    exact hmeasureLt
  have hsmall := ih (dgmPatternInnerMeasure P μ) hltM
  have hTargetTail : (patternSubsumSpectrum P μ).Nonempty := by
    rw [← hspec]
    exact hTargetHead
  have hboundTail : DGMPatternBound P μ :=
    hsmall K n inferInstance inferInstance P μ rfl hTargetTail
  have hboundHead : DGMPatternBound ((∅ : Finset A) :: P) μ := by
    unfold DGMPatternBound at hboundTail ⊢
    rw [hspec]
    simp only at hboundTail ⊢
    rw [stabilizerDgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
      (patternSubsumSpectrum P μ) (∅ : Finset A) P n hall hlt]
    rw [dgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
      K (∅ : Finset A) P n hall hlt]
    exact hboundTail
  exact (dgmPatternBound_iff_of_perm hperm μ).2 hboundHead

/-- Failure of nonempty-setpartition status is witnessed by an actual empty
labelled layer. -/
theorem empty_mem_of_not_isNonemptySetPartition
    (Q : List (Finset A)) (hQ : ¬IsNonemptySetPartition Q) :
    (∅ : Finset A) ∈ Q := by
  by_contra hEmpty
  apply hQ
  intro B hB
  exact Finset.nonempty_iff_ne_empty.mpr (by
    intro hBe
    subst B
    exact hEmpty hB)

/-- Empty-layer reduction in the form consumed by the final aperiodic case
split. -/
theorem dgmPatternBound_of_not_isNonemptySetPartition_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K n)
    (hQ : ¬IsNonemptySetPartition Q)
    (hmeasure : dgmPatternInnerMeasure Q μ = M)
    (hTarget : (patternSubsumSpectrum Q μ).Nonempty) :
    DGMPatternBound Q μ :=
  dgmPatternBound_of_mem_empty_strongIH M ih Q μ
    (empty_mem_of_not_isNonemptySetPartition Q hQ) hmeasure hTarget

/-- Equality-transport wrapper for the already proved full-weight singleton
quotient endpoint. -/
theorem dgmPatternBound_full_of_singleton_quotient_of_weight_eq
    [Fintype A] (K : AddSubgroup A)
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {n : ℕ} (P : List (Finset A)) (μ : QuotientPattern K n)
    (hfull : n = P.length) (hP : IsNonemptySetPartition P)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty)
    (hsingle : ∀ B ∈ P, (quotientLayer K B).card = 1) :
    DGMPatternBound P μ := by
  subst n
  exact dgmPatternBound_full_of_singleton_quotient
    K P μ hP hTarget hsingle

/-- Equality-transport wrapper for the proved full-weight cross-`K` endpoint. -/
theorem dgmPatternBound_fullWeight_crossK_of_weight_eq
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n)
    (hfull : n = P.length) (hP : IsNonemptySetPartition P)
    (hcross : ¬(∀ B ∈ P, (quotientLayer K B).card = 1))
    (hmeasure : dgmPatternInnerMeasure P μ = M)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty)
    (haper : (patternSubsumSpectrum P μ).addStab = {0}) :
    DGMPatternBound P μ := by
  subst n
  exact dgmPatternBound_fullWeight_crossK_strongIH
    M ih P hP μ hmeasure hTarget haper hcross

/-- Exact aperiodic case classifier at one inner measure.  Every branch is
now unconditional: the full-cross endpoint is supplied by the faithful
minimal-convergent proof in `PGDGMCore`. -/
theorem dgmPatternBound_aperiodic_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n)
    (hmeasure : dgmPatternInnerMeasure P μ = M)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty)
    (haper : (patternSubsumSpectrum P μ).addStab = {0}) :
    DGMPatternBound P μ := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact dgmPatternBound_zero K P μ
  by_cases hn1 : n = 1
  · subst n
    exact dgmPatternBound_one K P μ hTarget
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 2 := by
    use n - 2
    omega
  subst n
  by_cases hP : IsNonemptySetPartition P
  · have hle : k + 2 ≤ P.length :=
      patternSubsumSpectrum_nonempty_weight_le_length P μ hTarget
    rcases lt_or_eq_of_le hle with hlt | hfull
    · exact dgmPatternBound_of_weight_lt_length_strongIH
        M ih P μ hP hlt hmeasure hTarget haper
    · by_cases hsingle :
        ∀ B ∈ P, (quotientLayer K B).card = 1
      · exact dgmPatternBound_full_of_singleton_quotient_of_weight_eq
          K P μ hfull hP hTarget hsingle
      · exact dgmPatternBound_fullWeight_crossK_of_weight_eq
          M ih P μ hfull hP hsingle hmeasure hTarget haper
  · exact dgmPatternBound_of_not_isNonemptySetPartition_strongIH
      M ih P μ hP hmeasure hTarget

/-- Universe-safe unconditional double well-founded driver.  The outer theorem performs
strong induction on `Nat.card B` and quotients every periodic target by its
nontrivial stabilizer.  Inside each fixed group, well-founded induction on
`DGMPatternInnerLt` supplies the full smaller-measure theorem needed by the
aperiodic transformations; the full-cross branch is the proved Core endpoint. -/
theorem generalDGMPatternTheorem_of_doubleInduction :
    ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
      GeneralDGMPatternTheorem B := by
  classical
  have outer : ∀ m : ℕ, DGMPatternAtGroupCard.{u} m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ihGroup =>
        intro B instGroup instFintype instDecEq hm
        have inner : ∀ M : DGMPatternInnerMeasure,
            DGMPatternAtMeasure (A := B) M :=
          fun M ↦ dgmPatternInnerLt_wellFounded.induction M (fun M ihM ↦ by
            intro K n instQFintype instQDecEq P μ hmeasure hTarget
            let T : Finset B := patternSubsumSpectrum P μ
            let J : AddSubgroup B := AddAction.stabilizer B (T : Set B)
            have hJK : J ≤ K := by
              simpa [J, T] using
                patternSpectrum_stabilizer_le_patternSubgroup
                  K n P μ hTarget
            by_cases hJbot : J = ⊥
            · have haper : (patternSubsumSpectrum P μ).addStab = {0} := by
                apply Finset.ext
                intro x
                rw [← Finset.mem_coe, Finset.coe_addStab hTarget]
                change x ∈ J ↔ x ∈ ({0} : Finset B)
                rw [hJbot]
                simp
              exact dgmPatternBound_aperiodic_of_strongIH
                M ihM P μ hmeasure hTarget haper
            · letI : Fintype (B ⧸ J) := Fintype.ofFinite _
              letI : DecidableEq (B ⧸ J) := Classical.decEq _
              let qJ : B →+ B ⧸ J := QuotientAddGroup.mk' J
              let Kbar : AddSubgroup (B ⧸ J) := K.map qJ
              letI : Fintype ((B ⧸ J) ⧸ Kbar) := Fintype.ofFinite _
              letI : DecidableEq ((B ⧸ J) ⧸ Kbar) := Classical.decEq _
              let Pbar : List (Finset (B ⧸ J)) :=
                P.map fun C ↦ C.image qJ
              let μbar : QuotientPattern Kbar n :=
                μ.ambientQuotient J K hJK
              have hsmall : Nat.card (B ⧸ J) < m := by
                rw [← hm]
                exact natCard_quotient_lt_of_ne_bot J hJbot
              have hgeneralBar : GeneralDGMPatternTheorem (B ⧸ J) :=
                ihGroup (Nat.card (B ⧸ J)) hsmall (B ⧸ J) rfl
              have hTbar :
                  (patternSubsumSpectrum Pbar μbar).Nonempty := by
                have himage := hTarget.image qJ
                rw [image_patternSubsumSpectrum_ambientQuotient
                  J K hJK P μ] at himage
                simpa [Pbar, μbar, Kbar, qJ] using himage
              have hQ : DGMPatternBound Pbar μbar :=
                hgeneralBar Kbar n inferInstance inferInstance
                  Pbar μbar hTbar
              exact dgmPatternBound_of_ambientStabilizerQuotient
                J K hJK P μ hTarget (by simp [J, T]) (by
                  simpa [Pbar, μbar, Kbar, qJ] using hQ))
        intro K n instQFintype instQDecEq P μ hTarget
        exact inner (dgmPatternInnerMeasure P μ)
          K n instQFintype instQDecEq P μ rfl hTarget
  intro B instGroup instFintype instDecEq
  exact outer (Nat.card B) B rfl

/-- Unconditional general setpartition DGM obtained by specializing the
proved generalized pattern theorem to the top pattern. -/
theorem generalDGMSetpartitionTheorem_of_doubleInduction :
    ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
      GeneralDGMSetpartitionTheorem B := by
  intro B instGroup instFintype instDecEq
  exact generalDGMSetpartitionTheorem_of_generalPatternTheorem
    (generalDGMPatternTheorem_of_doubleInduction B)

end GaoLean
