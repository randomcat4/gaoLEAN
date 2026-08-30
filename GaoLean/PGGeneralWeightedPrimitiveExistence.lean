import GaoLean.PGGeneralWeightedAperiodicSplit
import GaoLean.PGGeneralWeightedStep6SingletonBranch
import GaoLean.PGGeneralWeightedSingletonRecursion
import GaoLean.PGGeneralWeightedSelectionConvolution
import GaoLean.PGGeneralWeightedReserveAssembly
import GaoLean.PGGeneralWeightedLemma35
import GaoLean.PGGeneralWeightedCrossTypeInduction
import GaoLean.PGGaoOrdinaryComplete

/-!
# Primitive prescribed-length Step 6 assembly

This file closes the two Step 6 branches that follow from the currently
verified interfaces alone.  Full exact spectrum immediately contains the
prescribed target.  If the difference kernel is bottom, every singleton
weighted occurrence has source value zero; a maximal weighted zero selection
off that pool can therefore be padded by literal singleton occurrences to
the requested cardinality.

The final theorem exposes the remaining nontrivial-kernel branch in exactly
the kernel/range dichotomy already proved by the Step 6 counting layer.  It
does not assume a GMO conclusion or a conclusion-shaped provider.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

noncomputable local instance primitiveExistenceSubgroupFintype
    (K : AddSubgroup A) : Fintype K :=
  Fintype.ofFinite K

/-! ## Fixed-selection weighted zero sums -/

/-- Data for a weighted zero sum supported on one specified set of source
occurrences.  Keeping the support fixed makes maximality arguments genuinely
occurrence-sensitive. -/
structure WeightedZeroSelectionData
    (W : Set ℤ) (xs : List A) (I : Selection xs) where
  weights : Occurrence xs → ℤ
  weights_mem : ∀ i ∈ I, weights i ∈ W
  weighted_sum : (∑ i ∈ I, weights i • occurrenceValue xs i) = 0

/-- Proposition-valued fixed-support existence predicate used by the finite
maximality argument. -/
def IsWeightedZeroSelection
    (W : Set ℤ) (xs : List A) (I : Selection xs) : Prop :=
  Nonempty (WeightedZeroSelectionData W xs I)

theorem isWeightedZeroSelection_empty (W : Set ℤ) (xs : List A) :
    IsWeightedZeroSelection W xs ∅ := by
  exact ⟨{
    weights := fun _ ↦ 0
    weights_mem := by simp
    weighted_sum := by simp
  }⟩

/-- A fixed-support zero selection is the same data needed for an exact
weighted sum of cardinality equal to the support cardinality. -/
theorem IsWeightedZeroSelection.nonempty_hasWeightedSumOfCard_card
    {W : Set ℤ} {xs : List A} {I : Selection xs}
    (h : IsWeightedZeroSelection W xs I) :
    Nonempty (HasWeightedSumOfCard W xs I.card 0) := by
  obtain ⟨h⟩ := h
  exact ⟨{
    selected := I
    weights := h.weights
    weights_mem := h.weights_mem
    card_selected := rfl
    weighted_sum := h.weighted_sum
  }⟩

/-- Disjoint occurrence-supported weighted zero sums may be joined. -/
theorem IsWeightedZeroSelection.union
    {W : Set ℤ} {xs : List A} {I J : Selection xs}
    (hI : IsWeightedZeroSelection W xs I)
    (hJ : IsWeightedZeroSelection W xs J)
    (hdis : Disjoint I J) :
    IsWeightedZeroSelection W xs (I ∪ J) := by
  classical
  obtain ⟨dI⟩ := hI
  obtain ⟨dJ⟩ := hJ
  let hI' : HasWeightedSumOfCard W xs I.card 0 := {
    selected := I
    weights := dI.weights
    weights_mem := dI.weights_mem
    card_selected := rfl
    weighted_sum := dI.weighted_sum
  }
  let hJ' : HasWeightedSumOfCard W xs J.card 0 := {
    selected := J
    weights := dJ.weights
    weights_mem := dJ.weights_mem
    card_selected := rfl
    weighted_sum := dJ.weighted_sum
  }
  let hU := hI'.disjointUnion hJ' hdis
  exact ⟨{
    weights := hU.weights
    weights_mem := by
      intro i hi
      exact hU.weights_mem i (by simpa [hU, hI', hJ'] using hi)
    weighted_sum := by simpa [hU, hI', hJ'] using hU.weighted_sum
  }⟩

/-- Re-index an occurrence-supported weighted zero sum by a proved support
cardinality. -/
theorem IsWeightedZeroSelection.nonempty_hasWeightedSumOfCard
    {W : Set ℤ} {xs : List A} {I : Selection xs}
    (h : IsWeightedZeroSelection W xs I) {n : ℕ}
    (hcard : I.card = n) :
    Nonempty (HasWeightedSumOfCard W xs n 0) := by
  rw [← hcard]
  exact h.nonempty_hasWeightedSumOfCard_card

/-! ## The bottom difference-kernel branch -/

/-- Under primitivity, if the difference kernel is top, every allowed weight
acts exactly like the distinguished weight and that action is injective.
Thus every weighted zero sum is an ordinary zero sum on the same labelled
selection. -/
theorem hasNonemptyZeroSum_of_weighted_of_differenceKernel_eq_top
    {W : Set ℤ} {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (hprimitive : IsPrimitiveWeightSet W)
    (htop : weightedDifferenceKernel W w₀ A = ⊤)
    (xs : List A) :
    HasNonemptyWeightedZeroSum W xs → HasNonemptyZeroSum xs := by
  classical
  intro hzero
  rcases hzero with ⟨j, hjpos, ⟨h⟩⟩
  have hf : Function.Injective (fun x : A ↦ w₀ • x) := by
    intro x y hxy
    apply weightedBaseWeight_injOn_weightedDifferenceKernel
      (A := A) hw₀ hprimitive
    · rw [htop]
      simp
    · rw [htop]
      simp
    · exact hxy
  refine ⟨h.selected, ?_, ?_⟩
  · apply Finset.card_pos.mp
    rw [h.card_selected]
    exact hjpos
  · apply hf
    change w₀ • (∑ i ∈ h.selected, occurrenceValue xs i) = w₀ • (0 : A)
    rw [Finset.smul_sum]
    calc
      ∑ i ∈ h.selected, w₀ • occurrenceValue xs i =
          ∑ i ∈ h.selected, h.weights i • occurrenceValue xs i := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiKernel : occurrenceValue xs i ∈
                weightedDifferenceKernel W w₀ A := by
              rw [htop]
              simp
            have hiLocus : occurrenceValue xs i ∈ weightedSingletonLocus W :=
              (mem_weightedDifferenceKernel_iff_singletonLocus
                hw₀ (occurrenceValue xs i)).1 hiKernel
            exact ((mem_weightedSingletonLocus_iff_smul_eq
              hw₀ (occurrenceValue xs i)).1 hiLocus
                (h.weights i) (h.weights_mem i hi)).symm
      _ = w₀ • (0 : A) := by rw [h.weighted_sum]; simp

/-- The top difference-kernel branch is the ordinary prescribed-length
theorem transported through the injective distinguished-weight action. -/
theorem weightedGMOExistenceConclusion_of_topDifferenceKernel
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (htop : weightedDifferenceKernel W w₀ A = ⊤) :
    WeightedGMOExistenceConclusion W xs n := by
  classical
  obtain ⟨Dordinary, hDordinary⟩ := exists_isOrdinaryDavenportConstant A
  have hOrdinaryAtMostD : OrdinaryDavenportAtMost A D := by
    intro ys hys
    exact hasNonemptyZeroSum_of_weighted_of_differenceKernel_eq_top
      hw₀ hprimitive htop ys (hD.1 ys hys)
  have hDordinaryLe : Dordinary ≤ D := by
    by_contra hnot
    have hlt : D < Dordinary := Nat.lt_of_not_ge hnot
    rcases hDordinary.2 D hlt with ⟨ys, hys, hfree⟩
    exact hfree (hOrdinaryAtMostD ys hys)
  have hDLeOrdinary : D ≤ Dordinary :=
    weightedDavenportConstant_le_of_atMost W A hD
      (weightedDavenportAtMost_of_ordinary hW Dordinary hDordinary.1)
  have hDEq : Dordinary = D := Nat.le_antisymm hDordinaryLe hDLeOrdinary
  obtain ⟨hout⟩ :=
    ordinaryGMOPrescribedLengthProvider_of_canonicalDStar
      A Dordinary hDordinary xs n hn (by simpa [hDEq] using hlen)
  obtain ⟨z, hz⟩ := hout.sum_mem_target
  refine ⟨w₀ • z, ⟨{
    selected := hout.selected
    weights := fun _ ↦ w₀
    weights_mem := fun _ _ ↦ hw₀
    card_selected := hout.card_selected
    weighted_sum := ?_
  }⟩⟩
  rw [← Finset.smul_sum, hz]
  have hcommute : ∀ m : ℕ, w₀ • (m • z) = m • (w₀ • z) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [succ_nsmul, zsmul_add, succ_nsmul, ih]
  exact hcommute n

/-- If the difference kernel is bottom and at least `D` weighted singleton
occurrences are present, Davenport maximality off the singleton pool plus
literal zero padding gives an exact `n`-term weighted zero sum.

This is the arbitrary-weight counterpart of the high-zero-multiplicity
prescribed-length argument in the signed specialization. -/
theorem hasWeightedSumOfCard_zero_of_bottomDifferenceKernel_of_manySingleton
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hlen : n + D - 1 ≤ xs.length)
    (hmany : D ≤ weightedSingletonOccurrenceCount W xs)
    (hbot : weightedDifferenceKernel W w₀ A = ⊥) :
    Nonempty (HasWeightedSumOfCard W xs n 0) := by
  classical
  let Z : Selection xs := weightedSingletonOccurrences W xs
  let N : Selection xs := Finset.univ \ Z
  have hZcard : Z.card ≤ xs.length := by
    simpa using Finset.card_le_card (Finset.subset_univ Z)
  have hmany' : D ≤ Z.card := by
    simpa [Z, card_weightedSingletonOccurrences_eq_count W xs] using hmany
  have hNcard : N.card = xs.length - Z.card := by
    dsimp only [N]
    rw [Finset.card_sdiff]
    simp
  have hDpos : 1 ≤ D := weightedDavenportConstant_pos W D hD
  let good : Finset (Selection xs) := Finset.univ.filter fun I ↦
    I ⊆ N ∧ I.card ≤ n ∧ IsWeightedZeroSelection W xs I
  have hemptyGood : (∅ : Selection xs) ∈ good := by
    simp [good, isWeightedZeroSelection_empty]
  obtain ⟨I, hIgood, hImax⟩ := Finset.exists_max_image good
    (fun J ↦ J.card) ⟨∅, hemptyGood⟩
  have hIsub : I ⊆ N := (Finset.mem_filter.mp hIgood).2.1
  have hIcardN : I.card ≤ n := (Finset.mem_filter.mp hIgood).2.2.1
  have hIzero : IsWeightedZeroSelection W xs I :=
    (Finset.mem_filter.mp hIgood).2.2.2
  have hIlarge : n - Z.card ≤ I.card := by
    by_contra hnot
    have hIsmall : I.card < n - Z.card := Nat.lt_of_not_ge hnot
    let R : Selection xs := N \ I
    have hRcard : D ≤ R.card := by
      have hcard : R.card = N.card - I.card := by
        dsimp only [R]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIsub]
      rw [hcard, hNcard]
      omega
    obtain ⟨Rd, hRdsub, hRdcard⟩ :=
      Finset.exists_subset_card_eq (s := R) hRcard
    have htlen : (occurrenceSubsequence xs Rd).length = D := by
      simpa [occurrenceSubsequence] using hRdcard
    obtain ⟨j, hjpos, ⟨hj⟩⟩ :=
      hD.1 (occurrenceSubsequence xs Rd) htlen
    let hLift : HasWeightedSumOfCard W xs j 0 :=
      hj.liftOccurrenceSubsequence
    let J : Selection xs := hLift.selected
    have hJsubRd : J ⊆ Rd := by
      dsimp only [J, hLift]
      exact liftOccurrenceSubsequenceSelection_subset xs Rd hj.selected
    have hJsubR : J ⊆ R := hJsubRd.trans hRdsub
    have hJsubN : J ⊆ N := by
      intro q hq
      exact (Finset.mem_sdiff.mp (hJsubR hq)).1
    have hdis : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro q hqI hqJ
      exact (Finset.mem_sdiff.mp (hJsubR hqJ)).2 hqI
    have hJcard : J.card = j := hLift.card_selected
    have hJcardD : J.card ≤ D := by
      rw [hJcard]
      exact hj.card_le_length.trans_eq htlen
    have hJzero : IsWeightedZeroSelection W xs J := by
      exact ⟨{
        weights := hLift.weights
        weights_mem := hLift.weights_mem
        weighted_sum := hLift.weighted_sum
      }⟩
    have hUnionSub : I ∪ J ⊆ N := Finset.union_subset hIsub hJsubN
    have hUnionCard : (I ∪ J).card ≤ n := by
      rw [Finset.card_union_of_disjoint hdis]
      omega
    have hUnionZero : IsWeightedZeroSelection W xs (I ∪ J) :=
      hIzero.union hJzero hdis
    have hUnionGood : I ∪ J ∈ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hUnionSub, hUnionCard, hUnionZero⟩
    have hmaxUnion : (I ∪ J).card ≤ I.card := hImax _ hUnionGood
    rw [Finset.card_union_of_disjoint hdis] at hmaxUnion
    have hJne : J.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hJeq
      have : J.card = 0 := by simp [hJeq]
      rw [hJcard] at this
      omega
    have hJcardPos : 0 < J.card := Finset.card_pos.mpr hJne
    omega
  let k := n - I.card
  have hkZ : k ≤ Z.card := by
    dsimp only [k]
    omega
  obtain ⟨F, hFsub, hFcard⟩ :=
    Finset.exists_subset_card_eq (s := Z) hkZ
  have hdisIF : Disjoint I F := by
    rw [Finset.disjoint_left]
    intro i hiI hiF
    have hiN := hIsub hiI
    exact (Finset.mem_sdiff.mp hiN).2 (hFsub hiF)
  have hFzero : IsWeightedZeroSelection W xs F := by
    exact ⟨{
      weights := fun _ ↦ w₀
      weights_mem := fun _ _ ↦ hw₀
      weighted_sum := by
        apply Finset.sum_eq_zero
        intro i hi
        have hiZ : i ∈ weightedSingletonOccurrences W xs := by
          exact hFsub hi
        have hiFiber :=
          weightedSingletonOccurrences_subset_zeroFiber_of_kernel_eq_bot
            hW hw₀ xs hbot hiZ
        have hvalue : occurrenceValue xs i = 0 := by
          simpa [occurrenceFiber] using hiFiber
        simp [hvalue]
    }⟩
  have hUnionZero : IsWeightedZeroSelection W xs (I ∪ F) :=
    hIzero.union hFzero hdisIF
  have hUnionCard : (I ∪ F).card = n := by
    rw [Finset.card_union_of_disjoint hdisIF, hFcard]
    dsimp only [k]
    omega
  exact hUnionZero.nonempty_hasWeightedSumOfCard hUnionCard

/-- Bottom difference kernel closes the prescribed-target conclusion, with
target center zero. -/
theorem weightedGMOExistenceConclusion_of_bottomDifferenceKernel_of_manySingleton
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hlen : n + D - 1 ≤ xs.length)
    (hmany : D ≤ weightedSingletonOccurrenceCount W xs)
    (hbot : weightedDifferenceKernel W w₀ A = ⊥) :
    WeightedGMOExistenceConclusion W xs n := by
  refine ⟨0, ?_⟩
  simpa using
    hasWeightedSumOfCard_zero_of_bottomDifferenceKernel_of_manySingleton
      hW hw₀ D hD xs n hlen hmany hbot

/-! ## Actual recursive products in the proper-kernel branch -/

/-- The kernel-budget side really invokes the prescribed-length provider on
the difference-kernel subtype at its own exact Davenport value.  At target
`|K|` the recursive target is zero; singleton-recursion then lifts that exact
zero core to the original labelled source. -/
theorem hasWeightedSumOfCard_zero_of_kernelRecursiveProvider
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A)
    (hcount : Nat.card (weightedDifferenceKernel W w₀ A) + D - 1 ≤
      weightedSingletonOccurrenceCount W xs)
    (hprovider : GeneralWeightedGMOExistenceProvider
      (weightedDifferenceKernel W w₀ A)) :
    Nonempty (HasWeightedSumOfCard W xs
      (Nat.card (weightedDifferenceKernel W w₀ A)) 0) := by
  classical
  let K := weightedDifferenceKernel W w₀ A
  let DK := weightedDavenportValue W K hW
  change GeneralWeightedGMOExistenceProvider K at hprovider
  have hcountK : Nat.card K + D - 1 ≤
      weightedSingletonOccurrenceCount W xs := by
    simpa [K] using hcount
  have hDAeq : weightedDavenportValue W A hW = D :=
    isWeightedDavenportConstant_unique W A
      (weightedDavenportValue_spec W A hW) hD
  have hDKle : DK ≤ D := by
    dsimp only [DK]
    exact (weightedDavenportValue_subgroup_le_ambient hW K).trans_eq hDAeq
  have hlength : Nat.card K + DK - 1 ≤
      (weightedSingletonKernelSubsequence hW hw₀ xs).length := by
    rw [length_weightedSingletonKernelSubsequence hW hw₀ xs]
    omega
  obtain ⟨x, ⟨hx⟩⟩ := hprovider W hW DK
    (weightedDavenportValue_spec W K hW)
    (weightedSingletonKernelSubsequence hW hw₀ xs) (Nat.card K)
    (by rfl) hlength
  have hzero : Nat.card K • x = 0 := card_nsmul_eq_zero'
  have hxzero : HasWeightedSumOfCard W
      (weightedSingletonKernelSubsequence hW hw₀ xs)
      (Nat.card K) 0 := by
    simpa [hzero] using hx
  exact ⟨hxzero.liftSingletonKernelSubsequence hW hw₀⟩

/-- The kernel-budget branch needs only the strong recursion state for the
top subgroup of the fixed difference kernel; it does not need a provider
quantified over every weight set.

The strong state supplies an exact `|K| • beta` witness on the literal
singleton-kernel occurrence list.  Finiteness of `K` makes that target zero,
after which the existing occurrence-faithful singleton lift returns the
witness to the original source. -/
theorem hasWeightedSumOfCard_zero_of_kernelStrongRecursionAtTop
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A)
    (hcount : Nat.card (weightedDifferenceKernel W w₀ A) + D - 1 ≤
      weightedSingletonOccurrenceCount W xs)
    (hstrong : GeneralWeightedStrongRecursionAt
      (⊤ : AddSubgroup (weightedDifferenceKernel W w₀ A))) :
    Nonempty (HasWeightedSumOfCard W xs
      (Nat.card (weightedDifferenceKernel W w₀ A)) 0) := by
  classical
  let K := weightedDifferenceKernel W w₀ A
  let KT : AddSubgroup K := ⊤
  let DKT := weightedDavenportValue W KT hW
  let ks := weightedSingletonKernelSubsequence hW hw₀ xs
  have hDAeq : weightedDavenportValue W A hW = D :=
    isWeightedDavenportConstant_unique W A
      (weightedDavenportValue_spec W A hW) hD
  have hDKle : weightedDavenportValue W K hW ≤ D :=
    (weightedDavenportValue_subgroup_le_ambient hW K).trans_eq hDAeq
  have hDKTle : DKT ≤ D := by
    exact (weightedDavenportValue_subgroup_le_ambient hW KT).trans hDKle
  have hKTcard : Nat.card KT = Nat.card K := by
    simpa [KT] using (AddSubgroup.card_top (G := K))
  have hlength : Nat.card K + DKT - 1 ≤ ks.length := by
    rw [length_weightedSingletonKernelSubsequence hW hw₀ xs]
    have hcountK : Nat.card K + D - 1 ≤
        weightedSingletonOccurrenceCount W xs := by
      simpa [K] using hcount
    omega
  have hinput : GeneralWeightedOvergroupInput W KT 0 0 ks := by
    constructor <;> intro i
    · simp [KT]
    · intro w hw
      simp [KT]
  obtain ⟨S⟩ := hstrong W hW hprimitive DKT
    (weightedDavenportValue_spec W KT hW) 0 0 ks (Nat.card K)
    hKTcard.le hinput hlength
  obtain ⟨hx⟩ := S.nonempty_hasWeightedSumOfCard_nsmul_beta
  have hzero : Nat.card K • S.beta = 0 := card_nsmul_eq_zero'
  have hxzero : HasWeightedSumOfCard W ks (Nat.card K) 0 := by
    rw [hzero] at hx
    exact hx
  exact ⟨hxzero.liftSingletonKernelSubsequence hW hw₀⟩

/-- The range-budget side really invokes the occurrence-labelled weighted
Lemma 3.5 on the literal nonsingleton occurrence pool.  Properness of the
difference kernel makes its homomorphic range nontrivial. -/
theorem generalWeightedLemma35Certificate_of_differenceRangeBudget
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A)
    (hkernelProper : weightedDifferenceKernel W w₀ A ≠ ⊤)
    (hcount : Nat.card (weightedDifferenceRange W w₀ A) ≤
      weightedNonsingletonOccurrenceCount W xs) :
    Nonempty (GeneralWeightedLemma35Certificate W xs
      (weightedNonsingletonOccurrences W xs)
      (weightedDifferenceRange W w₀ A)) := by
  classical
  let K := weightedDifferenceRange W w₀ A
  let R := weightedNonsingletonOccurrences W xs
  have hKne : K ≠ ⊥ := by
    intro hKbot
    apply hkernelProper
    apply top_unique
    intro x _hx
    change weightedDifferenceHom W w₀ A x = 0
    have hxRange : weightedDifferenceHom W w₀ A x ∈ K := ⟨x, rfl⟩
    rw [hKbot, AddSubgroup.mem_bot] at hxRange
    exact hxRange
  have hcardTwo : ∀ i ∈ R,
      2 ≤ (weightedValueBlock W (occurrenceValue xs i)).card := by
    intro i hi
    have hne : (weightedValueBlock W (occurrenceValue xs i)).card ≠ 1 :=
      (mem_weightedNonsingletonOccurrences_iff W xs i).1 hi
    have hpos : 0 < (weightedValueBlock W (occurrenceValue xs i)).card :=
      Finset.card_pos.mpr
        (weightedValueBlock_nonempty hW (occurrenceValue xs i))
    omega
  have hlength : Nat.card K - 1 ≤ R.card := by
    have hRcard : R.card = weightedNonsingletonOccurrenceCount W xs := by
      exact card_weightedNonsingletonOccurrences_eq_count hW xs
    dsimp only [K, R]
    rw [hRcard]
    omega
  exact generalWeightedLemma35Certificate_exists
    W hW w₀ hw₀ xs R hKne hcardTwo hlength

/-! ## Honest endpoint of the currently assembled Step 6 branches -/

/-- In the primitive aperiodic branch, the checked components now close the
full-spectrum case and the bottom difference-kernel case.  Otherwise the
only remaining branch has a genuinely nontrivial difference kernel and is
already split into the exact kernel-recursive budget or the range-side
Lemma 3.5 budget.

The residual disjunction is mathematical data, not a provider premise. -/
theorem primitiveAperiodicExistence_or_step6KernelRangeResidual
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥) :
    WeightedGMOExistenceConclusion W xs n ∨
      ∃ w₀ ∈ W,
        weightedDifferenceKernel W w₀ A ≠ ⊥ ∧
        weightedDifferenceKernel W w₀ A ≠ ⊤ ∧
          (Nat.card (weightedDifferenceKernel W w₀ A) + D - 1 ≤
              weightedSingletonOccurrenceCount W xs ∨
            Nat.card (weightedDifferenceRange W w₀ A) ≤
              weightedNonsingletonOccurrenceCount W xs) := by
  classical
  obtain ⟨w₀, hw₀⟩ := hW
  have hW' : W.Nonempty := ⟨w₀, hw₀⟩
  rcases weightedExactSpectrum_eq_univ_or_manySingleton_of_bottomStabilizer
      hW' D hD xs n hn hlen hstab with hfull | hmany
  · left
    refine ⟨0, (mem_weightedExactSpectrum_iff W xs n (n • (0 : A))).1 ?_⟩
    rw [hfull]
    simp
  · have hDpos : 1 ≤ D := weightedDavenportConstant_pos W D hD
    have hmanyD : D ≤ weightedSingletonOccurrenceCount W xs := by
      have hcardPos : 1 ≤ Nat.card A := Nat.card_pos
      omega
    by_cases hbot : weightedDifferenceKernel W w₀ A = ⊥
    · left
      exact weightedGMOExistenceConclusion_of_bottomDifferenceKernel_of_manySingleton
        hW' hw₀ D hD xs n hlen hmanyD hbot
    · by_cases htop : weightedDifferenceKernel W w₀ A = ⊤
      · left
        exact weightedGMOExistenceConclusion_of_topDifferenceKernel
          hW' hw₀ hprimitive D hD xs n hn hlen htop
      · right
        refine ⟨w₀, hw₀, hbot, htop, ?_⟩
        apply weighted_singletonKernel_or_nonsingletonRange_count
          hW' hw₀ xs D hDpos
        · omega
        · exact hbot

/-- Legacy provider-based proper-kernel assembly.  This remains useful as a
corollary interface, but its provider is quantified over all nonempty weight
sets and is therefore stronger than the fixed-`W` strong recursion hypothesis
used by the source proof. -/
theorem primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥)
    (hrecursive : ∀ K : AddSubgroup A,
      K ≠ ⊥ → K ≠ ⊤ → GeneralWeightedGMOExistenceProvider K) :
    WeightedGMOExistenceConclusion W xs n ∨
      ∃ w₀ ∈ W,
        weightedDifferenceKernel W w₀ A ≠ ⊥ ∧
        weightedDifferenceKernel W w₀ A ≠ ⊤ ∧
          (Nonempty (HasWeightedSumOfCard W xs
              (Nat.card (weightedDifferenceKernel W w₀ A)) 0) ∨
            Nonempty (GeneralWeightedLemma35Certificate W xs
              (weightedNonsingletonOccurrences W xs)
              (weightedDifferenceRange W w₀ A))) := by
  rcases primitiveAperiodicExistence_or_step6KernelRangeResidual
      hW hprimitive D hD xs n hn hlen hstab with hdone | hresidual
  · exact Or.inl hdone
  · right
    obtain ⟨w₀, hw₀, hKbot, hKtop, hkernel | hrange⟩ := hresidual
    · refine ⟨w₀, hw₀, hKbot, hKtop, Or.inl ?_⟩
      exact hasWeightedSumOfCard_zero_of_kernelRecursiveProvider
        hW hw₀ D hD xs hkernel
          (hrecursive (weightedDifferenceKernel W w₀ A) hKbot hKtop)
    · refine ⟨w₀, hw₀, hKbot, hKtop, Or.inr ?_⟩
      exact generalWeightedLemma35Certificate_of_differenceRangeBudget
        hW hw₀ xs hKtop hrange

/-- Proper-kernel assembly driven by the honest fixed-weight strong recursion
state on each strict nontrivial kernel.  Unlike the legacy provider version,
this premise does not quantify over unrelated weight sets.

The result is still a local zero core or a Lemma-3.5 certificate, not the full
equation-(3)--(9) parent state. -/
theorem primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate_of_strongRecursion
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥)
    (hrecursive : ∀ K : AddSubgroup A,
      K ≠ ⊥ → K ≠ ⊤ →
        GeneralWeightedStrongRecursionAt (⊤ : AddSubgroup K)) :
    WeightedGMOExistenceConclusion W xs n ∨
      ∃ w₀ ∈ W,
        weightedDifferenceKernel W w₀ A ≠ ⊥ ∧
        weightedDifferenceKernel W w₀ A ≠ ⊤ ∧
          (Nonempty (HasWeightedSumOfCard W xs
              (Nat.card (weightedDifferenceKernel W w₀ A)) 0) ∨
            Nonempty (GeneralWeightedLemma35Certificate W xs
              (weightedNonsingletonOccurrences W xs)
              (weightedDifferenceRange W w₀ A))) := by
  rcases primitiveAperiodicExistence_or_step6KernelRangeResidual
      hW hprimitive D hD xs n hn hlen hstab with hdone | hresidual
  · exact Or.inl hdone
  · right
    obtain ⟨w₀, hw₀, hKbot, hKtop, hkernel | hrange⟩ := hresidual
    · refine ⟨w₀, hw₀, hKbot, hKtop, Or.inl ?_⟩
      exact hasWeightedSumOfCard_zero_of_kernelStrongRecursionAtTop
        hW hprimitive hw₀ D hD xs hkernel
          (hrecursive (weightedDifferenceKernel W w₀ A) hKbot hKtop)
    · refine ⟨w₀, hw₀, hKbot, hKtop, Or.inr ?_⟩
      exact generalWeightedLemma35Certificate_of_differenceRangeBudget
        hW hw₀ xs hKtop hrange

/-- The proper-kernel local products obtained directly from the cross-type
strict-cardinality recursion hypothesis at the ambient top subgroup.

This theorem removes the last adapter premise from the preceding fixed-weight
version: strictness of each proper kernel supplies the strong state on its own
top subgroup through `applySubgroupTop`.  The parent equation-(3)--(9) state is
still not claimed here. -/
theorem primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate_of_crossTypeIH
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥)
    (ih : GeneralWeightedCrossTypeSmallerCardRecursionHypothesis
      (⊤ : AddSubgroup A)) :
    WeightedGMOExistenceConclusion W xs n ∨
      ∃ w₀ ∈ W,
        weightedDifferenceKernel W w₀ A ≠ ⊥ ∧
        weightedDifferenceKernel W w₀ A ≠ ⊤ ∧
          (Nonempty (HasWeightedSumOfCard W xs
              (Nat.card (weightedDifferenceKernel W w₀ A)) 0) ∨
            Nonempty (GeneralWeightedLemma35Certificate W xs
              (weightedNonsingletonOccurrences W xs)
              (weightedDifferenceRange W w₀ A))) := by
  apply
    primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate_of_strongRecursion
      hW hprimitive D hD xs n hn hlen hstab
  intro K hKbot hKtop
  exact ih.applySubgroupTop K (lt_top_iff_ne_top.mpr hKtop)

end GaoLean

#print axioms GaoLean.IsWeightedZeroSelection.union
#print axioms GaoLean.hasNonemptyZeroSum_of_weighted_of_differenceKernel_eq_top
#print axioms GaoLean.weightedGMOExistenceConclusion_of_topDifferenceKernel
#print axioms GaoLean.hasWeightedSumOfCard_zero_of_bottomDifferenceKernel_of_manySingleton
#print axioms GaoLean.weightedGMOExistenceConclusion_of_bottomDifferenceKernel_of_manySingleton
#print axioms GaoLean.primitiveAperiodicExistence_or_step6KernelRangeResidual
#print axioms GaoLean.hasWeightedSumOfCard_zero_of_kernelRecursiveProvider
#print axioms GaoLean.hasWeightedSumOfCard_zero_of_kernelStrongRecursionAtTop
#print axioms GaoLean.generalWeightedLemma35Certificate_of_differenceRangeBudget
#print axioms GaoLean.primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate
#print axioms GaoLean.primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate_of_strongRecursion
#print axioms GaoLean.primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate_of_crossTypeIH
