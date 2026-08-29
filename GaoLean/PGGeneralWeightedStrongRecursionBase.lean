import GaoLean.PGGeneralWeightedStrongRecursionState

/-!
# Bottom-subgroup base case for the strong general-weight recursion

For `G = ⊥`, the overgroup input forces every source occurrence to equal
the incoming source centre and every allowed weighted value to equal the
incoming weighted centre.  Consequently every feasible exact weighted
spectrum is a singleton.  This file uses that fact to construct all fields
of the frozen equations-(3)--(9) state, including a literal one-occurrence
core and small carrier.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

noncomputable local instance strongRecursionBaseDecidableEq
    {X : Type*} : DecidableEq X :=
  Classical.decEq X

/-! ## Two elementary singleton-spectrum facts -/

/-- Every nonempty weight set has weighted Davenport constant one on a
subsingleton finite additive group. -/
theorem isWeightedDavenportConstant_one_of_subsingleton
    {B : Type v} [AddCommGroup B] [Fintype B] [Subsingleton B]
    {W : Set ℤ} (hW : W.Nonempty) :
    IsWeightedDavenportConstant W B 1 := by
  classical
  obtain ⟨w₀, hw₀⟩ := hW
  constructor
  · intro ys hys
    refine ⟨1, by omega, ⟨{
      selected := Finset.univ
      weights := fun _ ↦ w₀
      weights_mem := fun _ _ ↦ hw₀
      card_selected := by simpa [Occurrence] using hys
      weighted_sum := by
        apply Finset.sum_eq_zero
        intro i _hi
        rw [show occurrenceValue ys i = 0 from Subsingleton.elim _ _]
        simp
    }⟩⟩
  · intro m hm
    have hmzero : m = 0 := by omega
    subst m
    refine ⟨[], rfl, ?_⟩
    rintro ⟨k, hk, ⟨z⟩⟩
    have hkzero : k = 0 := by
      have := z.card_le_length
      simpa using this
    omega

/-- If every allowed weighted value at every labelled occurrence is the
same element `beta`, then every feasible exact spectrum is the singleton
`{k * beta}`. -/
theorem weightedExactSpectrum_eq_singleton_of_weightedValue_eq
    {B : Type v} [AddCommGroup B] [Fintype B]
    {W : Set ℤ} (hW : W.Nonempty) (ys : List B) (k : ℕ) (beta : B)
    (hvalue : ∀ i : Occurrence ys, ∀ w ∈ W,
      w • occurrenceValue ys i = beta)
    (hk : k ≤ ys.length) :
    weightedExactSpectrum W ys k = {k • beta} := by
  classical
  ext y
  rw [mem_weightedExactSpectrum_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨z⟩
    calc
      y = ∑ i ∈ z.selected,
          z.weights i • occurrenceValue ys i := z.weighted_sum.symm
      _ = ∑ _i ∈ z.selected, beta := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hvalue i (z.weights i) (z.weights_mem i hi)
      _ = k • beta := by simp [z.card_selected]
  · rintro rfl
    obtain ⟨w₀, hw₀⟩ := hW
    obtain ⟨I, _hIuniv, hIcard⟩ :=
      Finset.exists_subset_card_eq
        (s := (Finset.univ : Selection ys)) (by simpa using hk)
    exact ⟨{
      selected := I
      weights := fun _ ↦ w₀
      weights_mem := fun _ _ ↦ hw₀
      card_selected := hIcard
      weighted_sum := by
        calc
          ∑ i ∈ I, w₀ • occurrenceValue ys i =
              ∑ _i ∈ I, beta := by
                apply Finset.sum_congr rfl
                intro i _hi
                exact hvalue i w₀ hw₀
          _ = k • beta := by simp [hIcard]
    }⟩

/-! ## The unconditional bottom strong-recursion state -/

variable {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]

/-- The genuine strong-recursion base case.  No provider or engine is an
input: every field of the equation-(3)--(9) state is constructed directly
from the bottom overgroup hypothesis. -/
theorem generalWeightedStrongRecursionAt_bot :
    GeneralWeightedStrongRecursionAt (⊥ : AddSubgroup G₀) := by
  classical
  intro W hW _hprimitive D hD gamma delta xs n hn hinput hlen
  let G : AddSubgroup G₀ := ⊥
  let H : AddSubgroup G₀ := ⊥
  have hDbot : IsWeightedDavenportConstant W G 1 :=
    isWeightedDavenportConstant_one_of_subsingleton hW
  have hDone : D = 1 :=
    isWeightedDavenportConstant_unique W G hD hDbot
  have hGcard : Nat.card G = 1 := by simp [G]
  have hHcard : Nat.card H = 1 := by simp [H]
  have hnpos : 1 ≤ n := by simpa [G] using hn
  have hnlen : n ≤ xs.length := by omega
  have hlenpos : 1 ≤ xs.length := hnpos.trans hnlen
  have hsource (i : Occurrence xs) : occurrenceValue xs i = gamma := by
    apply sub_eq_zero.mp
    simpa [G] using hinput.source_mem i
  have hweighted (i : Occurrence xs) (w : ℤ) (hw : w ∈ W) :
      w • occurrenceValue xs i = delta := by
    apply sub_eq_zero.mp
    simpa [G] using hinput.weighted_mem i w hw
  obtain ⟨core, _hcoreUniv, hcoreCard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Selection xs)) (by simpa using hlenpos)
  let retained : Selection xs := Finset.univ
  let small : Selection xs := core
  let Q := G ⧸ H.addSubgroupOf G
  letI : Subsingleton Q := by
    constructor
    intro x y
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      induction y using QuotientAddGroup.induction_on with
      | _ y =>
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        simp [G, H]
  have hQexact : IsWeightedDavenportConstant W Q 1 :=
    isWeightedDavenportConstant_one_of_subsingleton hW
  have hQcard : Nat.card Q = 1 := by
    letI : Unique Q := uniqueOfSubsingleton 0
    simp
  have hambientSpectrum :
      weightedExactSpectrum W xs n = {n • delta} :=
    weightedExactSpectrum_eq_singleton_of_weightedValue_eq
      hW xs n delta hweighted hnlen
  have hsmallLength : (occurrenceSubsequence xs small).length = 1 := by
    simpa [small, occurrenceSubsequence] using hcoreCard
  have hsmallWeighted
      (i : Occurrence (occurrenceSubsequence xs small))
      (w : ℤ) (hw : w ∈ W) :
      w • occurrenceValue (occurrenceSubsequence xs small) i = delta := by
    rw [occurrenceValue_occurrenceSubsequence]
    exact hweighted (occurrenceSubsequenceSource xs small i) w hw
  have hsmallSpectrum :
      weightedExactSpectrumOn W xs small 1 = {delta} := by
    unfold weightedExactSpectrumOn
    simpa using
      weightedExactSpectrum_eq_singleton_of_weightedValue_eq
        hW (occurrenceSubsequence xs small) 1 delta hsmallWeighted
          (by simpa [hsmallLength])
  have htranslate :
      translateWeightedSpectrum ((n - 1) • delta) {delta} =
        {n • delta} := by
    have hcoef : (n - 1) • delta + delta = n • delta := by
      rw [← succ_nsmul]
      congr 1
      omega
    ext y
    simp [translateWeightedSpectrum, hcoef]
  refine ⟨{
    H := H
    H_le_G := by simp [H, G]
    alpha := gamma
    beta := delta
    alpha_sub_gamma_mem := by simp [G]
    beta_sub_delta_mem := by simp [G]
    retained := retained
    core := core
    small := small
    core_subset_retained := by simp [retained]
    retained_sourceCoset := by
      intro i _hi
      simp [H, hsource i]
    retained_weightCoset := by
      intro i _hi w hw
      simp [H, hweighted i w hw]
    retained_card_lower := by
      have hmin := min_le_left xs.length
        (xs.length - Nat.card (G ⧸ H.addSubgroupOf G) + 2)
      simpa [retained, Selection, Occurrence] using hmin
    DH := 1
    DQ := 1
    DH_exact := by simpa [H, G] using hDbot
    DQ_exact := by simpa [Q] using hQexact
    core_card := by simp [hcoreCard, hHcard]
    core_full := by
      intro h
      obtain ⟨w₀, hw₀⟩ := hW
      have hhzero : (h : G₀) = 0 := by
        have hm : (h : G₀) ∈ (⊥ : AddSubgroup G₀) := by
          simpa [H] using h.property
        exact AddSubgroup.mem_bot.mp hm
      refine ⟨{
        selected := core
        weights := fun _ ↦ w₀
        weights_mem := fun _ _ ↦ hw₀
        card_selected := by simpa [hHcard] using hcoreCard
        weighted_sum := ?_
      }, Finset.Subset.rfl⟩
      calc
        ∑ i ∈ core, w₀ • occurrenceValue xs i =
            ∑ _i ∈ core, delta := by
              apply Finset.sum_congr rfl
              intro i _hi
              exact hweighted i w₀ hw₀
        _ = delta := by simp [hcoreCard]
        _ = Nat.card H • delta + (h : G₀) := by
          simp [hHcard, hhzero]
    r := 0
    r_eq_complement_card := by simp [retained]
    r_le_quotient_sub_two := Nat.zero_le _
    outside_union_core_subset_small := by simp [retained, small]
    H_card_add_r_le_n := by simpa [hHcard] using hnpos
    small_card := by simp [small, hcoreCard, hHcard, hQcard]
    small_card_upper := by simp [small, hcoreCard, hHcard, hDone]
    spectrum_periodic := by simp [H]
    spectrum_reduction := by
      rw [hambientSpectrum, hHcard]
      simp only [Nat.add_zero, Nat.sub_zero]
      rw [hsmallSpectrum, htranslate]
    small_center_mem := by
      rw [hHcard]
      simp only [Nat.add_zero, one_nsmul]
      rw [hsmallSpectrum]
      simp
  }⟩

end GaoLean

#print axioms GaoLean.isWeightedDavenportConstant_one_of_subsingleton
#print axioms GaoLean.weightedExactSpectrum_eq_singleton_of_weightedValue_eq
#print axioms GaoLean.generalWeightedStrongRecursionAt_bot
