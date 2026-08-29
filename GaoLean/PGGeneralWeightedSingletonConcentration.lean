import GaoLean.PGGeneralWeightedAperiodicSplit
import GaoLean.PGGeneralWeightedSingletonOccurrences

/-!
# Singleton occurrences give the genuine concentration alternative

This file closes the singleton side of the aperiodic split without a
proposition-valued provider.  The retained selection is literally the finset
of labelled singleton occurrences, so repeated equal source values remain
distinct.  For the canonical difference kernel both concentration centres can
be chosen to be zero.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- If the canonical difference kernel is proper and the literal singleton
occurrence count meets its quotient threshold, those exact occurrences form a
`WeightedGMOConcentration`.  The source and every one of its weighted values
lie in the same kernel coset, with the explicit centres `alpha = beta = 0`. -/
theorem weightedGMOConcentration_of_manySingleton_differenceKernel
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A)
    (hproper : weightedDifferenceKernel W w₀ A < ⊤)
    (hmany :
      xs.length - Nat.card (A ⧸ (weightedDifferenceKernel W w₀ A)) + 2 ≤
        weightedSingletonOccurrenceCount W xs) :
    Nonempty (WeightedGMOConcentration W xs) := by
  classical
  refine ⟨{
    K := weightedDifferenceKernel W w₀ A
    strict := hproper
    alpha := 0
    beta := 0
    selected := weightedSingletonOccurrences W xs
    sourceCoset := ?_
    weightCoset := ?_
    card_lower := ?_ }⟩
  · intro i hi
    have hiK : occurrenceValue xs i ∈
        weightedDifferenceKernel W w₀ A :=
      (mem_weightedSingletonOccurrences_iff_mem_weightedDifferenceKernel
        hW hw₀ xs i).1 hi
    simpa using hiK
  · intro i hi w _hw
    have hiK : occurrenceValue xs i ∈
        weightedDifferenceKernel W w₀ A :=
      (mem_weightedSingletonOccurrences_iff_mem_weightedDifferenceKernel
        hW hw₀ xs i).1 hi
    have hwiK : w • occurrenceValue xs i ∈
        weightedDifferenceKernel W w₀ A :=
      (weightedDifferenceKernel W w₀ A).zsmul_mem hiK w
    simpa using hwiK
  · simpa [card_weightedSingletonOccurrences_eq_count] using hmany

/-- Trivial-kernel specialization.  Properness of `⊥` is stated explicitly:
it is necessary, since `WeightedGMOConcentration` itself requires a strict
subgroup and the one-element group has `⊥ = ⊤`. -/
theorem weightedGMOConcentration_of_manySingleton_kernel_eq_bot
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A)
    (hkernel : weightedDifferenceKernel W w₀ A = ⊥)
    (hbot : (⊥ : AddSubgroup A) < ⊤)
    (hmany : xs.length - Nat.card A + 2 ≤
      weightedSingletonOccurrenceCount W xs) :
    Nonempty (WeightedGMOConcentration W xs) := by
  apply weightedGMOConcentration_of_manySingleton_differenceKernel
    hW hw₀ xs
  · simpa [hkernel] using hbot
  · have hquot : Nat.card (A ⧸ (⊥ : AddSubgroup A)) = Nat.card A :=
      Nat.card_congr QuotientAddGroup.quotientBot.toEquiv
    simpa [hkernel, hquot] using hmany

/-- The existing aperiodic occurrence split, with the singleton branch turned
into the actual structural conclusion.  No nontriviality assumption on `A` is
needed: if `⊥ = ⊤`, nonemptiness of the exact spectrum already makes it all
of the one-element ambient group. -/
theorem weightedExactSpectrum_eq_univ_or_singletonConcentration
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥)
    (hkernel : weightedDifferenceKernel W w₀ A = ⊥) :
    weightedExactSpectrum W xs n = Finset.univ ∨
      Nonempty (WeightedGMOConcentration W xs) := by
  classical
  rcases weightedExactSpectrum_eq_univ_or_manySingleton_of_bottomStabilizer
      hW D hD xs n hn hlen hstab with hfull | hmany
  · exact Or.inl hfull
  · by_cases hbot : (⊥ : AddSubgroup A) < ⊤
    · exact Or.inr
        (weightedGMOConcentration_of_manySingleton_kernel_eq_bot
          hW hw₀ xs hkernel hbot hmany)
    · left
      have heq : (⊥ : AddSubgroup A) = ⊤ := by
        by_contra hne
        exact hbot (lt_top_iff_ne_top.mpr hne)
      have htopbot : (⊤ : AddSubgroup A) ≤ ⊥ := by
        rw [heq]
      have hsubsingleton : Subsingleton A := by
        constructor
        intro a b
        have ha : a ∈ (⊥ : AddSubgroup A) := htopbot (by simp)
        have hb : b ∈ (⊥ : AddSubgroup A) := htopbot (by simp)
        have ha0 : a = 0 := by simpa using ha
        have hb0 : b = 0 := by simpa using hb
        exact ha0.trans hb0.symm
      letI : Subsingleton A := hsubsingleton
      have hDpos : 1 ≤ D := weightedDavenportConstant_pos W D hD
      have hnlen : n ≤ xs.length := by omega
      obtain ⟨y, hy⟩ := weightedExactSpectrum_nonempty hW xs n hnlen
      apply Finset.eq_univ_iff_forall.mpr
      intro x
      simpa only [Subsingleton.elim x y] using hy

end GaoLean

#print axioms GaoLean.weightedGMOConcentration_of_manySingleton_differenceKernel
#print axioms GaoLean.weightedGMOConcentration_of_manySingleton_kernel_eq_bot
#print axioms GaoLean.weightedExactSpectrum_eq_univ_or_singletonConcentration
