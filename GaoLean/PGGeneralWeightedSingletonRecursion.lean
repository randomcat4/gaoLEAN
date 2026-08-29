import GaoLean.PGGeneralWeightedSingletonOccurrences
import GaoLean.PGGeneralWeightedSubsequence
import GaoLean.PGGeneralWeightedDavenport

/-!
# Lifting singleton-kernel recursive witnesses

Weighted witnesses constructed in the difference-kernel subtype are first
mapped into the ambient group, identified with the literal occurrence
subsequence of singleton layers, and only then lifted to the original source.
Thus repeated source values remain distinct occurrences throughout.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

noncomputable local instance weightedDifferenceKernelFintype
    (W : Set ℤ) (w₀ : ℤ) :
    Fintype (weightedDifferenceKernel W w₀ A) :=
  Fintype.ofFinite _

/-- An exact weighted witness in the singleton-kernel list lifts to an exact
witness of the same cardinality and ambient value in the original source. -/
noncomputable def HasWeightedSumOfCard.liftSingletonKernelSubsequence
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    {xs : List A} {n : ℕ}
    {y : weightedDifferenceKernel W w₀ A}
    (h : HasWeightedSumOfCard W
      (weightedSingletonKernelSubsequence hW hw₀ xs) n y) :
    HasWeightedSumOfCard W xs n (y : A) := by
  classical
  let K := weightedDifferenceKernel W w₀ A
  let ks := weightedSingletonKernelSubsequence hW hw₀ xs
  let R := weightedSingletonOccurrences W xs
  have hmapped : HasWeightedSumOfCard W
      (ks.map K.subtype) n (K.subtype y) :=
    hasWeightedSumOfCard_map_addMonoidHom W K.subtype ks n y h
  have hlist : ks.map K.subtype = occurrenceSubsequence xs R := by
    dsimp only [ks, K, R]
    exact map_coe_weightedSingletonKernelSubsequence hW hw₀ xs
  have hsubsequence : HasWeightedSumOfCard W
      (occurrenceSubsequence xs R) n (y : A) := by
    rw [← hlist]
    exact hmapped
  exact hsubsequence.liftOccurrenceSubsequence

/-- The exact weighted spectrum of the kernel-valued singleton list maps
into the exact weighted spectrum of the full source. -/
theorem image_weightedExactSpectrum_singletonKernelSubsequence_subset
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) (n : ℕ) :
    (weightedExactSpectrum W
      (weightedSingletonKernelSubsequence hW hw₀ xs) n).image
        (weightedDifferenceKernel W w₀ A).subtype ⊆
      weightedExactSpectrum W xs n := by
  classical
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  rw [mem_weightedExactSpectrum_iff] at hy ⊢
  exact hy.map (HasWeightedSumOfCard.liftSingletonKernelSubsequence
    hW hw₀)

/-- If the kernel-valued singleton list has full exact spectrum, every
element of the actual difference kernel occurs as an ambient exact weighted
sum on the original labelled source. -/
theorem hasWeightedSumOfCard_of_singletonKernelSpectrum_eq_univ
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) (n : ℕ)
    (hfull : weightedExactSpectrum W
      (weightedSingletonKernelSubsequence hW hw₀ xs) n = Finset.univ) :
    ∀ y : weightedDifferenceKernel W w₀ A,
      Nonempty (HasWeightedSumOfCard W xs n (y : A)) := by
  classical
  intro y
  have hy : y ∈ weightedExactSpectrum W
      (weightedSingletonKernelSubsequence hW hw₀ xs) n := by
    rw [hfull]
    simp
  rw [mem_weightedExactSpectrum_iff] at hy
  exact hy.map (HasWeightedSumOfCard.liftSingletonKernelSubsequence
    hW hw₀)

/-- Finset form of the preceding full-kernel image certificate. -/
theorem image_univ_differenceKernel_subset_weightedExactSpectrum
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) (n : ℕ)
    (hfull : weightedExactSpectrum W
      (weightedSingletonKernelSubsequence hW hw₀ xs) n = Finset.univ) :
    (Finset.univ : Finset (weightedDifferenceKernel W w₀ A)).image
        (weightedDifferenceKernel W w₀ A).subtype ⊆
      weightedExactSpectrum W xs n := by
  classical
  rw [← hfull]
  exact image_weightedExactSpectrum_singletonKernelSubsequence_subset
    hW hw₀ xs n

end GaoLean

#print axioms GaoLean.HasWeightedSumOfCard.liftSingletonKernelSubsequence
#print axioms GaoLean.image_weightedExactSpectrum_singletonKernelSubsequence_subset
#print axioms GaoLean.hasWeightedSumOfCard_of_singletonKernelSpectrum_eq_univ
#print axioms GaoLean.image_univ_differenceKernel_subset_weightedExactSpectrum
