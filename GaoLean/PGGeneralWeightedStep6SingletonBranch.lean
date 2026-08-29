import GaoLean.PGGeneralWeightedSingletonOccurrences
import GaoLean.PGGeneralWeightedStep6Numerics
import GaoLean.PGSetpartitionOccurrences

/-!
# The many-singleton entrance to weighted GMO Step 6

This file proves the first genuine subgroup consequence of the singleton
branch.  If more than `D` weighted occurrence layers are singletons while
every source value in the difference kernel occurs at most `D - 1` times,
then that kernel cannot be trivial.  All counts are on labelled occurrences.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Every singleton weighted occurrence lies in the source-value fiber
specified by its difference-kernel value.  In particular, if the kernel is
bottom then all singleton occurrences carry source value zero. -/
theorem weightedSingletonOccurrences_subset_zeroFiber_of_kernel_eq_bot
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A)
    (hbot : weightedDifferenceKernel W w₀ A = ⊥) :
    weightedSingletonOccurrences W xs ⊆ occurrenceFiber xs 0 := by
  classical
  intro i hi
  have hmem : occurrenceValue xs i ∈
      weightedDifferenceKernel W w₀ A :=
    (mem_weightedSingletonOccurrences_iff_mem_weightedDifferenceKernel
      hW hw₀ xs i).1 hi
  rw [hbot, AddSubgroup.mem_bot] at hmem
  simp [occurrenceFiber, hmem]

/-- The literal Step 6 nontriviality test.  The multiplicity hypothesis is
needed only on values in the canonical difference kernel and counts repeated
source occurrences exactly. -/
theorem weightedDifferenceKernel_ne_bot_of_manySingleton
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (hw₀ : w₀ ∈ W)
    (xs : List A) (D : ℕ)
    (hmany : D + 1 ≤ weightedSingletonOccurrenceCount W xs)
    (hmult : ∀ x : weightedDifferenceKernel W w₀ A,
      (occurrenceFiber xs (x : A)).card ≤ D - 1) :
    weightedDifferenceKernel W w₀ A ≠ ⊥ := by
  intro hbot
  have hsubset :=
    weightedSingletonOccurrences_subset_zeroFiber_of_kernel_eq_bot
      hW hw₀ xs hbot
  have hcard : weightedSingletonOccurrenceCount W xs ≤
      (occurrenceFiber xs 0).card := by
    rw [← card_weightedSingletonOccurrences_eq_count W xs]
    exact Finset.card_le_card hsubset
  have hzeroMem : (0 : A) ∈ weightedDifferenceKernel W w₀ A :=
    (weightedDifferenceKernel W w₀ A).zero_mem
  have hzeroBound := hmult ⟨0, hzeroMem⟩
  have hzeroBound' : (occurrenceFiber xs (0 : A)).card ≤ D - 1 := by
    simpa using hzeroBound
  omega

/-- Once the difference kernel is nontrivial, the source critical length
forces the exact Step 6 dichotomy: either there are enough singleton layers
to recurse inside the kernel, or there are at least `|dA|` nonsingleton
layers to invoke Lemma 3.5 in the difference range. -/
theorem weighted_singletonKernel_or_nonsingletonRange_count
    {W : Set ℤ} (hW : W.Nonempty) {w₀ : ℤ} (_hw₀ : w₀ ∈ W)
    (xs : List A) (D : ℕ) (hDpos : 1 ≤ D)
    (hlen : Nat.card A + D - 1 ≤ xs.length)
    (hNne : weightedDifferenceKernel W w₀ A ≠ ⊥) :
    Nat.card (weightedDifferenceKernel W w₀ A) + D - 1 ≤
        weightedSingletonOccurrenceCount W xs ∨
      Nat.card (weightedDifferenceRange W w₀ A) ≤
        weightedNonsingletonOccurrenceCount W xs := by
  classical
  let N := weightedDifferenceKernel W w₀ A
  let K := weightedDifferenceRange W w₀ A
  have hsplit := weightedSingleton_add_weightedNonsingleton hW xs
  have hNtwo : 2 ≤ Nat.card N := by
    letI : Nontrivial N :=
      (AddSubgroup.nontrivial_iff_ne_bot N).2 hNne
    exact (Finite.one_lt_card_iff_nontrivial).2 inferInstance
  have hfactor := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N
  have hqK : Nat.card (A ⧸ N) = Nat.card K := by
    exact Nat.card_congr (weightedDifferenceQuotientEquivRange W w₀ A)
  rw [hqK] at hfactor
  by_cases hlarge : Nat.card N + D - 1 ≤
      weightedSingletonOccurrenceCount W xs
  · exact Or.inl hlarge
  · right
    change Nat.card K ≤ weightedNonsingletonOccurrenceCount W xs
    have hKpos : 1 ≤ Nat.card K := Nat.card_pos
    have hambient : Nat.card A = Nat.card K * Nat.card N := by
      simpa [N, K, Nat.mul_comm] using hfactor
    have hsingleUpper : weightedSingletonOccurrenceCount W xs ≤
        Nat.card N + D - 2 := by omega
    have hcritical : Nat.card A + D ≤ xs.length + 1 := by omega
    by_contra hnot
    have hnonsingleUpper : weightedNonsingletonOccurrenceCount W xs ≤
        Nat.card K - 1 := by omega
    have hsinglePlus : weightedSingletonOccurrenceCount W xs + 2 ≤
        Nat.card N + D := by omega
    have hnonsinglePlus : weightedNonsingletonOccurrenceCount W xs + 1 ≤
        Nat.card K := by omega
    have hlengthUpper : xs.length + 3 ≤
        Nat.card N + D + Nat.card K := by omega
    have hprodUpper : Nat.card K * Nat.card N + 2 ≤
        Nat.card N + Nat.card K := by omega
    have hprodLower : Nat.card N + Nat.card K - 1 ≤
        Nat.card K * Nat.card N := by
      simpa [Nat.mul_comm] using
        generalWeighted_add_sub_one_le_mul_of_pos
          (Nat.card N) (Nat.card K) (by omega) hKpos
    omega

end GaoLean

#print axioms GaoLean.weightedSingletonOccurrences_subset_zeroFiber_of_kernel_eq_bot
#print axioms GaoLean.weightedDifferenceKernel_ne_bot_of_manySingleton
#print axioms GaoLean.weighted_singletonKernel_or_nonsingletonRange_count
