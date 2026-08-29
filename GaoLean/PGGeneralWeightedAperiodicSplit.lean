import GaoLean.PGGeneralWeightedCappedIncidence

/-!
# The arbitrary-target aperiodic occurrence split

This file records the DGM split at every source target `n ≥ |A|`, not only
at the cardinal target.  If the exact weighted spectrum has bottom
stabilizer, then either it is already all of `A`, or the singleton weighted
occurrences meet the literal concentration lower bound for the trivial
subgroup.  Repeated source values are counted as labelled occurrences.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- The many-nonsingleton DGM branch with the canonical spectrum stabilizer
used by the general-weight induction driver. -/
theorem weightedExactSpectrum_eq_univ_of_bottomStabilizer_of_manyNonsingleton
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n) (hnlen : n ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥)
    (hmany : Nat.card A - 1 ≤
      weightedNonsingletonOccurrenceCount W xs) :
    weightedExactSpectrum W xs n = Finset.univ := by
  classical
  have hfinStab :
      (weightedExactSpectrum W xs n).addStab = {0} := by
    ext x
    rw [← Finset.mem_coe,
      Finset.coe_addStab (weightedExactSpectrum_nonempty hW xs n hnlen)]
    change x ∈ AddAction.stabilizer A
        (weightedExactSpectrum W xs n : Set A) ↔
      x ∈ ({0} : Finset A)
    rw [← weightedSpectrumStabilizer, hstab]
    simp
  exact weightedExactSpectrum_eq_univ_of_aperiodic_of_manyNonsingleton
    hW xs n hn hnlen hfinStab hmany

/-- At every source-legal target, the aperiodic DGM argument gives the exact
Corollary 1.3 alternative for the trivial subgroup: either the spectrum is
full, or at least `|xs| - |A| + 2` labelled occurrences have singleton
weighted layers. -/
theorem weightedExactSpectrum_eq_univ_or_manySingleton_of_bottomStabilizer
    {W : Set ℤ} (hW : W.Nonempty)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs n = ⊥) :
    weightedExactSpectrum W xs n = Finset.univ ∨
      xs.length - Nat.card A + 2 ≤
        weightedSingletonOccurrenceCount W xs := by
  have hDpos : 1 ≤ D := weightedDavenportConstant_pos W D hD
  have hnlen : n ≤ xs.length := by omega
  have hsplit := weightedSingleton_add_weightedNonsingleton hW xs
  by_cases hsparse :
      weightedSingletonOccurrenceCount W xs + Nat.card A - 1 ≤ xs.length
  · left
    apply weightedExactSpectrum_eq_univ_of_bottomStabilizer_of_manyNonsingleton
      hW xs n hn hnlen hstab
    omega
  · right
    have hcardPos : 1 ≤ Nat.card A := Nat.card_pos
    omega

end GaoLean

#print axioms GaoLean.weightedExactSpectrum_eq_univ_of_bottomStabilizer_of_manyNonsingleton
#print axioms GaoLean.weightedExactSpectrum_eq_univ_or_manySingleton_of_bottomStabilizer
