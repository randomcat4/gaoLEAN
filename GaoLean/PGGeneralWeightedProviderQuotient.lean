import GaoLean.PGGeneralWeightedDavenportMinimum
import GaoLean.PGGeneralWeightedExistenceQuotient
import GaoLean.PGGeneralWeightedConcentrationQuotient

/-!
# Applying general weighted GMO providers on a stabilizer quotient

The source providers require the *exact* weighted Davenport constant of their
ambient group.  Thus the quotient branch cannot merely reuse the ambient
constant as a label: it chooses the canonical exact quotient constant, proves
that it is no larger than the ambient one, applies the quotient provider, and
then lifts the resulting conclusion through the spectrum stabilizer.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Apply a general weighted existence provider on the stabilizer quotient,
using the quotient's canonical exact weighted Davenport constant, and lift the
prescribed target back to the ambient group. -/
theorem weightedGMOExistenceConclusion_of_stabilizerQuotientProvider
    {W : Set ℤ} (hW : W.Nonempty)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (L : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (hL : L = weightedSpectrumStabilizer W xs n)
    (hproviderQ : GeneralWeightedGMOExistenceProvider (A ⧸ L)) :
    WeightedGMOExistenceConclusion W xs n := by
  classical
  let DQ : ℕ := weightedDavenportValue W (A ⧸ L) hW
  have hDQexact : IsWeightedDavenportConstant W (A ⧸ L) DQ := by
    simpa [DQ] using weightedDavenportValue_spec W (A ⧸ L) hW
  have hQDupper : WeightedDavenportAtMost W (A ⧸ L) D :=
    weightedDavenportAtMost_quotient W L D hD.1
  have hDQle : DQ ≤ D :=
    weightedDavenportConstant_le_of_atMost W (A ⧸ L) hDQexact hQDupper
  have hDpos : 0 < D := weightedDavenportConstant_pos W D hD
  have hnlen : n ≤ xs.length := by omega
  have hQcard : Nat.card (A ⧸ L) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos L.card_quotient_dvd_card
  have hQn : Nat.card (A ⧸ L) ≤ n := hQcard.trans hn
  have hQlen : n + DQ - 1 ≤
      (xs.map (QuotientAddGroup.mk' L)).length := by
    simp only [List.length_map]
    omega
  have hQ : WeightedGMOExistenceConclusion W
      (xs.map (QuotientAddGroup.mk' L)) n :=
    hproviderQ W hW DQ hDQexact
      (xs.map (QuotientAddGroup.mk' L)) n hQn hQlen
  exact weightedGMOExistenceConclusion_of_stabilizerQuotient
    hW xs n hnlen L hL hQ

/-- Apply a general weighted structural provider on the stabilizer quotient,
using the quotient's canonical exact weighted Davenport constant, and lift
either quotient fullness or quotient concentration back to the ambient group.
-/
theorem weightedGMOStructuralConclusion_of_stabilizerQuotientProvider
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (L : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (hL : L = weightedSpectrumStabilizer W xs n)
    (hproviderQ : GeneralWeightedGMOStructuralProvider (A ⧸ L)) :
    weightedExactSpectrum W xs n = Finset.univ ∨
      Nonempty (WeightedGMOConcentration W xs) := by
  classical
  let DQ : ℕ := weightedDavenportValue W (A ⧸ L) hW
  have hDQexact : IsWeightedDavenportConstant W (A ⧸ L) DQ := by
    simpa [DQ] using weightedDavenportValue_spec W (A ⧸ L) hW
  have hQDupper : WeightedDavenportAtMost W (A ⧸ L) D :=
    weightedDavenportAtMost_quotient W L D hD.1
  have hDQle : DQ ≤ D :=
    weightedDavenportConstant_le_of_atMost W (A ⧸ L) hDQexact hQDupper
  have hDpos : 0 < D := weightedDavenportConstant_pos W D hD
  have hnlen : n ≤ xs.length := by omega
  have hQcard : Nat.card (A ⧸ L) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos L.card_quotient_dvd_card
  have hQn : Nat.card (A ⧸ L) ≤ n := hQcard.trans hn
  have hQlen : n + DQ - 1 ≤
      (xs.map (QuotientAddGroup.mk' L)).length := by
    simp only [List.length_map]
    omega
  have hQ : weightedExactSpectrum W
        (xs.map (QuotientAddGroup.mk' L)) n = Finset.univ ∨
      Nonempty (WeightedGMOConcentration W
        (xs.map (QuotientAddGroup.mk' L))) :=
    hproviderQ W hW hprimitive DQ hDQexact
      (xs.map (QuotientAddGroup.mk' L)) n hQn hQlen
  exact weightedGMOStructuralConclusion_of_stabilizerQuotient
    hW xs n hnlen L hL hQ

/-- Combined stabilizer-quotient branch obtained from the exact source package
on the quotient.  The primitive-weight hypothesis is needed only by the
structural conjunct; the existence conjunct is proved without using it. -/
theorem generalWeightedGMOConclusions_of_stabilizerQuotientPackage
    {W : Set ℤ} (hW : W.Nonempty) (hprimitive : IsPrimitiveWeightSet W)
    (D : ℕ) (hD : IsWeightedDavenportConstant W A D)
    (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n)
    (hlen : n + D - 1 ≤ xs.length)
    (L : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (hL : L = weightedSpectrumStabilizer W xs n)
    (hpackageQ : GeneralWeightedGMOSourcePackage (A ⧸ L)) :
    WeightedGMOExistenceConclusion W xs n ∧
      (weightedExactSpectrum W xs n = Finset.univ ∨
        Nonempty (WeightedGMOConcentration W xs)) := by
  exact ⟨
    weightedGMOExistenceConclusion_of_stabilizerQuotientProvider
      hW D hD xs n hn hlen L hL hpackageQ.1,
    weightedGMOStructuralConclusion_of_stabilizerQuotientProvider
      hW hprimitive D hD xs n hn hlen L hL hpackageQ.2
  ⟩

end GaoLean

#print axioms GaoLean.weightedGMOExistenceConclusion_of_stabilizerQuotientProvider
#print axioms GaoLean.weightedGMOStructuralConclusion_of_stabilizerQuotientProvider
#print axioms GaoLean.generalWeightedGMOConclusions_of_stabilizerQuotientPackage
