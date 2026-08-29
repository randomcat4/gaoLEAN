import GaoLean.PGGeneralWeightedProviderQuotient

/-!
# Cardinal induction for the general weighted GMO theorem

This file isolates the exact well-founded recursion used by the source
theorem.  Once the aperiodic (trivial spectrum-stabilizer) branch is proved
for every finite abelian group, all nontrivial stabilizer branches follow by
recursion on the stabilizer quotient.  The quotient is supplied with its own
exact weighted Davenport constant; no ambient constant is relabelled as a
quotient constant.
-/

namespace GaoLean

universe u

/-- The prescribed-target conclusion in the sole branch not reduced by the
spectrum stabilizer quotient. -/
def GeneralWeightedGMOAperiodicExistenceStep
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (W : Set ℤ), W.Nonempty →
    ∀ (D : ℕ), IsWeightedDavenportConstant W A D →
      ∀ (xs : List A) (n : ℕ),
        Nat.card A ≤ n →
        n + D - 1 ≤ xs.length →
        weightedSpectrumStabilizer W xs n = ⊥ →
        WeightedGMOExistenceConclusion W xs n

/-- The full-or-concentrated conclusion in the sole branch not reduced by
the spectrum stabilizer quotient. -/
def GeneralWeightedGMOAperiodicStructuralStep
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (W : Set ℤ), W.Nonempty → IsPrimitiveWeightSet W →
    ∀ (D : ℕ), IsWeightedDavenportConstant W A D →
      ∀ (xs : List A) (n : ℕ),
        Nat.card A ≤ n →
        n + D - 1 ≤ xs.length →
        weightedSpectrumStabilizer W xs n = ⊥ →
        weightedExactSpectrum W xs n = Finset.univ ∨
          Nonempty (WeightedGMOConcentration W xs)

def GeneralWeightedGMOAperiodicPackage
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  GeneralWeightedGMOAperiodicExistenceStep A ∧
    GeneralWeightedGMOAperiodicStructuralStep A

/-- Quotienting by a nontrivial finite subgroup strictly lowers the ambient
cardinality. -/
theorem generalWeighted_natCard_quotient_lt_of_bot_lt
    {A : Type u} [AddCommGroup A] [Fintype A]
    (L : AddSubgroup A) (hL : ⊥ < L) :
    Nat.card (A ⧸ L) < Nat.card A := by
  have hLcard : 2 ≤ Nat.card L := by
    have hcardlt : Nat.card (⊥ : AddSubgroup A) < Nat.card L :=
      natCard_lt_of_addSubgroup_lt hL
    have hbotcard : Nat.card (⊥ : AddSubgroup A) = 1 := by simp
    rw [hbotcard] at hcardlt
    omega
  have hqpos : 0 < Nat.card (A ⧸ L) := Nat.card_pos
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L
  nlinarith

/-- Strong induction on the cardinality of arbitrary finite abelian groups.
The top stabilizer gives the full spectrum immediately, a nontrivial proper
stabilizer recurses on the quotient, and only the bottom stabilizer is handed
to `haperiodic`. -/
theorem generalWeightedGMOSourcePackage_of_aperiodicPackages
    (haperiodic : ∀ (C : Type u) [AddCommGroup C] [Fintype C],
      GeneralWeightedGMOAperiodicPackage C)
    (A : Type u) [AddCommGroup A] [Fintype A] :
    GeneralWeightedGMOSourcePackage A := by
  have outer : ∀ m : ℕ,
      ∀ (C : Type u) [AddCommGroup C] [Fintype C],
        Nat.card C = m → GeneralWeightedGMOSourcePackage C := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro C instGroup instFintype hcardC
        classical
        constructor
        · intro W hW D hD xs n hn hlen
          let L : AddSubgroup C := weightedSpectrumStabilizer W xs n
          letI : Fintype (C ⧸ L) := Fintype.ofFinite (C ⧸ L)
          have hDpos : 0 < D := weightedDavenportConstant_pos W D hD
          have hnlen : n ≤ xs.length := by omega
          by_cases htop : L = ⊤
          · have hfull : weightedExactSpectrum W xs n = Finset.univ :=
              weightedExactSpectrum_eq_univ_of_stabilizer_eq_top
                hW xs n hnlen (by simpa [L] using htop)
            refine ⟨0,
              (mem_weightedExactSpectrum_iff W xs n
                (n • (0 : C))).1 ?_⟩
            rw [hfull]
            simp
          · by_cases hbot : L = ⊥
            · exact (haperiodic C).1 W hW D hD xs n hn hlen
                (by simpa [L] using hbot)
            · have hLpos : ⊥ < L := bot_lt_iff_ne_bot.mpr hbot
              have hqcardlt : Nat.card (C ⧸ L) < m := by
                rw [← hcardC]
                exact generalWeighted_natCard_quotient_lt_of_bot_lt L hLpos
              have hpackageQ : GeneralWeightedGMOSourcePackage (C ⧸ L) :=
                ih (Nat.card (C ⧸ L)) hqcardlt (C ⧸ L) rfl
              exact weightedGMOExistenceConclusion_of_stabilizerQuotientProvider
                hW D hD xs n hn hlen L rfl hpackageQ.1
        · intro W hW hprimitive D hD xs n hn hlen
          let L : AddSubgroup C := weightedSpectrumStabilizer W xs n
          letI : Fintype (C ⧸ L) := Fintype.ofFinite (C ⧸ L)
          have hDpos : 0 < D := weightedDavenportConstant_pos W D hD
          have hnlen : n ≤ xs.length := by omega
          by_cases htop : L = ⊤
          · exact Or.inl
              (weightedExactSpectrum_eq_univ_of_stabilizer_eq_top
                hW xs n hnlen (by simpa [L] using htop))
          · by_cases hbot : L = ⊥
            · exact (haperiodic C).2 W hW hprimitive D hD xs n hn hlen
                (by simpa [L] using hbot)
            · have hLpos : ⊥ < L := bot_lt_iff_ne_bot.mpr hbot
              have hqcardlt : Nat.card (C ⧸ L) < m := by
                rw [← hcardC]
                exact generalWeighted_natCard_quotient_lt_of_bot_lt L hLpos
              have hpackageQ : GeneralWeightedGMOSourcePackage (C ⧸ L) :=
                ih (Nat.card (C ⧸ L)) hqcardlt (C ⧸ L) rfl
              exact weightedGMOStructuralConclusion_of_stabilizerQuotientProvider
                hW hprimitive D hD xs n hn hlen L rfl hpackageQ.2
  exact outer (Nat.card A) A rfl

end GaoLean

#print axioms GaoLean.generalWeighted_natCard_quotient_lt_of_bot_lt
#print axioms GaoLean.generalWeightedGMOSourcePackage_of_aperiodicPackages
