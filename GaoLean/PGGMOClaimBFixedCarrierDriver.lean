import GaoLean.PGGMOPGroupFixedCarrierInduction

/-!
# Fixed-carrier dispatch from an existing Claim-B witness

This module isolates the Claim-B branch of the fixed-carrier structural
recursion.  Starting from one genuine occurrence-faithful Claim-B witness, it
first chooses a cardinal-maximal genuine witness for the same source data.
The top-subgroup endpoint supplies a fixed carrier directly.  At a proper
maximal subgroup, the verified low-multiplicity dispatch constructs the
canonical quotient input; the already proved structural recursion is then
run on that actual quotient input and its trichotomy is lifted back to the
parent source.

No root Theorem E run, external recursive conclusion, assumed oracle, or conversion
of a bare full spectrum into a setpartition is used here.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- An existing genuine Claim-B witness in an odd-primary group already
drives the fixed-carrier recursion: either its source has a fixed carrier
of the original seed cardinality supporting every exact-`n` target, or the
source has the verified concentration conclusion. -/
theorem OrdinaryGMOClaimBOutput.nonempty_fixedCarrierSpectrumFull_or_concentration
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hambient : pGroupDStar A ≤ n) :
    Nonempty (OrdinaryFixedCarrierSpectrumFull xs seed.card n) ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  obtain ⟨Wmax, hmax⟩ :=
    exists_card_maximal_ordinaryGMOClaimBOutput ⟨W⟩
  by_cases hKtop : Wmax.K = ⊤
  · have hrn : pGroupDStar Wmax.K ≤ n := by
      exact (Nat.le_add_right (pGroupDStar Wmax.K)
        (pGroupDStar (A ⧸ Wmax.K))).trans
          (Wmax.canonicalQuotient_budget hambient)
    exact Or.inl
      (Wmax.nonempty_fixedCarrierSpectrumFull_of_K_eq_top hrn hKtop)
  have hproper : Wmax.K < ⊤ := lt_top_iff_ne_top.mpr hKtop
  obtain ⟨R⟩ :=
    Wmax.nonempty_quotientRecursiveInput_of_card_maximal
      p hp hpTwo hA hmax hproper hambient
  obtain ⟨IQ⟩ := R.theoremEInput
  letI : Fintype (A ⧸ Wmax.K) := Fintype.ofFinite (A ⧸ Wmax.K)
  have hquotientTrichotomy : OrdinaryGMOFixedCarrierStructuralTrichotomy
      (Wmax.paddedQuotientRValues R.zeroCapacity)
      (Wmax.paddedQuotientRSeed R.zeroCapacity)
      (pGroupDStar (A ⧸ Wmax.K)) :=
    ordinaryGMOPGroupFixedCarrierStructuralTrichotomy
      (A ⧸ Wmax.K) p hp hpTwo R.quotientPGroup
      (Wmax.paddedQuotientRValues R.zeroCapacity)
      (Wmax.paddedQuotientRSeed R.zeroCapacity)
      (pGroupDStar (A ⧸ Wmax.K)) IQ R.dQPos le_rfl R.sourceWide
  exact Wmax.fixedCarrier_or_concentration_of_quotientTrichotomy
    hproper R.zeroCapacity R.liftBudget hquotientTrichotomy

#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_fixedCarrierSpectrumFull_or_concentration

end GaoLean
