import GaoLean.GAOARResidualController
import GaoLean.PGSourceAssembly
import GaoLean.PGDavenportConvolution
import GaoLean.PGOlson

/-!
# Final source-facing assembly for the 13-page PR #7 manuscript

The source is `randomcat4/gao0824` PR #7 at commit `6d4ab81`, whose main
statement is the odd abelian p-group theorem `PG-GAO-v1`.  The package below
contains the still-unformalized source-facing inputs: the cited
small-Davenport and GMO results.  Olson's formula, Proposition 3.1, ordinary
subgroup and quotient Davenport values, and their concatenation inequality
are now constructed internally.  The package contains no controller, branch
output, or desired Gao upper conclusion.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

universe u

/-- Final source-theorem boundary for one finite odd abelian kernel. -/
def PGGaoStructuralUpperInputs
    (A : Type*) [AddCommGroup A] [Fintype A] (D : ℕ) : Prop :=
  SmallDavenportProductOneFreeAtMost (Group A) D ∧
  OrdinaryGMOPrescribedLengthProvider A D ∧
  WeightedGMOPrescribedLengthProvider A ∧
  PlusMinusGMOStructuralProvider A ∧
  (∀ K : AddSubgroup A,
    QuotientSmallDavenportProductOneFreeAtMost K
      (ordinaryDavenportValue (A ⧸ K))) ∧
  (∀ (K : AddSubgroup A) [Fintype K],
    OrdinaryGMOStructuralProvider K) ∧
  (∀ (K : AddSubgroup A) [Fintype K],
    PlusMinusGMOStructuralProvider K)

set_option maxHeartbeats 1000000 in
/-- The final structural source package produces the exact upper input for
every labelled source sequence. -/
theorem pgGaoUpperInputs_of_structuralUpperInputs
    (p D : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hgroup : IsPGroup p (Multiplicative A))
    (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hD : IsOrdinaryDavenportConstant A D)
    (hsource : PGGaoStructuralUpperInputs A D) :
    PGGaoUpperInputs A D := by
  classical
  rcases hsource with
    ⟨hsmall, hordinaryPrescribed, hweighted, hambientGMO,
      hsmallQuotient, hordinaryGMO, hplusMinusGMO⟩
  have hDodd : Odd D :=
    odd_ordinaryDavenport_of_isPGroup A p D hp hpTwo hgroup hD
  have hrestricted : RestrictedCoefficientOutputAt A ((D + 1) / 2) :=
    restrictedCoefficientOutputAt_half_of_isPGroup A p D hp hpTwo hgroup hD
  let Dker : AddSubgroup A → ℕ := fun K => ordinaryDavenportValue K
  let Dquot : AddSubgroup A → ℕ := fun K =>
    ordinaryDavenportValue (A ⧸ K)
  have hDkerSpec (K : AddSubgroup A) [Fintype K] :
      IsOrdinaryDavenportConstant K (Dker K) := by
    simpa [Dker] using ordinaryDavenportValue_spec K
  have hDquotSpec (K : AddSubgroup A) :
      IsOrdinaryDavenportConstant (A ⧸ K) (Dquot K) := by
    simpa [Dquot] using ordinaryDavenportValue_spec (A ⧸ K)
  have hconvolution : ∀ K : AddSubgroup A, ⊥ < K → K < ⊤ →
      Dker K + Dquot K ≤ D + 1 := by
    intro K _ _
    exact ordinaryDavenport_subgroup_quotient K D (Dker K) (Dquot K)
      hD (hDkerSpec K) (hDquotSpec K)
  have hDquotLe : ∀ K : AddSubgroup A, Dquot K ≤ D := by
    intro K
    have hconv := ordinaryDavenport_subgroup_quotient
      K D (Dker K) (Dquot K) hD (hDkerSpec K) (hDquotSpec K)
    have hpos := ordinaryDavenportConstant_pos (Dker K) (hDkerSpec K)
    omega
  have hordinary : ∀ (K : AddSubgroup A) [Fintype K],
      ⊥ < K → K < ⊤ → OrdinaryDavenportAtMost K (Dker K) := by
    intro K _ _ _
    exact (hDkerSpec K).1
  have hplusMinus : ∀ (K : AddSubgroup A) [Fintype K],
      ⊥ < K → K < ⊤ → PlusMinusDavenportAtMost K (Dker K) := by
    intro K _ _ _
    exact plusMinusDavenportAtMost_of_ordinaryDavenportAtMost
      (hDkerSpec K).1
  have hpmAmbient : PlusMinusDavenportAtMost A ((D + 1) / 2) :=
    plusMinusDavenportAtMost_half_of_isPGroup A p D hp hpTwo hgroup hD
  intro s hlen
  let Q := Nat.card A
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hQpos : 0 < Q := Nat.card_pos
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b, Q]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
  refine ⟨?_, ?_, ?_⟩
  · intro hlow
    exact exists_lowReflectionTargetOutput_of_ordinaryGMO
      s Q D a b rfl rfl htotal hlow hordinaryPrescribed
  · intro hhigh
    exact exists_highReflectionTargetOutput_of_weightedGMO
      s Q D a b hQpos rfl hDodd rfl rfl htotal hhigh
        hrestricted hweighted
  · intro hmiddle
    have hcontroller : PGO3ControllerSkeleton QuotientNoReflection
        s Q D a b :=
      GaoLean.concretePGO3ControllerSkeleton_of_structuralGMO
        s Q D a b (by simpa [Q] using hlen) rfl rfl rfl hAodd hDQ
          hmiddle.2 htotal hsmall Dker Dquot hsmallQuotient hDquotLe
            hconvolution hordinary hplusMinus hordinaryGMO hplusMinusGMO
    have hbook := middle_target_bookkeeping hDQ hmiddle.1 hmiddle.2
    have htargetCard : Nat.card A ≤ middleRotationTarget Q a := by
      dsimp only [Q]
      exact hbook.2.2.2.2.1
    have hbEq : b = 2 * Q + D - a := by omega
    have hsurplus := middle_rotation_surplus hDQ hmiddle.1 hmiddle.2 hbEq
    have hdpmLe : (D + 1) / 2 ≤ D := by omega
    have hthreshold : middleRotationTarget Q a + (D + 1) / 2 - 1 ≤ b := by
      have htgtle : middleRotationTarget Q a ≤ b := hsurplus.1
      have hsur : D - 1 ≤ b - middleRotationTarget Q a := hsurplus.2
      omega
    have hspectrum : MiddleSpectrumAlternative s Q D a b := by
      exact middleSpectrumAlternative_of_plusMinusGMO
        s Q D a b ((D + 1) / 2) hmiddle.1 rfl rfl htargetCard
          hthreshold hpmAmbient hambientGMO
    exact ⟨hcontroller, hspectrum⟩

/-- Conditional end-to-end equality for one kernel, with the lower witness,
all three upper regimes, and simultaneous residual descent constructed
internally. -/
theorem pgGaoV1_of_structuralUpperInputs_and_ordinaryDavenport
    (p D : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hgroup : IsPGroup p (Multiplicative A))
    (hAodd : Odd (Nat.card A))
    (hsource : PGGaoStructuralUpperInputs A D)
    (hD : IsOrdinaryDavenportConstant A D) :
    PGGaoV1 A D := by
  have hDQ : D ≤ Nat.card A := ordinaryDavenportConstant_le_natCard D hD
  exact pgGaoV1_of_upperInputs_and_isOrdinaryDavenportConstant
    D hDQ hAodd
      (pgGaoUpperInputs_of_structuralUpperInputs p D hp hpTwo hgroup
        hDQ hAodd hD hsource) hD

/-- Exact remaining-input boundary under the frozen odd-prime p-group
quantifiers.  Its fields are precisely the cited small-Davenport and GMO
results not yet reconstructed in Lean. -/
def PGGaoStructuralRemainingInputs : Prop :=
  ∀ (p : ℕ) (A : Type u),
    [AddCommGroup A] → [Fintype A] → [Nontrivial A] →
    p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ D : ℕ, IsOrdinaryDavenportConstant A D →
      PGGaoStructuralUpperInputs A D

/-- Final conditional realization of the frozen manuscript statement.  Its
sole argument is the explicit collection of remaining source statements
above; this theorem must not be reported as unconditional. -/
theorem pgGaoV1Statement_of_structuralRemainingInputs
    (hremaining : PGGaoStructuralRemainingInputs.{u}) :
    PGGaoV1Statement.{u} := by
  intro p A _ _ _ hp hpne hgroup D hD
  have hsource := hremaining p A hp hpne hgroup D hD
  exact pgGaoV1_of_structuralUpperInputs_and_ordinaryDavenport
    p D hp hpne hgroup
      (odd_natCard_of_odd_prime_pgroup p A hp hpne hgroup) hsource hD

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.pgGaoUpperInputs_of_structuralUpperInputs
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_structuralUpperInputs_and_ordinaryDavenport
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1Statement_of_structuralRemainingInputs
