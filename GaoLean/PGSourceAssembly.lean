import GaoLean.PGDavenportBridge
import GaoLean.PGDavenportBound
import GaoLean.PGControllerClosure
import GaoLean.PGOrdinaryGMOBridge
import GaoLean.PGPGroupNumerics
import GaoLean.PGWeightedGMOBridge

/-!
# Source-level PG-GAO upper assembly

This module refines the coarse `PGGaoUpperInputs` boundary.  The residual
controller is now built from the already checked quotient extractions,
simultaneous induction, and channel consumers.  The remaining source inputs
are the exact low/high/middle spectrum outputs, the two narrow GMO providers,
and the quotient/ambient small-Davenport bounds.

All of those inputs remain proposition parameters.  No cited theorem is
introduced as an axiom and no unconditional Gao equality is asserted.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

universe u

/-- Exact external boundary for one source in the middle reflection regime.
The spectrum alternative is fixed-source.  The rotation provider is
quantified over every auxiliary source needed by `ZR`, while the reflection
provider is fixed-source as required by `RC_S`. -/
def PGMiddleExternalInputs
    (s : List (Group A)) (Q D a b : ℕ) : Prop :=
  MiddleSpectrumAlternative s Q D a b ∧
  (∀ (K : AddSubgroup A) (X : List (Group A)),
    ⊥ < K → K < ⊤ →
    X.length = 2 * Q + D →
    (reflectionOccurrences X).card = a →
    (rotationOccurrences X).card = b →
    b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
    QuotientNoReflection X K →
    RotationChannelGMOProvider X Q D a b K) ∧
  (∀ K : AddSubgroup A,
    ⊥ < K → K < ⊤ →
    b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn s K).card →
    ¬QuotientNoReflection s K →
    ReflectionChannelGMOProvider s Q D a b K)

/-- Source-faithful external upper package.  Unlike `PGGaoUpperInputs`, this
does not assume a middle controller: it supplies only the numerical bounds,
the actual ordinary/weighted GMO theorem interfaces, the restricted-
coefficient source, middle spectrum alternative, and narrow channel providers
from which both outer outputs and the controller are mechanically assembled. -/
def PGGaoExternalUpperInputs
    (A : Type*) [AddCommGroup A] [Fintype A] (D : ℕ) : Prop :=
  SmallDavenportProductOneFreeAtMost (Group A) D ∧
  Odd D ∧
  RestrictedCoefficientOutputAt A ((D + 1) / 2) ∧
  GaoLean.OrdinaryGMOPrescribedLengthProvider A D ∧
  WeightedGMOPrescribedLengthProvider A ∧
  ∃ Dquot : AddSubgroup A → ℕ,
    (∀ K : AddSubgroup A,
      QuotientSmallDavenportProductOneFreeAtMost K (Dquot K)) ∧
    (∀ K : AddSubgroup A, Dquot K ≤ D) ∧
    ∀ s : List (Group A), s.length = 2 * Nat.card A + D →
      let a := (reflectionOccurrences s).card
      let b := (rotationOccurrences s).card
      ((2 ≤ a ∧ a ≤ D) →
        PGMiddleExternalInputs s (Nat.card A) D a b)

/-- The checked controller/extraction stack converts the narrow external
provider package into the earlier top-level upper package. -/
theorem pgGaoUpperInputs_of_externalUpperInputs
    (D : ℕ) (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hexternal : PGGaoExternalUpperInputs A D) :
    PGGaoUpperInputs A D := by
  rcases hexternal with
    ⟨hsmall, hDodd, hrestricted, hordinaryGMO, hweightedGMO,
      Dquot, hsmallQuotient, hDquotLe, hsource⟩
  intro s hlen
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have htotal : a + b = 2 * Nat.card A + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
  have hmiddleInput : (2 ≤ a ∧ a ≤ D) →
      PGMiddleExternalInputs s (Nat.card A) D a b := by
    simpa only [a, b] using hsource s hlen
  refine ⟨?_, ?_, ?_⟩
  · intro hlow
    exact exists_lowReflectionTargetOutput_of_ordinaryGMO
      s (Nat.card A) D a b rfl rfl htotal hlow hordinaryGMO
  · intro hhigh
    have hQpos : 0 < Nat.card A := by
      rcases hAodd with ⟨k, hk⟩
      omega
    exact exists_highReflectionTargetOutput_of_weightedGMO
      s (Nat.card A) D a b hQpos rfl hDodd rfl rfl htotal hhigh
        hrestricted hweightedGMO
  intro hmiddle
  rcases hmiddleInput hmiddle with
    ⟨hspectrum, hrotationGMO, hreflectionGMO⟩
  refine ⟨?_, hspectrum⟩
  exact GaoLean.concretePGO3ControllerSkeleton_of_channelGMOProviders
    s (Nat.card A) D a b hlen rfl rfl rfl hAodd hDQ hmiddle.2
      htotal hsmall Dquot hsmallQuotient hDquotLe hrotationGMO
      hreflectionGMO

/-- Conditional PG-GAO closure from the narrow, source-level external upper
package and the exact lower witness.  This theorem still does not prove either
external package. -/
theorem pgGaoV1_of_externalUpperInputs_and_smallDavenportWitness
    (D : ℕ) (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hupper : PGGaoExternalUpperInputs A D)
    (hlower : SmallDavenportWitness (Group A) D) :
    PGGaoV1 A D := by
  exact pgGaoV1_of_upperInputs_and_smallDavenportWitness
    D hDQ hAodd
      (pgGaoUpperInputs_of_externalUpperInputs D hDQ hAodd hupper)
      hlower

/-- Source-level conditional PG-GAO closure directly from the frozen ordinary
Davenport premise.  Its lower witness is constructed internally; only the
refined external upper package remains. -/
theorem pgGaoV1_of_externalUpperInputs_and_isOrdinaryDavenportConstant
    (D : ℕ) (hDQ : D ≤ Nat.card A) (hAodd : Odd (Nat.card A))
    (hupper : PGGaoExternalUpperInputs A D)
    (hD : IsOrdinaryDavenportConstant A D) :
    PGGaoV1 A D := by
  exact pgGaoV1_of_upperInputs_and_isOrdinaryDavenportConstant
    D hDQ hAodd
      (pgGaoUpperInputs_of_externalUpperInputs D hDQ hAodd hupper)
      hD

/-- The odd-cardinality side condition is discharged directly from the
frozen odd-prime p-group hypotheses. -/
theorem pgGaoV1_of_externalUpperInputs_and_ordinaryDavenport_of_pgroup
    (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2)
    (hgroup : IsPGroup p (Multiplicative A))
    (D : ℕ)
    (hupper : PGGaoExternalUpperInputs A D)
    (hD : IsOrdinaryDavenportConstant A D) :
    PGGaoV1 A D := by
  exact pgGaoV1_of_externalUpperInputs_and_isOrdinaryDavenportConstant
    D (GaoLean.ordinaryDavenportConstant_le_natCard D hD)
      (GaoLean.odd_natCard_of_odd_prime_pgroup p A hp hpne hgroup)
      hupper hD

/-- Exact remaining boundary for the fully quantified frozen theorem.  The
ordinary Davenport premise supplies `D ≤ |A|` internally; the odd-prime
p-group hypotheses supply odd cardinality; and the lower construction and all
internal upper bookkeeping are not repeated here.  Only the source-level
external upper providers remain. -/
def PGGaoRemainingInputs : Prop :=
  ∀ (p : ℕ) (A : Type u),
    [AddCommGroup A] → [Fintype A] → [Nontrivial A] →
    p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ D : ℕ, IsOrdinaryDavenportConstant A D →
      PGGaoExternalUpperInputs A D

/-- Conditional closure of the exact frozen `PGGaoV1Statement` from its
remaining numerical and external-provider boundary. -/
theorem pgGaoV1Statement_of_remainingInputs
    (hremaining : PGGaoRemainingInputs.{u}) :
    PGGaoV1Statement.{u} := by
  intro p A _ _ _ hp hpne hgroup D hD
  have hupper := hremaining p A hp hpne hgroup D hD
  exact pgGaoV1_of_externalUpperInputs_and_ordinaryDavenport_of_pgroup
    p hp hpne hgroup D hupper hD

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.pgGaoUpperInputs_of_externalUpperInputs
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_externalUpperInputs_and_smallDavenportWitness
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_externalUpperInputs_and_isOrdinaryDavenportConstant
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_externalUpperInputs_and_ordinaryDavenport_of_pgroup
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1Statement_of_remainingInputs
