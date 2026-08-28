import GaoLean.GAOARFinal
import GaoLean.PGGMOProvidersFromDGM

/-!
# Exact ordinary GMO boundary remaining after General DGM

This module is a bookkeeping reduction, not a proof of the remaining ordinary
GMO statements.  The signed prescribed-length, ambient structural, and
all-subgroup structural fields are supplied by the proved General DGM theorem.
Only the two ordinary GMO fields used by the frozen PR #7 assembly remain.
-/

namespace GaoLean.ConcreteGDihedral

universe u

/-- **Remaining boundary, not a proof.**  Under exactly the finite odd-prime
`p`-group and ordinary Davenport quantifiers of the frozen final statement,
the only source inputs still required are the ambient ordinary prescribed-
length theorem and the ordinary structural theorem in every subgroup. -/
def PGGaoOrdinaryRemainingInputs : Prop :=
  ∀ (p : ℕ) (A : Type u),
    [AddCommGroup A] → [Fintype A] → [Nontrivial A] →
    p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ D : ℕ, IsOrdinaryDavenportConstant A D →
      OrdinaryGMOPrescribedLengthProvider A D ∧
      (∀ (K : AddSubgroup A) [Fintype K],
        OrdinaryGMOStructuralProvider K)

/-- General DGM supplies exactly the three signed fields missing from the
ordinary boundary, yielding the existing five-field final source package. -/
theorem pgGaoStructuralRemainingInputs_of_ordinaryRemainingInputs
    (hordinary : PGGaoOrdinaryRemainingInputs.{u}) :
    PGGaoStructuralRemainingInputs.{u} := by
  intro p A _group _finite _nontrivial hp hpne hgroup D hD
  obtain ⟨hordinaryPrescribed, hordinarySubgroups⟩ :=
    hordinary p A hp hpne hgroup D hD
  have hodd : Odd (Nat.card A) :=
    odd_natCard_of_odd_prime_pgroup p A hp hpne hgroup
  obtain ⟨hweighted, hambientSigned, hsubgroupSigned⟩ :=
    GaoLean.oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction
      A hodd
  exact ⟨hordinaryPrescribed, hweighted, hambientSigned,
    hordinarySubgroups, hsubgroupSigned⟩

/-- Conditional PR #7 main statement with the signed GMO inputs removed from
the hypothesis.  This remains conditional precisely on
`PGGaoOrdinaryRemainingInputs`; it is not an unconditional final theorem. -/
theorem pgGaoV1Statement_of_ordinaryRemainingInputs
    (hordinary : PGGaoOrdinaryRemainingInputs.{u}) :
    PGGaoV1Statement.{u} :=
  pgGaoV1Statement_of_structuralRemainingInputs
    (pgGaoStructuralRemainingInputs_of_ordinaryRemainingInputs hordinary)

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.pgGaoStructuralRemainingInputs_of_ordinaryRemainingInputs
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1Statement_of_ordinaryRemainingInputs
