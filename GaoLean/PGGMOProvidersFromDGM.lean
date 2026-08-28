import GaoLean.PGDGMAperiodicDriver
import GaoLean.PGGMOTheorem11

/-!
# Signed GMO providers from the proved General DGM theorem

This file performs only the final mechanical specialization.  General DGM is
already proved by the double induction driver; the odd-order signed GMO
induction in `PGGMOTheorem11` accepts exactly that theorem and returns the
source-faithful Corollary 1.2/1.3 package.  No provider or target inequality is
assumed here.
-/

namespace GaoLean

universe u

/-- Canonical finite subtype instance used only to state the convenience
version whose subgroup provider does not expose an instance binder. -/
noncomputable local instance providersFromDGMSubgroupFintype
    {B : Type u} [AddCommGroup B] [Fintype B]
    (K : AddSubgroup B) : Fintype K :=
  Fintype.ofFinite K

/-- The theorem-11 wrapper's hidden classical equality decision is supplied
by the unconditional double-induction DGM theorem. -/
theorem finiteDGMSetpartitionInput_of_doubleInduction
    (B : Type u) [AddCommGroup B] [Fintype B] :
    FiniteDGMSetpartitionInput B := by
  classical
  exact generalDGMSetpartitionTheorem_of_doubleInduction B

/-- The exact occurrence-labelled signed GMO source package required by the
13-page odd-order specialization, now with its General DGM input discharged. -/
theorem plusMinusGMOSourcePackage_of_doubleInduction
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    PlusMinusGMOSourcePackage B := by
  apply plusMinusGMOSourcePackage_of_oddDGM
    (B := B) (hodd := hodd)
  intro C _group _finite
  exact finiteDGMSetpartitionInput_of_doubleInduction C

/-- Unconditional signed Corollary 1.2 provider and ambient/all-subgroup
Corollary 1.3 providers for every finite odd-order abelian group. -/
theorem oddPlusMinusGMOProviders_of_doubleInduction
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    WeightedGMOPrescribedLengthProvider B ∧
      PlusMinusGMOStructuralProvider B ∧
      (∀ K : AddSubgroup B, PlusMinusGMOStructuralProvider K) := by
  apply oddPlusMinusGMOProviders (B := B) (hodd := hodd)
  intro C _group _finite
  exact finiteDGMSetpartitionInput_of_doubleInduction C

/-- Literal signed-provider field shape consumed by `GAOARFinal`: the
subgroup provider remains polymorphic in the requested `Fintype K` instance. -/
theorem oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    WeightedGMOPrescribedLengthProvider B ∧
      PlusMinusGMOStructuralProvider B ∧
      (∀ (K : AddSubgroup B) [Fintype K],
        PlusMinusGMOStructuralProvider K) := by
  apply oddPlusMinusGMOProviders_for_finalAssembly
    (B := B) (hodd := hodd)
  intro C _group _finite
  exact finiteDGMSetpartitionInput_of_doubleInduction C

end GaoLean

#print axioms GaoLean.finiteDGMSetpartitionInput_of_doubleInduction
#print axioms GaoLean.plusMinusGMOSourcePackage_of_doubleInduction
#print axioms GaoLean.oddPlusMinusGMOProviders_of_doubleInduction
#print axioms GaoLean.oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction
