import GaoLean.GAOARFinal
import GaoLean.PGGMOOrdinarySource
import GaoLean.PGGMOPlusMinusSource

/-!
# Assembly of the exact GMO source obligations

This module replaces the five consumer-facing provider fields by the three
literal source theorem families from Grynkiewicz--Marchan--Ordaz.  It is an
adapter only: the source obligations remain explicit propositions until the
DGM/setpartition proof constructs them.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact GMO source obligations needed for one ambient group and all of its
subgroups.  Corollary 1.2 is needed only ambiently; both ordinary and signed
Corollary 1.3 are needed uniformly on subgroups. -/
def PGGaoGMOSourceInputs
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  OrdinaryGMOSourceProvider A ∧
  PlusMinusGMOSourcePackage A ∧
  (∀ (K : AddSubgroup A) [Fintype K], OrdinaryGMOSourceProvider K) ∧
  (∀ (K : AddSubgroup A) [Fintype K], PlusMinusGMOCorollary13Source K)

/-- The exact source theorem families give precisely the five visible GMO
providers in `PGGaoStructuralUpperInputs`. -/
theorem pgGaoStructuralUpperInputs_of_gmoSourceInputs
    (D : ℕ) (hD : OrdinaryDavenportAtMost A D)
    (hsource : PGGaoGMOSourceInputs A) :
    PGGaoStructuralUpperInputs A D := by
  rcases hsource with ⟨hordinary, ⟨hsigned12, hsigned13⟩,
    hordinarySubgroups, hsignedSubgroups⟩
  refine ⟨
    ordinaryGMOPrescribedLengthProvider_of_source hordinary D hD,
    weightedGMOPrescribedLengthProvider_of_corollary12Source hsigned12,
    plusMinusGMOStructuralProvider_of_corollary13Source hsigned13,
    ?_, ?_⟩
  · intro K _
    exact ordinaryGMOStructuralProvider_of_source (hordinarySubgroups K)
  · intro K _
    exact plusMinusGMOStructuralProvider_of_corollary13Source
      (hsignedSubgroups K)

/-- End-to-end manuscript theorem with the source-facing GMO obligations and
the ordinary Davenport characterization kept explicit. -/
theorem pgGaoV1_of_gmoSourceInputs_and_ordinaryDavenport
    (p D : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hgroup : IsPGroup p (Multiplicative A))
    (hAodd : Odd (Nat.card A))
    (hsource : PGGaoGMOSourceInputs A)
    (hD : IsOrdinaryDavenportConstant A D) :
    PGGaoV1 A D := by
  exact pgGaoV1_of_structuralUpperInputs_and_ordinaryDavenport
    p D hp hpTwo hgroup hAodd
      (pgGaoStructuralUpperInputs_of_gmoSourceInputs D hD.1 hsource) hD

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.pgGaoStructuralUpperInputs_of_gmoSourceInputs
#print axioms GaoLean.ConcreteGDihedral.pgGaoV1_of_gmoSourceInputs_and_ordinaryDavenport
