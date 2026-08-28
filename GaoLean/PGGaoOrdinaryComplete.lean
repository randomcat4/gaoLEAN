import GaoLean.PGGaoOrdinaryRemaining
import GaoLean.PR7ThirteenPage
import GaoLean.PGGMOOrdinaryDGMTargetInduction
import GaoLean.PGGMOOrdinaryCanonicalExtension

/-!
# Unconditional ordinary completion of the frozen thirteen-page theorem

This module closes the two ordinary GMO fields isolated by
`PGGaoOrdinaryRemainingInputs`.  The prescribed-length field follows from the
canonical DGM target theorem and uniqueness of the exact ordinary Davenport
constant.  The structural field is inherited by every additive subgroup of an
odd-prime `p`-group and discharged by the unconditional canonical-extension
theorem.

The final endpoint has exactly the quantifiers frozen in
`PR7ThirteenPageMainStatement`; it accepts no remaining-input package or
provider hypothesis.
-/

namespace GaoLean

universe u

/-! ## Canonical DGM target to the exact prescribed-length provider -/

/-- The canonical DGM target theorem supplies the ordinary prescribed-length
provider at every exact ordinary Davenport value.  Exactness is used only to
identify `D` with the canonical value `pGroupDStar A + 1`; after that
identification the two length thresholds are arithmetically identical. -/
theorem ordinaryGMOPrescribedLengthProvider_of_canonicalDStar
    (A : Type u) [AddCommGroup A] [Fintype A]
    (D : ℕ) (hD : IsOrdinaryDavenportConstant A D) :
    OrdinaryGMOPrescribedLengthProvider A D := by
  intro xs n hnA hlen
  have hDcanonical : D = pGroupDStar A + 1 :=
    isOrdinaryDavenportConstant_unique hD (pGroupDStar_spec A)
  apply ordinaryGMOTargetOutput_nonempty_of_canonicalDStar A xs n hnA
  rw [hDcanonical] at hlen
  omega

/-! ## Subgroup structural inheritance -/

/-- Every additive subgroup of an odd-prime additive `p`-group inherits the
same `p`-group structure, so the unconditional canonical-extension endpoint
applies to it without any nontriviality or source hypothesis. -/
theorem ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (K : AddSubgroup A) [Fintype K] :
    OrdinaryGMOStructuralProvider K := by
  have hK : IsPGroup p (Multiplicative K) :=
    isPGroup_multiplicative_addSubgroup p hA K
  exact ordinaryGMOStructuralProvider_of_oddPrimePGroup
    K p hp hpTwo hK

namespace ConcreteGDihedral

/-! ## Remaining-input and thirteen-page assembly -/

/-- The exact ordinary boundary isolated by `PGGaoOrdinaryRemainingInputs` is
unconditional: DGM supplies the ambient prescribed-length field, and the
canonical-extension theorem supplies the structural field in every subgroup.
All typeclass and theorem quantifiers are the frozen ones. -/
theorem pgGaoOrdinaryRemainingInputs :
    PGGaoOrdinaryRemainingInputs.{u} := by
  intro p A _group _finite _nontrivial hp hpTwo hA D hD
  refine ⟨
    ordinaryGMOPrescribedLengthProvider_of_canonicalDStar A D hD,
    ?_⟩
  intro K _Kfinite
  exact ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup
    A p hp hpTwo hA K

/-- Unconditional realization of the exact core theorem in the thirteen-page
`gao0824` PR #7 manuscript. -/
theorem pr7ThirteenPageMain :
    PR7ThirteenPageMainStatement.{u} := by
  exact pgGaoV1Statement_of_ordinaryRemainingInputs
    pgGaoOrdinaryRemainingInputs

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ordinaryGMOPrescribedLengthProvider_of_canonicalDStar
#print axioms GaoLean.ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup
#print axioms GaoLean.ConcreteGDihedral.pgGaoOrdinaryRemainingInputs
#print axioms GaoLean.ConcreteGDihedral.pr7ThirteenPageMain
