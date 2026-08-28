import GaoLean.PGGMOOrdinaryCanonicalPairBlock
import GaoLean.PGGMOOrdinaryStructuralDriver

/-!
# Unconditional canonical enlargement and ordinary structural provider

The honest pair-subgroup certificate is now available by strong induction.
This module feeds that certificate into the explicit labelled pair-block
assembly, eliminating the last conditional local-enlargement input from the
ordinary structural driver.

The local enlargement theorem is purely finite-additive and does not assume
that the ambient group is a p-group.  The p-group hypotheses occur only in
the source-shaped structural provider, exactly where the imported driver
uses them.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance canonicalExtensionDecidableEq {X : Type*} :
    DecidableEq X :=
  Classical.decEq X
noncomputable local instance canonicalExtensionQuotientFintype
    (H : AddSubgroup A) : Fintype (A ⧸ H) :=
  Fintype.ofFinite (A ⧸ H)

namespace CanonicalOrdinaryGMOStep1Core

/-- Every proper canonical core below the source-coset threshold strictly
enlarges.  The pair certificate is produced internally from the literal
outside quotient occurrences; it is not an input or provider. -/
theorem exists_strict_canonicalOrdinaryGMOStep1Core
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (hproper : C.H < ⊤)
    (hsmall : C.container.card <
      xs.length - Nat.card (A ⧸ C.H) + 2)
    (hlen : Nat.card A + pGroupDStar A ≤ xs.length) :
    ∃ C'' : CanonicalOrdinaryGMOStep1Core xs, C.H < C''.H := by
  letI : Nontrivial (A ⧸ C.H) :=
    C.nontrivial_outsideQuotient hproper
  have houtsideLength :
      Nat.card (A ⧸ C.H) - 1 ≤ Nat.card (↑C.outsideOccurrences) := by
    simpa [Nat.card_eq_fintype_card] using
      C.quotientCard_sub_one_le_card_outsideOccurrences hproper hsmall
  obtain ⟨P⟩ := ordinaryPairSubgroupCertificate_exists
    C.outsideQuotientValue C.outsideQuotientValue_ne_zero
      houtsideLength
  exact C.exists_strict_canonicalOrdinaryGMOStep1Core_of_pairCertificate
    P hlen

end CanonicalOrdinaryGMOStep1Core

/-- Unconditional source-shaped ordinary GMO structural provider for finite
additive p-groups.  The source length hypothesis and the supplied Davenport
threshold imply the canonical ambient budget at each invocation, after
which the proved local strict enlargement discharges the conditional driver
input. -/
theorem ordinaryGMOStructuralProvider_of_oddPrimePGroup
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A)) :
    OrdinaryGMOStructuralProvider A := by
  intro xs n d hnA hD hlen
  have hdStar : pGroupDStar A + 1 ≤ d :=
    pGroupDStar_add_one_le_of_ordinaryDavenportAtMost hD
  have hambientLength : Nat.card A + pGroupDStar A ≤ xs.length := by
    omega
  exact ordinaryGMOStructuralAlternative_of_canonicalLocalStrictEnlargement
    A p hp hpTwo hA xs n d hnA hD hlen
      (fun C hproper hsmall ↦
        C.exists_strict_canonicalOrdinaryGMOStep1Core
          hproper hsmall hambientLength)

end GaoLean

#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.exists_strict_canonicalOrdinaryGMOStep1Core
#print axioms GaoLean.ordinaryGMOStructuralProvider_of_oddPrimePGroup
