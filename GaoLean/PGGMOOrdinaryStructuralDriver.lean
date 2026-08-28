import GaoLean.PGGMOOrdinaryStructuralLow
import GaoLean.PGGMOOrdinaryCanonicalMaximal

/-!
# Conditional ordinary structural driver

This module assembles the verified low-multiplicity branch and the canonical
Step 1 bookkeeping branch.  It is intentionally conditional: the local
strict-enlargement function is the one remaining Step 1.2 proof obligation.
Consequently, neither theorem in this file counts as an unconditional
completion of the ordinary structural theorem.

The source preprocessing remains occurrence-faithful.  It chooses an exact
capped seed of size `n + d*(A)`, or returns a concrete overfull value fiber.
The first branch uses the proved fixed-carrier structural induction; the
second constructs the canonical `H = bot` core and invokes the conditional
finite maximality scheduler.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Conditional single-source structural driver.

The argument `hExt` is exactly the missing canonical local strict
enlargement theorem.  All remaining steps, including the Davenport
arithmetic, exact capped-seed dichotomy, low-multiplicity branch, canonical
bot core, and finite maximality scheduler, are proved in the imported
modules. -/
theorem ordinaryGMOStructuralAlternative_of_canonicalLocalStrictEnlargement
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (xs : List A) (n d : ℕ)
    (hnA : Nat.card A ≤ n)
    (hD : OrdinaryDavenportAtMost A d)
    (hlen : n + d - 1 ≤ xs.length)
    (hExt :
      ∀ C : CanonicalOrdinaryGMOStep1Core xs,
        C.H < ⊤ →
        C.container.card <
          xs.length - Nat.card (A ⧸ C.H) + 2 →
        ∃ C'' : CanonicalOrdinaryGMOStep1Core xs, C.H < C''.H) :
    OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  let r := pGroupDStar A
  let m := n + r
  have hrD : r + 1 ≤ d := by
    dsimp only [r]
    exact pGroupDStar_add_one_le_of_ordinaryDavenportAtMost hD
  have hmSource : m ≤ xs.length := by
    dsimp only [m, r]
    omega
  rcases exists_capped_seed_or_excess_occurrenceFiber
      xs r m hmSource with hseed | hexcess
  · obtain ⟨seed, _hseedUniv, hseedCard, hcap⟩ := hseed
    apply ordinaryGMOStructuralAlternative_of_cappedSeed
      A p hp hpTwo hA xs seed n hnA
    · simpa [m, r] using hseedCard
    · simpa [r] using hcap
  · obtain ⟨_hsmall, a, haExcess⟩ := hexcess
    obtain ⟨C⟩ :=
      canonicalOrdinaryGMOStep1Core_bot_of_excess_occurrenceFiber
        xs a (by simpa [r] using haExcess)
    exact ordinaryStructuralAlternative_of_canonicalLocalStrictEnlargement
      n ⟨C⟩ hnA (by simpa [m, r] using hmSource) hExt

/-- Conditional wrapper with the exact quantifier shape of
`OrdinaryGMOStructuralProvider A`.

This theorem does not prove the provider unconditionally.  Its explicit
`hExt` argument is the unique remaining canonical Step 1.2 gap, uniformly
for every labelled source.  No provider, extension witness, or desired
conclusion is hidden in a structure or introduced as an axiom. -/
theorem ordinaryGMOStructuralProvider_of_canonicalLocalStrictEnlargement
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hExt :
      ∀ (xs : List A) (C : CanonicalOrdinaryGMOStep1Core xs),
        C.H < ⊤ →
        C.container.card <
          xs.length - Nat.card (A ⧸ C.H) + 2 →
        ∃ C'' : CanonicalOrdinaryGMOStep1Core xs, C.H < C''.H) :
    OrdinaryGMOStructuralProvider A := by
  intro xs n d hnA hD hlen
  exact ordinaryGMOStructuralAlternative_of_canonicalLocalStrictEnlargement
    A p hp hpTwo hA xs n d hnA hD hlen (hExt xs)

end GaoLean

#print axioms GaoLean.ordinaryGMOStructuralAlternative_of_canonicalLocalStrictEnlargement
#print axioms GaoLean.ordinaryGMOStructuralProvider_of_canonicalLocalStrictEnlargement
