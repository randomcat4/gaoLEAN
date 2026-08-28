import GaoLean.PGGMOOrdinaryComplement
import GaoLean.PGGMOPGroupFixedCarrierInduction

/-!
# The low-multiplicity ordinary structural branch

This file closes the source-faithful capped-seed branch of the ordinary GMO
structural provider.  The seed has the exact complementary cardinality
`n + d*(A)`.  Consequently a fixed-carrier `d*(A)`-spectrum, or a genuine
large replacement partition whose numerical bound reaches the ambient group,
complements to the required full `n`-spectrum.  A genuine concentration is
retained unchanged.

The trivial ambient group is handled directly.  In the nontrivial branch the
positivity of `d*(A)` is derived from the canonical Davenport value; it is not
added as a premise.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Any asserted ordinary Davenport threshold is at least the canonical one.
The conclusion is written in the canonical `d* + 1` form consumed by the
source driver. -/
theorem pGroupDStar_add_one_le_of_ordinaryDavenportAtMost
    {d : ℕ} (hD : OrdinaryDavenportAtMost A d) :
    pGroupDStar A + 1 ≤ d := by
  rw [pGroupDStar_add_one A]
  by_contra hnot
  have hdlt : d < ordinaryDavenportValue A := Nat.lt_of_not_ge hnot
  obtain ⟨ys, hysLength, hysFree⟩ :=
    (ordinaryDavenportValue_spec A).2 d hdlt
  exact hysFree (hD ys hysLength)

/-- In a subsingleton additive group every admissible exact occurrence
spectrum is full.  The selection is still chosen from genuine labelled
occurrences. -/
theorem ordinarySpectrumFull_of_subsingleton
    [Subsingleton A] (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    OrdinarySpectrumFull xs n := by
  classical
  intro y
  have hnUniv : n ≤ (Finset.univ : Selection xs).card := by
    simpa using hn
  obtain ⟨I, _hI, hIcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Selection xs)) hnUniv
  exact ⟨I, hIcard, Subsingleton.elim _ y⟩

/-- The complete low-multiplicity branch of the ordinary structural source
theorem.  No structural provider or desired conclusion is accepted as an
input: the nontrivial branch runs unconditional Theorem E through the genuine
well-founded fixed-carrier induction. -/
theorem ordinaryGMOStructuralAlternative_of_cappedSeed
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (hnA : Nat.card A ≤ n)
    (hseedCard : seed.card = n + pGroupDStar A)
    (hcap : SelectionMultiplicityAtMost xs seed (pGroupDStar A)) :
    OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  classical
  have hseedLeSource : seed.card ≤ xs.length := by
    simpa using Finset.card_le_univ seed
  have hnSeed : n ≤ seed.card := by
    rw [hseedCard]
    omega
  have hnSource : n ≤ xs.length :=
    hnSeed.trans hseedLeSource
  by_cases hsub : Subsingleton A
  · letI : Subsingleton A := hsub
    exact Or.inl (ordinarySpectrumFull_of_subsingleton xs n hnSource)
  · letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hsub
    have hrPos : 0 < pGroupDStar A := by
      have hDgt : 1 < ordinaryDavenportValue A :=
        one_lt_ordinaryDavenportValue (B := A)
      have hrecover := pGroupDStar_add_one A
      omega
    have hrSeed : pGroupDStar A ≤ seed.card := by
      rw [hseedCard]
      omega
    obtain ⟨I⟩ := exists_gmoTheoremEInput
      xs seed (pGroupDStar A) hcap hrSeed
    have hsourceWide : Nat.card A ≤ xs.length :=
      hnA.trans hnSource
    have htri := ordinaryGMOPGroupFixedCarrierStructuralTrichotomy
      A p hp hpTwo hA xs seed (pGroupDStar A) I
        hrPos le_rfl hsourceWide
    rcases htri with hfixed | hlarge | hconcentration
    · obtain ⟨F⟩ := hfixed
      exact Or.inl
        (F.ordinarySpectrumFull_complement hseedCard)
    · obtain ⟨P, hlarge⟩ := hlarge
      have hwide :
          Nat.card A ≤ seed.card - pGroupDStar A + 1 := by
        rw [hseedCard]
        omega
      exact Or.inl
        (hlarge.ordinarySpectrumFull_complement hseedCard hwide)
    · exact Or.inr hconcentration

end GaoLean

#print axioms GaoLean.pGroupDStar_add_one_le_of_ordinaryDavenportAtMost
#print axioms GaoLean.ordinarySpectrumFull_of_subsingleton
#print axioms GaoLean.ordinaryGMOStructuralAlternative_of_cappedSeed
