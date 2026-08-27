import GaoLean.PGGMOSpectrum

/-!
# Ordinary specialization of the GMO source theorem

This file records the exact occurrence-labelled ordinary conclusion obtained
from Theorem 1.1 of Grynkiewicz--Marchan--Ordaz (equivalently, the joint
content needed for Corollaries 1.2 and 1.3 at the singleton weight set
`{1}`).  It then proves the adapters to the two interfaces used by the GAO
development.

`OrdinaryGMOSourceProvider` is deliberately a proposition-valued source
boundary, not an axiom and not a claimed proof of GMO.  In particular, the
target witness `beta`, the exact selected occurrences, the exact cardinality,
the equality with `n • beta`, and the full/non-full structural alternative are
all retained.  A later formalization of the DGM/setpartition proof must
construct this provider; the adapters below do not weaken that obligation.
-/

namespace GaoLean

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact ordinary output retained from the source theorem.  The selected
terms witnessing Corollary 1.2 and the structural alternative of Corollary
1.3 refer to the same source list and prescribed cardinality. -/
structure OrdinaryGMOSourceOutput (xs : List A) (n : ℕ) where
  beta : A
  selected : Selection xs
  card_selected : selected.card = n
  sum_selected :
    (∑ i ∈ selected, occurrenceValue xs i) = n • beta
  alternative :
    OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs)

/-- Forget only the structural branch, retaining the same occurrence-labelled
target witness. -/
def OrdinaryGMOSourceOutput.toTargetOutput
    {xs : List A} {n : ℕ} (h : OrdinaryGMOSourceOutput xs n) :
    OrdinaryGMOTargetOutput xs n where
  selected := h.selected
  card_selected := h.card_selected
  sum_mem_target := ⟨h.beta, h.sum_selected⟩

omit [Fintype A] in
/-- The source-output structure is exactly the conjunction of the target
conclusion and the full/non-full structural alternative.  This equivalence is
an audit guard: no mathematical conclusion is hidden in the packaging. -/
theorem nonempty_ordinaryGMOSourceOutput_iff
    (xs : List A) (n : ℕ) :
    Nonempty (OrdinaryGMOSourceOutput xs n) ↔
      Nonempty (OrdinaryGMOTargetOutput xs n) ∧
        (OrdinarySpectrumFull xs n ∨
          Nonempty (OrdinaryGMOConcentration xs)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨⟨h.toTargetOutput⟩, h.alternative⟩
  · rintro ⟨⟨h⟩, halt⟩
    obtain ⟨beta, hsum⟩ := h.sum_mem_target
    exact ⟨{
      beta := beta
      selected := h.selected
      card_selected := h.card_selected
      sum_selected := hsum
      alternative := halt
    }⟩

/-- The exact target endpoint of the ordinary source proof, before fixing a
particular certified Davenport threshold.  This is Corollary 1.2's remaining
proof obligation, not a theorem asserted by this project. -/
def OrdinaryGMOTargetSourceProvider
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n d : ℕ),
    Nat.card A ≤ n →
    OrdinaryDavenportAtMost A d →
    n + d - 1 ≤ xs.length →
    Nonempty (OrdinaryGMOTargetOutput xs n)

/-- Quantitative non-full endpoint closest to the DGM/setpartition
multiplicity argument.  It speaks about the canonical filter of labelled
occurrences in a coset, so repetitions are counted and no arbitrary subset
can hide a cardinality mismatch.  This remains a proposition-valued proof
obligation. -/
def OrdinaryGMONonfullCosetCardProvider
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n d : ℕ),
    Nat.card A ≤ n →
    OrdinaryDavenportAtMost A d →
    n + d - 1 ≤ xs.length →
    ¬ OrdinarySpectrumFull xs n →
    ∃ (K : AddSubgroup A), K < ⊤ ∧
      ∃ alpha : A,
        xs.length - Nat.card (A ⧸ K) + 2 ≤
          (occurrencesInAddCoset xs K alpha).card

/-- Source-facing ordinary GMO theorem schema.  It keeps the paper's
quantifiers `n ≥ |A|` and `|S| ≥ n + d - 1`, with an explicit proof that
`d` is an ordinary Davenport upper threshold.  This is a `Prop` awaiting the
DGM/setpartition proof, not a project axiom. -/
def OrdinaryGMOSourceProvider
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n d : ℕ),
    Nat.card A ≤ n →
    OrdinaryDavenportAtMost A d →
    n + d - 1 ≤ xs.length →
    Nonempty (OrdinaryGMOSourceOutput xs n)

/-- Project the exact target endpoint from the joint source theorem. -/
theorem ordinaryGMOTargetSourceProvider_of_source
    (hsource : OrdinaryGMOSourceProvider A) :
    OrdinaryGMOTargetSourceProvider A := by
  intro xs n d hn hD hlen
  obtain ⟨h⟩ := hsource xs n d hn hD hlen
  exact ⟨h.toTargetOutput⟩

/-- Project the canonical large-coset count from the joint source theorem.
The source concentration may name only a selected sub-finset; its source-coset
field proves that this sub-finset lies inside the canonical occurrence filter,
so the cardinality lower bound transfers without losing multiplicities. -/
theorem ordinaryGMONonfullCosetCardProvider_of_source
    (hsource : OrdinaryGMOSourceProvider A) :
    OrdinaryGMONonfullCosetCardProvider A := by
  intro xs n d hn hD hlen hnot
  obtain ⟨h⟩ := hsource xs n d hn hD hlen
  rcases h.alternative with hfull | hcon
  · exact False.elim (hnot hfull)
  · obtain ⟨hcon⟩ := hcon
    refine ⟨hcon.K, hcon.strict, hcon.alpha, ?_⟩
    apply hcon.card_lower.trans
    apply Finset.card_le_card
    intro i hi
    exact (mem_occurrencesInAddCoset_iff xs hcon.K hcon.alpha i).2
      (hcon.sourceCoset i hi)

/-- Reassemble the joint source output from the two honest mathematical
endpoints.  In the non-full case the canonical coset count is converted to
the existing occurrence-labelled concentration structure. -/
theorem ordinaryGMOSourceProvider_of_endpoints
    (htarget : OrdinaryGMOTargetSourceProvider A)
    (hcoset : OrdinaryGMONonfullCosetCardProvider A) :
    OrdinaryGMOSourceProvider A := by
  intro xs n d hn hD hlen
  have ht := htarget xs n d hn hD hlen
  have halt : OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
    by_cases hfull : OrdinarySpectrumFull xs n
    · exact Or.inl hfull
    · obtain ⟨K, hK, alpha, hcard⟩ := hcoset xs n d hn hD hlen hfull
      exact Or.inr
        (ordinaryGMOConcentration_of_coset_card xs K hK alpha hcard)
  exact (nonempty_ordinaryGMOSourceOutput_iff xs n).2 ⟨ht, halt⟩

/-- The exact target endpoint immediately gives the fixed-threshold provider
used by the low-reflection channel. -/
theorem ordinaryGMOPrescribedLengthProvider_of_targetSource
    (htarget : OrdinaryGMOTargetSourceProvider A)
    (D : ℕ) (hD : OrdinaryDavenportAtMost A D) :
    OrdinaryGMOPrescribedLengthProvider A D := by
  intro xs n hn hlen
  exact htarget xs n D hn hD hlen

/-- The quantitative non-full coset endpoint gives the structural provider;
the full branch is decided without changing any source quantifier. -/
theorem ordinaryGMOStructuralProvider_of_nonfullCosetCard
    (hcoset : OrdinaryGMONonfullCosetCardProvider A) :
    OrdinaryGMOStructuralProvider A := by
  intro xs n d hn hD hlen
  by_cases hfull : OrdinarySpectrumFull xs n
  · exact Or.inl hfull
  · obtain ⟨K, hK, alpha, hcard⟩ := hcoset xs n d hn hD hlen hfull
    exact Or.inr (ordinaryGMOConcentration_of_coset_card xs K hK alpha hcard)

/-- Corollary 1.2, in the exact interface consumed by the low-reflection
channel, follows from the source theorem at any certified Davenport
threshold. -/
theorem ordinaryGMOPrescribedLengthProvider_of_source
    (hsource : OrdinaryGMOSourceProvider A)
    (D : ℕ) (hD : OrdinaryDavenportAtMost A D) :
    OrdinaryGMOPrescribedLengthProvider A D := by
  intro xs n hn hlen
  obtain ⟨h⟩ := hsource xs n D hn hD hlen
  exact ⟨h.toTargetOutput⟩

/-- Corollary 1.3 at singleton weight support, in the exact full/non-full
interface consumed by the residual controller, follows from the same source
output. -/
theorem ordinaryGMOStructuralProvider_of_source
    (hsource : OrdinaryGMOSourceProvider A) :
    OrdinaryGMOStructuralProvider A := by
  intro xs n d hn hD hlen
  obtain ⟨h⟩ := hsource xs n d hn hD hlen
  exact h.alternative

/-- Convenient joint adapter used by the final source assembly.  Both
downstream providers are obtained from one source theorem instance; neither
is postulated separately. -/
theorem ordinaryGMOProviders_of_source
    (hsource : OrdinaryGMOSourceProvider A)
    (D : ℕ) (hD : OrdinaryDavenportAtMost A D) :
    OrdinaryGMOPrescribedLengthProvider A D ∧
      OrdinaryGMOStructuralProvider A :=
  ⟨ordinaryGMOPrescribedLengthProvider_of_source hsource D hD,
    ordinaryGMOStructuralProvider_of_source hsource⟩

end GaoLean

#print axioms GaoLean.OrdinaryGMOSourceOutput.toTargetOutput
#print axioms GaoLean.nonempty_ordinaryGMOSourceOutput_iff
#print axioms GaoLean.ordinaryGMOTargetSourceProvider_of_source
#print axioms GaoLean.ordinaryGMONonfullCosetCardProvider_of_source
#print axioms GaoLean.ordinaryGMOSourceProvider_of_endpoints
#print axioms GaoLean.ordinaryGMOPrescribedLengthProvider_of_targetSource
#print axioms GaoLean.ordinaryGMOStructuralProvider_of_nonfullCosetCard
#print axioms GaoLean.ordinaryGMOPrescribedLengthProvider_of_source
#print axioms GaoLean.ordinaryGMOStructuralProvider_of_source
#print axioms GaoLean.ordinaryGMOProviders_of_source
