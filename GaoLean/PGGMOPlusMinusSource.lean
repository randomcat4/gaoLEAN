import GaoLean.PGGMOSpectrum

/-!
# Source-facing `{+1,-1}` GMO corollaries

This file freezes the exact occurrence-labelled specializations of
Grynkiewicz--Marchan--Ordaz, Corollaries 1.2 and 1.3, at the weight set
`{+1,-1}`.  The declarations ending in `Source` are proposition-valued
source boundaries, not axioms and not proofs of the cited corollaries.

The conversion theorems below prove that these source statements are neither
weaker nor stronger than the two manuscript-facing provider interfaces:

* Corollary 1.2 selects exactly `n` distinct source occurrences, partitioned
  into disjoint positive and negative parts, with signed sum in `n • A`;
* Corollary 1.3 gives either the entire exact-`n` signed spectrum or a proper
  subgroup together with one source coset and a common coset containing both
  signed weights of every retained occurrence.

Thus the only unproved content left at this layer is the substantive published
GMO theorem itself (and ultimately its DGM/setpartition proof), kept visible as
an explicit proposition argument.
-/

namespace GaoLean

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact occurrence-level conclusion of GMO Corollary 1.2 specialized to
weights `{+1,-1}`.  The witness `z` states that the signed sum lies in the
set `n • A = {n • z | z ∈ A}`. -/
def PlusMinusGMOCorollary12At (xs : List A) (n : ℕ) : Prop :=
  ∃ z : A, Nonempty (HasPlusMinusSumOfCard xs n (n • z))

/-- Uniform source statement for GMO Corollary 1.2 at `{+1,-1}`.  The input
`PlusMinusDavenportAtMost A d` permits any certified upper bound `d` for the
weighted Davenport constant. -/
def PlusMinusGMOCorollary12Source
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n d : ℕ),
    Nat.card A ≤ n →
    PlusMinusDavenportAtMost A d →
    n + d - 1 ≤ xs.length →
    PlusMinusGMOCorollary12At xs n

/-- Raw concentration branch of GMO Corollary 1.3 at `{+1,-1}`.  Membership
in `occurrencesInPlusMinusGMOCosets` simultaneously asserts

* `x ∈ alpha + K` for the source occurrence,
* `x ∈ beta + K` for its positive weight, and
* `-x ∈ beta + K` for its negative weight.

The cardinality is consequently an occurrence count and does not collapse
repeated source values. -/
structure PlusMinusGMOCorollary13Concentration (xs : List A) where
  K : AddSubgroup A
  strict : K < ⊤
  alpha : A
  beta : A
  card_lower :
    xs.length - Nat.card (A ⧸ K) + 2 ≤
      (occurrencesInPlusMinusGMOCosets xs K alpha beta).card

/-- Exact source-level full/concentrated alternative of GMO Corollary 1.3.
The full branch is stated as literal equality of the finite exact-`n` signed
spectrum with the ambient universe. -/
def PlusMinusGMOCorollary13At (xs : List A) (n : ℕ) : Prop :=
  plusMinusExactSpectrum xs n = Finset.univ ∨
    Nonempty (PlusMinusGMOCorollary13Concentration xs)

/-- Uniform source statement for GMO Corollary 1.3 specialized to
`{+1,-1}` (whose integer gcd is one). -/
def PlusMinusGMOCorollary13Source
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n d : ℕ),
    Nat.card A ≤ n →
    PlusMinusDavenportAtMost A d →
    n + d - 1 ≤ xs.length →
    PlusMinusGMOCorollary13At xs n

/-- The two exact source corollaries needed by the signed channels of the
13-page manuscript. -/
def PlusMinusGMOSourcePackage
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  PlusMinusGMOCorollary12Source A ∧ PlusMinusGMOCorollary13Source A

/-- Corollary 1.2's exact occurrence witness gives the existing prescribed
length weighted-GMO provider without any selection or cardinality weakening. -/
theorem weightedGMOPrescribedLengthProvider_of_corollary12Source
    (hsource : PlusMinusGMOCorollary12Source A) :
    WeightedGMOPrescribedLengthProvider A := by
  intro xs n d hn hd hlen
  obtain ⟨z, ⟨h⟩⟩ := hsource xs n d hn hd hlen
  exact ⟨{
    positive := h.positive
    negative := h.negative
    disjoint := h.disjoint
    card_selected := h.card_selected
    weightedSum_mem_target := ⟨z, h.weighted_sum⟩
  }⟩

/-- Conversely, the existing prescribed-length provider contains exactly the
Corollary 1.2 source witness, including disjoint signs and exact cardinality. -/
theorem corollary12Source_of_weightedGMOPrescribedLengthProvider
    (hprovider : WeightedGMOPrescribedLengthProvider A) :
    PlusMinusGMOCorollary12Source A := by
  intro xs n d hn hd hlen
  obtain ⟨h⟩ := hprovider xs n d hn hd hlen
  obtain ⟨z, hz⟩ := h.weightedSum_mem_target
  exact ⟨z, ⟨{
    positive := h.positive
    negative := h.negative
    disjoint := h.disjoint
    card_selected := h.card_selected
    weighted_sum := hz
  }⟩⟩

theorem corollary12Source_iff_weightedGMOPrescribedLengthProvider :
    PlusMinusGMOCorollary12Source A ↔
      WeightedGMOPrescribedLengthProvider A :=
  ⟨weightedGMOPrescribedLengthProvider_of_corollary12Source,
    corollary12Source_of_weightedGMOPrescribedLengthProvider⟩

/-- The raw Corollary 1.3 concentration data produces the manuscript record by
selecting every source occurrence which satisfies all three source/weight
coset conditions. -/
theorem plusMinusGMOConcentration_of_corollary13Concentration
    {xs : List A} (h : PlusMinusGMOCorollary13Concentration xs) :
    Nonempty (PlusMinusGMOConcentration xs) :=
  plusMinusGMOConcentration_of_coset_card
    xs h.K h.strict h.alpha h.beta h.card_lower

/-- Every manuscript concentration record recovers the literal Corollary 1.3
cardinality bound for the simultaneous three-coset filter.  This direction
checks that the record has not hidden a weaker, occurrence-dependent choice of
cosets. -/
theorem corollary13Concentration_of_plusMinusGMOConcentration
    {xs : List A} (h : PlusMinusGMOConcentration xs) :
    Nonempty (PlusMinusGMOCorollary13Concentration xs) := by
  classical
  refine ⟨{
    K := h.K
    strict := h.strict
    alpha := h.alpha
    beta := h.beta
    card_lower := ?_
  }⟩
  have hsubset : h.selected ⊆
      occurrencesInPlusMinusGMOCosets xs h.K h.alpha h.beta := by
    intro i hi
    exact (mem_occurrencesInPlusMinusGMOCosets_iff
      xs h.K h.alpha h.beta i).2
        ⟨h.sourceCoset i hi, h.positiveWeightCoset i hi,
          h.negativeWeightCoset i hi⟩
  exact h.card_lower.trans (Finset.card_le_card hsubset)

theorem corollary13Concentration_iff_plusMinusGMOConcentration
    (xs : List A) :
    Nonempty (PlusMinusGMOCorollary13Concentration xs) ↔
      Nonempty (PlusMinusGMOConcentration xs) := by
  constructor
  · rintro ⟨h⟩
    exact plusMinusGMOConcentration_of_corollary13Concentration h
  · rintro ⟨h⟩
    exact corollary13Concentration_of_plusMinusGMOConcentration h

/-- Corollary 1.3's finite-spectrum/coset statement gives the exact signed
structural provider consumed by the manuscript. -/
theorem plusMinusGMOStructuralProvider_of_corollary13Source
    (hsource : PlusMinusGMOCorollary13Source A) :
    PlusMinusGMOStructuralProvider A := by
  intro xs n d hn hd hlen
  rcases hsource xs n d hn hd hlen with hfull | hconcentrated
  · exact Or.inl
      ((plusMinusSpectrumFull_iff_exactSpectrum_eq_univ xs n).2 hfull)
  · obtain ⟨h⟩ := hconcentrated
    exact Or.inr
      (plusMinusGMOConcentration_of_corollary13Concentration h)

/-- Conversely, the project concentration record implies the literal source
coset count: its selected occurrences form a subset of the simultaneous
source/positive-weight/negative-weight filter. -/
theorem corollary13Source_of_plusMinusGMOStructuralProvider
    (hprovider : PlusMinusGMOStructuralProvider A) :
    PlusMinusGMOCorollary13Source A := by
  classical
  intro xs n d hn hd hlen
  rcases hprovider xs n d hn hd hlen with hfull | hconcentrated
  · exact Or.inl
      ((plusMinusSpectrumFull_iff_exactSpectrum_eq_univ xs n).1 hfull)
  · obtain ⟨h⟩ := hconcentrated
    exact Or.inr
      (corollary13Concentration_of_plusMinusGMOConcentration h)

theorem corollary13Source_iff_plusMinusGMOStructuralProvider :
    PlusMinusGMOCorollary13Source A ↔ PlusMinusGMOStructuralProvider A :=
  ⟨plusMinusGMOStructuralProvider_of_corollary13Source,
    corollary13Source_of_plusMinusGMOStructuralProvider⟩

/-- Exact audit theorem for the source boundary used in the final assembly:
the source package is logically equivalent to the pair of visible signed GMO
providers.  This theorem is a translation certificate, not a proof that either
side is inhabited. -/
theorem plusMinusGMOSourcePackage_iff_providers :
    PlusMinusGMOSourcePackage A ↔
      WeightedGMOPrescribedLengthProvider A ∧
        PlusMinusGMOStructuralProvider A := by
  constructor
  · rintro ⟨h12, h13⟩
    exact ⟨
      weightedGMOPrescribedLengthProvider_of_corollary12Source h12,
      plusMinusGMOStructuralProvider_of_corollary13Source h13⟩
  · rintro ⟨hweighted, hstructural⟩
    exact ⟨
      corollary12Source_of_weightedGMOPrescribedLengthProvider hweighted,
      corollary13Source_of_plusMinusGMOStructuralProvider hstructural⟩

end GaoLean

#print axioms GaoLean.weightedGMOPrescribedLengthProvider_of_corollary12Source
#print axioms GaoLean.corollary12Source_of_weightedGMOPrescribedLengthProvider
#print axioms GaoLean.plusMinusGMOConcentration_of_corollary13Concentration
#print axioms GaoLean.corollary13Concentration_of_plusMinusGMOConcentration
#print axioms GaoLean.plusMinusGMOStructuralProvider_of_corollary13Source
#print axioms GaoLean.corollary13Source_of_plusMinusGMOStructuralProvider
#print axioms GaoLean.plusMinusGMOSourcePackage_iff_providers
