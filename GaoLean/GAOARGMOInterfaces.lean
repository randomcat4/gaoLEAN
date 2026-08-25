import GaoLean.GAOARStatements
import GaoLean.PGFrontend
import GaoLean.PGOrdinaryGMOBridge
import GaoLean.PGWeightedGMOTransport

/-!
# Exact GMO interfaces used by the GAO-AR manuscript

The declarations in this file are proposition-valued provider interfaces,
not axioms and not proofs of the cited literature.  The structural interface
is the occurrence-labelled specialization of GMO Corollary 1.3 to weights
`{+1,-1}`.  In particular, its non-full branch retains both source-coset and
weight-coset conclusions instead of assuming the later subspace consequence.
-/

namespace GaoLean

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- An exact-cardinality occurrence-labelled signed sum. -/
structure HasPlusMinusSumOfCard (xs : List A) (n : ℕ) (y : A) : Prop where
  positive : Selection xs
  negative : Selection xs
  disjoint : Disjoint positive negative
  card_selected : positive.card + negative.card = n
  weighted_sum :
    (∑ i ∈ positive, occurrenceValue xs i) -
      (∑ i ∈ negative, occurrenceValue xs i) = y

/-- Every group element is represented by an exact `n`-occurrence signed
subsum of `xs`. -/
def PlusMinusSpectrumFull (xs : List A) (n : ℕ) : Prop :=
  ∀ y : A, HasPlusMinusSumOfCard xs n y

/-- The complete non-full conclusion of GMO Corollary 1.3 specialized to
weights `{+1,-1}`.  `sourceCoset` records `supp(S') ⊆ α+K`; the two
`weightCoset` fields record `{x,-x} ⊆ β+K` for every retained occurrence.
The cardinality bound counts occurrences, including repeated values. -/
structure PlusMinusGMOConcentration (xs : List A) : Prop where
  K : AddSubgroup A
  strict : K < ⊤
  alpha : A
  beta : A
  selected : Selection xs
  sourceCoset : ∀ i ∈ selected, occurrenceValue xs i - alpha ∈ K
  positiveWeightCoset :
    ∀ i ∈ selected, occurrenceValue xs i - beta ∈ K
  negativeWeightCoset :
    ∀ i ∈ selected, -occurrenceValue xs i - beta ∈ K
  card_lower :
    xs.length - Nat.card (A ⧸ K) + 2 ≤ selected.card

/-- Source-shaped external interface for GMO Corollary 1.3 at weights
`{+1,-1}`.  The `PlusMinusDavenportAtMost A d` input makes the literature's
`D_A(A)` threshold explicit; no value of that constant is asserted here. -/
def PlusMinusGMOStructuralProvider
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n d : ℕ),
    Nat.card A ≤ n →
    PlusMinusDavenportAtMost A d →
    n + d - 1 ≤ xs.length →
    PlusMinusSpectrumFull xs n ∨
      Nonempty (PlusMinusGMOConcentration xs)

/-- Checked specialization used after the weighted-coset output: if the
quotient has odd order, every occurrence in the concentrated source actually
lies in `K`.  This is a derived bridge, not part of the external interface. -/
theorem PlusMinusGMOConcentration.value_mem_subgroup
    (h : PlusMinusGMOConcentration xs)
    (hodd : Odd (Nat.card (A ⧸ h.K)))
    (i : Occurrence xs) (hi : i ∈ h.selected) :
    occurrenceValue xs i ∈ h.K := by
  letI : Fintype (A ⧸ h.K) := Fintype.ofFinite (A ⧸ h.K)
  have hodd' : Odd (Fintype.card (A ⧸ h.K)) := by
    simpa [Nat.card_eq_fintype_card] using hodd
  exact mem_of_pos_neg_mem_same_coset_of_quotient_card_odd h.K hodd'
    (h.positiveWeightCoset i hi) (h.negativeWeightCoset i hi)

end GaoLean

#print axioms GaoLean.PlusMinusGMOConcentration.value_mem_subgroup
