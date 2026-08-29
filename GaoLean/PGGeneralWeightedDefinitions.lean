import GaoLean.Sequence
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# General integer-weighted GMO definitions

This file freezes the literal general-weight statement used in Theorem 2.2
of the manuscript.  A weight set is an arbitrary `Set ℤ`: none of the
definitions below assumes that it is finite.  Selections are sets of source
positions, so repeated source values remain distinct occurrences.

The source's condition `gcd(W) = 1` is represented by
`AddSubgroup.closure W = ⊤`, i.e. the integer weights generate all of `ℤ`.
For an arbitrary (possibly infinite) set this is the intrinsic additive-group
form of the gcd-one condition.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A]

/-- Data witnessing that exactly `n` labelled source occurrences have a
`W`-weighted sum equal to `y`.  The weight function is total on source
positions, but only its values at selected positions are constrained to lie
in `W`; this avoids quotienting or enumerating the possibly infinite set `W`.
-/
structure HasWeightedSumOfCard
    (W : Set ℤ) (xs : List A) (n : ℕ) (y : A) where
  selected : Selection xs
  weights : Occurrence xs → ℤ
  weights_mem : ∀ i ∈ selected, weights i ∈ W
  card_selected : selected.card = n
  weighted_sum :
    (∑ i ∈ selected, weights i • occurrenceValue xs i) = y

/-- Every exact weighted selection uses no more occurrences than the source
contains. -/
theorem HasWeightedSumOfCard.card_le_length
    {W : Set ℤ} {xs : List A} {n : ℕ} {y : A}
    (h : HasWeightedSumOfCard W xs n y) : n ≤ xs.length := by
  rw [← h.card_selected]
  simpa using Finset.card_le_card (Finset.subset_univ h.selected)

section FiniteAmbient

variable [Fintype A]

/-- The finite set `Σⁿ_W(xs)` of all values of exact `n`-occurrence
weighted sums.  Finiteness comes only from the finite ambient group `A`, not
from the weight set `W`. -/
noncomputable def weightedExactSpectrum
    (W : Set ℤ) (xs : List A) (n : ℕ) : Finset A := by
  classical
  exact Finset.univ.filter fun y ↦
    Nonempty (HasWeightedSumOfCard W xs n y)

@[simp]
theorem mem_weightedExactSpectrum_iff
    (W : Set ℤ) (xs : List A) (n : ℕ) (y : A) :
    y ∈ weightedExactSpectrum W xs n ↔
      Nonempty (HasWeightedSumOfCard W xs n y) := by
  classical
  simp [weightedExactSpectrum]

/-- The exact zero-occurrence weighted spectrum is `{0}`.  No nonemptiness
assumption on `W` is needed because no occurrence receives a used weight. -/
@[simp]
theorem weightedExactSpectrum_zero (W : Set ℤ) (xs : List A) :
    weightedExactSpectrum W xs 0 = {0} := by
  classical
  ext y
  rw [mem_weightedExactSpectrum_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨h⟩
    have hselected : h.selected = ∅ := Finset.card_eq_zero.mp h.card_selected
    simpa [hselected] using h.weighted_sum.symm
  · rintro rfl
    exact ⟨{
      selected := ∅
      weights := fun _ ↦ 0
      weights_mem := by simp
      card_selected := by simp
      weighted_sum := by simp
    }⟩

/-- If `W` is nonempty, an exact weighted sum exists at every feasible
cardinality. -/
theorem weightedExactSpectrum_nonempty
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : n ≤ xs.length) :
    (weightedExactSpectrum W xs n).Nonempty := by
  classical
  obtain ⟨w, hw⟩ := hW
  obtain ⟨I, -, hIcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Selection xs)) (by simpa using hn)
  let y : A := ∑ i ∈ I, w • occurrenceValue xs i
  let hsum : HasWeightedSumOfCard W xs n y := {
    selected := I
    weights := fun _ ↦ w
    weights_mem := by
      intro i hi
      exact hw
    card_selected := hIcard
    weighted_sum := rfl
  }
  exact ⟨y, (mem_weightedExactSpectrum_iff W xs n y).2 ⟨hsum⟩⟩

/-- A source sequence has a nonempty occurrence-labelled `W`-weighted
zero-sum subsequence. -/
def HasNonemptyWeightedZeroSum (W : Set ℤ) (xs : List A) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Nonempty (HasWeightedSumOfCard W xs n 0)

/-- Threshold formulation of `D_W(A) ≤ D`. -/
def WeightedDavenportAtMost
    (W : Set ℤ) (A : Type u) [AddCommGroup A] (D : ℕ) : Prop :=
  ∀ xs : List A, xs.length = D → HasNonemptyWeightedZeroSum W xs

/-- Occurrence-sensitive assertion that `D` is the exact weighted Davenport
constant.  Besides the upper property at `D`, every smaller length has an
explicit weighted-zero-sum-free witness. -/
def IsWeightedDavenportConstant
    (W : Set ℤ) (A : Type u) [AddCommGroup A] (D : ℕ) : Prop :=
  WeightedDavenportAtMost W A D ∧
    ∀ n : ℕ, n < D →
      ∃ xs : List A,
        xs.length = n ∧ ¬HasNonemptyWeightedZeroSum W xs

/-- The intrinsic form of the source hypothesis `gcd(W) = 1`: the weights
generate the whole additive group of integers.  This definition is valid
without a finiteness assumption on `W`. -/
def IsPrimitiveWeightSet (W : Set ℤ) : Prop :=
  AddSubgroup.closure W = ⊤

/-- The set `W x = {w • x | w ∈ W}`, represented as a finite subset of the
finite ambient group.  Again, `W` itself need not be finite. -/
noncomputable def weightedValueBlock (W : Set ℤ) (x : A) : Finset A := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ w : ℤ, w ∈ W ∧ w • x = y

@[simp]
theorem mem_weightedValueBlock_iff
    (W : Set ℤ) (x y : A) :
    y ∈ weightedValueBlock W x ↔
      ∃ w : ℤ, w ∈ W ∧ w • x = y := by
  classical
  simp [weightedValueBlock]

theorem weightedValueBlock_nonempty
    {W : Set ℤ} (hW : W.Nonempty) (x : A) :
    (weightedValueBlock W x).Nonempty := by
  obtain ⟨w, hw⟩ := hW
  exact ⟨w • x,
    (mem_weightedValueBlock_iff W x (w • x)).2 ⟨w, hw, rfl⟩⟩

/-- One literal weighted value block for every source occurrence.  Equal
source values remain repeated list entries rather than being deduplicated. -/
noncomputable def weightedOccurrenceSetpartition
    (W : Set ℤ) (xs : List A) : List (Finset A) := by
  classical
  exact xs.map (weightedValueBlock W)

@[simp]
theorem length_weightedOccurrenceSetpartition
    (W : Set ℤ) (xs : List A) :
    (weightedOccurrenceSetpartition W xs).length = xs.length := by
  classical
  simp [weightedOccurrenceSetpartition]

/-- Nonempty weights make every literal weighted occurrence layer nonempty.
-/
theorem weightedOccurrenceSetpartition_cells_nonempty
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) :
    ∀ B ∈ weightedOccurrenceSetpartition W xs, B.Nonempty := by
  classical
  intro B hB
  obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hB
  exact weightedValueBlock_nonempty hW x

/-- The complete non-full conclusion of general weighted GMO.  A *single*
global subgroup `K` and centers `alpha`, `beta` serve all retained source
occurrences and every weight in `W`, exactly as in the manuscript's two coset
clauses.  The lower bound counts occurrences, including repeated values. -/
structure WeightedGMOConcentration
    (W : Set ℤ) (xs : List A) where
  K : AddSubgroup A
  strict : K < ⊤
  alpha : A
  beta : A
  selected : Selection xs
  sourceCoset :
    ∀ i ∈ selected, occurrenceValue xs i - alpha ∈ K
  weightCoset :
    ∀ i ∈ selected, ∀ w ∈ W,
      w • occurrenceValue xs i - beta ∈ K
  card_lower :
    xs.length - Nat.card (A ⧸ K) + 2 ≤ selected.card

/-- The exact source conclusion `Σⁿ_W(T) ∩ nA ≠ ∅`. -/
def WeightedGMOExistenceConclusion
    (W : Set ℤ) (xs : List A) (n : ℕ) : Prop :=
  ∃ x : A, Nonempty (HasWeightedSumOfCard W xs n (n • x))

/-- Proposition-valued interface for the existence clause of manuscript
Theorem 2.2.  It quantifies over arbitrary nonempty integer weight sets and
uses the exact weighted Davenport constant in the source length threshold. -/
def GeneralWeightedGMOExistenceProvider
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (W : Set ℤ), W.Nonempty →
    ∀ (D : ℕ), IsWeightedDavenportConstant W A D →
      ∀ (xs : List A) (n : ℕ),
        Nat.card A ≤ n →
        n + D - 1 ≤ xs.length →
        WeightedGMOExistenceConclusion W xs n

/-- Proposition-valued interface for the structural clause of manuscript
Theorem 2.2.  The extra source hypothesis `gcd(W)=1` is kept explicitly as
`IsPrimitiveWeightSet W`. -/
def GeneralWeightedGMOStructuralProvider
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (W : Set ℤ), W.Nonempty → IsPrimitiveWeightSet W →
    ∀ (D : ℕ), IsWeightedDavenportConstant W A D →
      ∀ (xs : List A) (n : ℕ),
        Nat.card A ≤ n →
        n + D - 1 ≤ xs.length →
        weightedExactSpectrum W xs n = Finset.univ ∨
          Nonempty (WeightedGMOConcentration W xs)

/-- The source package keeps the existence and structural clauses separate,
while exposing their conjunction as the exact general-weight theorem boundary.
This is a `Prop` interface, not an axiom or an assertion that the theorem has
already been proved in this file. -/
def GeneralWeightedGMOSourcePackage
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  GeneralWeightedGMOExistenceProvider A ∧
    GeneralWeightedGMOStructuralProvider A

end FiniteAmbient

end GaoLean

#print axioms GaoLean.HasWeightedSumOfCard.card_le_length
#print axioms GaoLean.mem_weightedExactSpectrum_iff
#print axioms GaoLean.weightedExactSpectrum_zero
#print axioms GaoLean.weightedExactSpectrum_nonempty
#print axioms GaoLean.mem_weightedValueBlock_iff
#print axioms GaoLean.weightedValueBlock_nonempty
#print axioms GaoLean.length_weightedOccurrenceSetpartition
#print axioms GaoLean.weightedOccurrenceSetpartition_cells_nonempty
