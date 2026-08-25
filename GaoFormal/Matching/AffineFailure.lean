import GaoFormal.Matching.OccurrenceLift

/-!
# Occurrence-labelled affine-failure residue identity

This is the label-faithful algebraic core of formula (3.4) in the frozen
affine-exchange theorem.  It identifies the exceptional source positions and
computes the quotient defect of every fixed-cardinality selection.
-/

namespace GaoFormal

open scoped BigOperators

variable {Ω V Q : Type*} [AddCommGroup V] [AddCommGroup Q]

/-- Source labels whose image is outside the distinguished affine fibre. -/
def affineExceptionalPart [DecidableEq Q]
    (C : Ω → V) (φ : V →+ Q) (β : Q) (I : Finset Ω) : Finset Ω :=
  I.filter fun ω => φ (C ω) ≠ β

theorem affineExceptionalPart_subset [DecidableEq Q]
    (C : Ω → V) (φ : V →+ Q) (β : Q) (I : Finset Ω) :
    affineExceptionalPart C φ β I ⊆ I :=
  Finset.filter_subset _ _

/-- Exact labelled form of the affine quotient calculation: after subtracting
one copy of `β` for every selected occurrence, only the selected exceptional
labels contribute.  Repeated values remain separate terms in both sums. -/
theorem sum_image_sub_card_smul_eq_sum_exceptional_offsets
    [DecidableEq Ω] [DecidableEq Q]
    (C : Ω → V) (φ : V →+ Q) (β : Q) (I : Finset Ω) :
    (∑ ω ∈ I, φ (C ω)) - I.card • β =
      ∑ ω ∈ affineExceptionalPart C φ β I, (φ (C ω) - β) := by
  have hfull :
      (∑ ω ∈ I, (φ (C ω) - β)) =
        ∑ ω ∈ affineExceptionalPart C φ β I, (φ (C ω) - β) := by
    classical
    rw [affineExceptionalPart]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : φ (C ω) ≠ β
    · simp [h]
    · simp [not_ne_iff.mp h]
  rw [← hfull]
  rw [Finset.sum_sub_distrib]
  simp

/-- Fixed-cardinality specialization used in formula (3.4). -/
theorem sum_image_sub_fixed_smul_eq_sum_exceptional_offsets
    [DecidableEq Ω] [DecidableEq Q]
    (C : Ω → V) (φ : V →+ Q) (β : Q) (I : Finset Ω) (d : ℕ)
    (hcard : I.card = d) :
    (∑ ω ∈ I, φ (C ω)) - d • β =
      ∑ ω ∈ affineExceptionalPart C φ β I, (φ (C ω) - β) := by
  rw [← hcard]
  exact sum_image_sub_card_smul_eq_sum_exceptional_offsets C φ β I

/-- Equality of two fixed-cardinality sums is therefore equivalent to
equality of their labelled exceptional-offset sums. -/
theorem fixedCardinality_sum_eq_iff_exceptionalOffsets_eq
    [DecidableEq Ω] [DecidableEq Q]
    (C : Ω → V) (φ : V →+ Q) (β : Q)
    (I J : Finset Ω) (d : ℕ) (hI : I.card = d) (hJ : J.card = d) :
    (∑ ω ∈ I, φ (C ω)) = ∑ ω ∈ J, φ (C ω) ↔
      (∑ ω ∈ affineExceptionalPart C φ β I, (φ (C ω) - β)) =
        ∑ ω ∈ affineExceptionalPart C φ β J, (φ (C ω) - β) := by
  have hresI :=
    sum_image_sub_fixed_smul_eq_sum_exceptional_offsets C φ β I d hI
  have hresJ :=
    sum_image_sub_fixed_smul_eq_sum_exceptional_offsets C φ β J d hJ
  constructor <;> intro h
  · rw [← hresI, ← hresJ, h]
  · have hsub :
        (∑ ω ∈ I, φ (C ω)) - d • β =
          (∑ ω ∈ J, φ (C ω)) - d • β := by
      rw [hresI, hresJ, h]
    exact sub_left_injective hsub

end GaoFormal

#print axioms GaoFormal.affineExceptionalPart_subset
#print axioms GaoFormal.sum_image_sub_card_smul_eq_sum_exceptional_offsets
#print axioms GaoFormal.sum_image_sub_fixed_smul_eq_sum_exceptional_offsets
#print axioms GaoFormal.fixedCardinality_sum_eq_iff_exceptionalOffsets_eq
