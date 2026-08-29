import GaoLean.PGGMOGeneralLemma35Core
import GaoLean.PGGeneralWeightedGcdTorsion

/-!
# General-weight specialization of GMO Lemma 3.5

This file applies the occurrence-labelled `generalLemma35Certificate_exists`
to the literal weighted value block at every selected source position.  The
index type used by the general theorem is the subtype of an actual source
selection `R`; its retained and core carriers are mapped back to
`Selection xs`.  Thus repeated equal source values remain separate
occurrences throughout the construction.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance generalWeightedLemma35DecidableEq
    {α : Type*} : DecidableEq α :=
  Classical.decEq α

noncomputable local instance generalWeightedLemma35PropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Full sumset of the literal weighted blocks indexed by a source
selection. -/
noncomputable def weightedSelectedCellSumset
    (W : Set ℤ) (xs : List A) (I : Selection xs) : Finset A :=
  selectedCellSumset
    (fun i : Occurrence xs ↦ weightedValueBlock W (occurrenceValue xs i)) I

/-- Source-facing certificate obtained from the general labelled form of
GMO Lemma 3.5.  Every carrier is an actual selection of source positions. -/
structure GeneralWeightedLemma35Certificate
    (W : Set ℤ) (xs : List A) (R : Selection xs)
    (K : AddSubgroup A) where
  H : AddSubgroup A
  H_le_K : H ≤ K
  H_ne_bot : H ≠ ⊥
  retained : Selection xs
  core : Selection xs
  retained_subset_R : retained ⊆ R
  core_subset_retained : core ⊆ retained
  retained_card_lower :
    min R.card (R.card - Nat.card (K ⧸ H.addSubgroupOf K) + 2) ≤
      retained.card
  core_card : core.card = Nat.card H - 1
  core_sumset_card :
    (weightedSelectedCellSumset W xs core).card = Nat.card H
  retained_singleton_mod :
    ∀ i ∈ retained,
      (quotientLayer H
        (weightedValueBlock W (occurrenceValue xs i))).card = 1

/-- Transport a general certificate on the subtype of `R` back to literal
source selections. -/
noncomputable def generalWeightedLemma35Certificate_of_general
    (W : Set ℤ) (xs : List A) (R : Selection xs)
    (K : AddSubgroup A)
    (C : GeneralLemma35Certificate K
      (fun j : ↥R ↦ weightedValueBlock W (occurrenceValue xs j.1))) :
    GeneralWeightedLemma35Certificate W xs R K := by
  classical
  let e : ↥R ↪ Occurrence xs := ⟨Subtype.val, Subtype.val_injective⟩
  refine {
    H := C.H
    H_le_K := C.H_le_K
    H_ne_bot := C.H_ne_bot
    retained := C.retained.map e
    core := C.core.map e
    retained_subset_R := ?_
    core_subset_retained := ?_
    retained_card_lower := ?_
    core_card := ?_
    core_sumset_card := ?_
    retained_singleton_mod := ?_
  }
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hi
    exact j.2
  · exact Finset.map_subset_map.mpr C.core_subset_retained
  · have hRcard : Nat.card ↥R = R.card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe R
    simpa [e, hRcard] using C.retained_card_lower
  · simpa [e] using C.core_card
  · change
      (selectedCellSumset
        (fun i : Occurrence xs ↦ weightedValueBlock W (occurrenceValue xs i))
        (C.core.map e)).card = Nat.card C.H
    calc
      (selectedCellSumset
          (fun i : Occurrence xs ↦ weightedValueBlock W (occurrenceValue xs i))
          (C.core.map e)).card =
          (selectedCellSumset
            (fun j : ↥R ↦ weightedValueBlock W (occurrenceValue xs j.1))
            C.core).card := by
        simpa [e] using
          congrArg Finset.card
            (selectedCellSumset_subtype_map
              (fun i : Occurrence xs ↦
                weightedValueBlock W (occurrenceValue xs i)) C.core).symm
      _ = Nat.card C.H := C.core_sumset_card
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact C.retained_singleton_mod j hj

/-- Specialization with an arbitrary subgroup `K`, when the one-`K`-coset
condition for every selected weighted block is supplied explicitly. -/
theorem generalWeightedLemma35Certificate_exists_of_quotient_singleton
    (W : Set ℤ) (xs : List A) (R : Selection xs)
    (K : AddSubgroup A) (hKne : K ≠ ⊥)
    (hcardTwo :
      ∀ i ∈ R, 2 ≤ (weightedValueBlock W (occurrenceValue xs i)).card)
    (hsingleK :
      ∀ i ∈ R,
        (quotientLayer K
          (weightedValueBlock W (occurrenceValue xs i))).card = 1)
    (hlength : Nat.card K - 1 ≤ R.card) :
    Nonempty (GeneralWeightedLemma35Certificate W xs R K) := by
  classical
  let cells : ↥R → Finset A := fun j ↦
    weightedValueBlock W (occurrenceValue xs j.1)
  have hcardTwo' : ∀ j : ↥R, 2 ≤ (cells j).card := by
    intro j
    exact hcardTwo j.1 j.2
  have hsingleK' :
      ∀ j : ↥R, (quotientLayer K (cells j)).card = 1 := by
    intro j
    exact hsingleK j.1 j.2
  have hRcard : Nat.card ↥R = R.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe R
  have hgeneral := generalLemma35Certificate_exists
    K hKne cells hcardTwo' hsingleK' (by simpa [hRcard] using hlength)
  obtain ⟨C⟩ := hgeneral
  exact ⟨generalWeightedLemma35Certificate_of_general W xs R K C⟩

/-- General weighted Step 6 with the canonical difference range `dA`.
Membership of the distinguished weight makes every weighted block a single
coset modulo this range, so no additional quotient-layer assumption is
needed. -/
theorem generalWeightedLemma35Certificate_exists
    (W : Set ℤ) (_hW : W.Nonempty) (w₀ : ℤ) (hw₀ : w₀ ∈ W)
    (xs : List A) (R : Selection xs)
    (hKne : weightedDifferenceRange W w₀ A ≠ ⊥)
    (hcardTwo :
      ∀ i ∈ R, 2 ≤ (weightedValueBlock W (occurrenceValue xs i)).card)
    (hlength :
      Nat.card (weightedDifferenceRange W w₀ A) - 1 ≤ R.card) :
    Nonempty (GeneralWeightedLemma35Certificate W xs R
      (weightedDifferenceRange W w₀ A)) := by
  classical
  apply generalWeightedLemma35Certificate_exists_of_quotient_singleton
    W xs R (weightedDifferenceRange W w₀ A) hKne hcardTwo
  · intro i _hi
    exact quotientLayer_weightedValueBlock_card_eq_one
      (A := A) hw₀ (occurrenceValue xs i)
  · exact hlength

end GaoLean

#print axioms GaoLean.generalWeightedLemma35Certificate_of_general
#print axioms GaoLean.generalWeightedLemma35Certificate_exists_of_quotient_singleton
#print axioms GaoLean.generalWeightedLemma35Certificate_exists
