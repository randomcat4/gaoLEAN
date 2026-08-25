import GaoLean.PGCapacity

/-!
# Occurrence-labelled rotation spectra

This file isolates the internal full-spectrum closure used in A-R6 equations
(5.14)--(5.15).  It does not assert that GMO produces the required
subselection; it proves the exact product-one and complement consequences once
such a labelled subselection is supplied.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Additive coordinate sum of an occurrence-labelled selection. -/
def coordinateSum (s : List (Group A)) (I : Selection s) : A :=
  ∑ i ∈ I, coordinate (occurrenceValue s i)

theorem sum_map_coordinate_selectedMultiset_toList
    (s : List (Group A)) (I : Selection s) :
    ((selectedMultiset s I).toList.map coordinate).sum =
      coordinateSum s I := by
  classical
  simp [coordinateSum, selectedMultiset]

/-- An all-rotation labelled selection with zero coordinate sum is product
one.  The witness uses the exact selected multiset, so equal values at
different source positions remain separate occurrences. -/
theorem isProductOneSelection_of_allRotation_coordinateSum_eq_zero
    (s : List (Group A)) (I : Selection s)
    (hall : ∀ i ∈ I, IsRotation (occurrenceValue s i))
    (hsum : coordinateSum s I = 0) :
    IsProductOneSelection s I := by
  let word := (selectedMultiset s I).toList
  have hallWord : ∀ g ∈ word, IsRotation g := by
    intro g hg
    have hg' : g ∈ selectedMultiset s I := by
      simpa [word] using hg
    rw [selectedMultiset] at hg'
    rcases Multiset.mem_map.mp hg' with ⟨i, hi, rfl⟩
    exact hall i hi
  refine ⟨word, ?_, ?_⟩
  · simp [word]
  · rw [prod_eq_rotation_sum_of_all_rotation word hallWord]
    have hwordSum : (word.map coordinate).sum = 0 := by
      rw [show (word.map coordinate).sum = coordinateSum s I by
        exact sum_map_coordinate_selectedMultiset_toList s I]
      exact hsum
    rw [hwordSum]
    simp [rotation]

/-- Exact-cardinality controller conclusion from a zero coordinate sum. -/
theorem hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
    (s : List (Group A)) (I : Selection s) (k : ℕ)
    (hcard : I.card = k)
    (hall : ∀ i ∈ I, IsRotation (occurrenceValue s i))
    (hsum : coordinateSum s I = 0) :
    HasAllRotationProductOneSubsequenceOfCard s k := by
  exact ⟨I, hcard,
    isProductOneSelection_of_allRotation_coordinateSum_eq_zero s I hall hsum,
    hall⟩

/-- Coordinate sums respect disjoint occurrence unions. -/
theorem coordinateSum_union
    (s : List (Group A)) (I J : Selection s) (hIJ : Disjoint I J) :
    coordinateSum s (I ∪ J) = coordinateSum s I + coordinateSum s J := by
  classical
  exact Finset.sum_union hIJ

/-- Occurrence-complement form of equation (5.15). -/
theorem coordinateSum_sdiff_add
    (s : List (Group A)) (C D : Selection s) (hDC : D ⊆ C) :
    coordinateSum s (C \ D) + coordinateSum s D = coordinateSum s C := by
  classical
  rw [← coordinateSum_union s (C \ D) D Finset.disjoint_sdiff.symm]
  rw [Finset.sdiff_union_of_subset hDC]

theorem coordinateSum_sdiff
    (s : List (Group A)) (C D : Selection s) (hDC : D ⊆ C) :
    coordinateSum s (C \ D) = coordinateSum s C - coordinateSum s D := by
  have h := coordinateSum_sdiff_add s C D hDC
  exact eq_sub_iff_add_eq.mpr h

/-- Full-spectrum internal closure for (5.14): if a selected `D⊆C` has the
same coordinate sum as `C`, then the exact occurrence complement is a
product-one all-rotation block of any certified cardinality. -/
theorem hasAllRotationProductOneSubsequence_of_complement_coordinateSum_eq
    (s : List (Group A)) (C D : Selection s) (k : ℕ)
    (hDC : D ⊆ C)
    (hcard : (C \ D).card = k)
    (hallC : ∀ i ∈ C, IsRotation (occurrenceValue s i))
    (hsum : coordinateSum s D = coordinateSum s C) :
    HasAllRotationProductOneSubsequenceOfCard s k := by
  apply hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
    s (C \ D) k hcard
  · intro i hi
    exact hallC i (Finset.mem_sdiff.mp hi).1
  · rw [coordinateSum_sdiff s C D hDC, hsum, sub_self]

/-- Cardinality-facing version used by (5.14). -/
theorem hasAllRotationProductOneSubsequence_of_fullSpectrumComplement
    (s : List (Group A)) (C D : Selection s) (Q M d : ℕ)
    (hDC : D ⊆ C)
    (hCcard : C.card = M) (hDcard : D.card = d)
    (hsize : M - d = 2 * Q)
    (hallC : ∀ i ∈ C, IsRotation (occurrenceValue s i))
    (hsum : coordinateSum s D = coordinateSum s C) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  apply hasAllRotationProductOneSubsequence_of_complement_coordinateSum_eq
    s C D (2 * Q) hDC
  · rw [Finset.card_sdiff_of_subset hDC, hCcard, hDcard, hsize]
  · exact hallC
  · exact hsum

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.sum_map_coordinate_selectedMultiset_toList
#print axioms GaoLean.ConcreteGDihedral.isProductOneSelection_of_allRotation_coordinateSum_eq_zero
#print axioms GaoLean.ConcreteGDihedral.coordinateSum_sdiff
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_complement_coordinateSum_eq
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_fullSpectrumComplement
