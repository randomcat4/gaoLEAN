import GaoLean.PGGeneralWeightedDGMBridge
import GaoLean.PGGMOOrdinaryDGMSingleton
import GaoLean.PGPlusMinusSetpartition

/-!
# Regression certificates for the two manuscript weight sets

The general-weight definitions must specialize literally to the existing
ordinary and `{+1,-1}` occurrence models.  These equalities are useful both
as compatibility bridges and as guards against accidentally weakening the
general statement while developing the full GMO proof.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

theorem weightedValueBlock_singleton_one (x : A) :
    weightedValueBlock ({1} : Set ℤ) x = {x} := by
  classical
  ext y
  rw [mem_weightedValueBlock_iff]
  simp [eq_comm]

theorem weightedValueBlock_plusMinus (x : A) :
    weightedValueBlock ({-1, 1} : Set ℤ) x = plusMinusValueBlock x := by
  classical
  ext y
  rw [mem_weightedValueBlock_iff]
  simp [plusMinusValueBlock]
  aesop

theorem weightedOccurrenceSetpartition_singleton_one (xs : List A) :
    weightedOccurrenceSetpartition ({1} : Set ℤ) xs =
      ordinaryOccurrenceSetpartition xs := by
  classical
  simp [weightedOccurrenceSetpartition, ordinaryOccurrenceSetpartition,
    weightedValueBlock_singleton_one]

theorem weightedOccurrenceSetpartition_plusMinus (xs : List A) :
    weightedOccurrenceSetpartition ({-1, 1} : Set ℤ) xs =
      plusMinusOccurrenceSetpartition xs := by
  classical
  simp [weightedOccurrenceSetpartition, plusMinusOccurrenceSetpartition,
    weightedValueBlock_plusMinus]

theorem weightedExactSpectrum_singleton_one (xs : List A) (n : ℕ) :
    weightedExactSpectrum ({1} : Set ℤ) xs n =
      ordinaryExactSpectrum xs n := by
  classical
  rw [weightedExactSpectrum_eq_layerSubsumSpectrum,
    weightedOccurrenceSetpartition_singleton_one,
    layerSubsumSpectrum_ordinaryOccurrenceSetpartition]

theorem weightedExactSpectrum_plusMinus (xs : List A) (n : ℕ) :
    weightedExactSpectrum ({-1, 1} : Set ℤ) xs n =
      plusMinusExactSpectrum xs n := by
  classical
  rw [weightedExactSpectrum_eq_layerSubsumSpectrum,
    weightedOccurrenceSetpartition_plusMinus,
    plusMinusExactSpectrum_eq_layerSubsumSpectrum]

end GaoLean

#print axioms GaoLean.weightedValueBlock_singleton_one
#print axioms GaoLean.weightedValueBlock_plusMinus
#print axioms GaoLean.weightedOccurrenceSetpartition_singleton_one
#print axioms GaoLean.weightedOccurrenceSetpartition_plusMinus
#print axioms GaoLean.weightedExactSpectrum_singleton_one
#print axioms GaoLean.weightedExactSpectrum_plusMinus
