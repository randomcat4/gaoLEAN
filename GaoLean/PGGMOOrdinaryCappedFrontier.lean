import GaoLean.PGGMOOrdinaryCarrierWiden
import GaoLean.PGGMOOrdinaryComplement
import GaoLean.PGGMOOrdinarySeed

/-!
# Honest capped fixed-carrier frontier

The canonical capped selection always contains at least `r` labelled
occurrences when the source itself has length at least `r`.  Given a genuine
fixed-carrier structural trichotomy at weight `r`, this module closes the
fixed branch by exact carrier widening and closes a sufficiently wide large
branch through its actual replacement partition.

If the large branch is not wide enough to fill the ambient group, the exact
partition and its large-alternative certificate are returned together with
the strict width failure.  That residual branch is not declared impossible.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- If the source contains at least `r` labelled occurrences, its capped
fiber mass at cap `r` is at least `r`. -/
theorem self_le_cappedFiberMass
    (xs : List A) (r : ℕ) (hrSource : r ≤ xs.length) :
    r ≤ cappedFiberMass xs r := by
  classical
  have hrUniv : r ≤ (Finset.univ : Selection xs).card := by
    simpa using hrSource
  obtain ⟨I, _hIuniv, hIcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Selection xs)) hrUniv
  have hcap : SelectionMultiplicityAtMost xs I r := by
    intro a
    change (I.filter fun i ↦ occurrenceValue xs i = a).card ≤ r
    rw [← hIcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  calc
    r = I.card := hIcard.symm
    _ ≤ cappedFiberMass xs r :=
      selection_card_le_cappedFiberMass xs I r hcap

/-- The honest residual frontier for the canonical capped selection.  The
third branch preserves a genuine `r`-cell replacement partition and records
the exact numerical obstruction to closing it by ambient cardinality. -/
noncomputable def OrdinaryGMOCappedFrontier
    (xs : List A) (r target : ℕ) : Prop :=
  OrdinarySpectrumFull xs target ∨
    Nonempty (OrdinaryGMOConcentration xs) ∨
    ∃ P : Theorem21SetPartition xs r
        (cappedOccurrenceSelection xs r).card,
      GMOTheorem21LargeAlternative xs
          (cappedOccurrenceSelection xs r) r P ∧
        Nat.card A >
          (cappedOccurrenceSelection xs r).card - r + 1

/-- Resolve a fixed-carrier trichotomy on the canonical capped selection up
to the genuine low-width large frontier.

The full branch is widened from the capped carrier size to the prescribed
`m = target + r`.  In the large branch, ambient width first makes the actual
partition sumset full; its literal support becomes a fixed carrier and is
then widened in the same way.  Only failure of that width test reaches the
third branch, with the original partition retained. -/
theorem ordinaryGMOCappedFrontier_of_fixedCarrierStructuralTrichotomy
    (xs : List A) (r m target : ℕ)
    (hCLe : (cappedOccurrenceSelection xs r).card ≤ m)
    (hmSource : m ≤ xs.length)
    (hm : m = target + r)
    (htri : OrdinaryGMOFixedCarrierStructuralTrichotomy xs
      (cappedOccurrenceSelection xs r) r) :
    OrdinaryGMOCappedFrontier xs r target := by
  have hCtarget :
      (cappedOccurrenceSelection xs r).card ≤ target + r := by
    rw [← hm]
    exact hCLe
  have htargetSource : target + r ≤ xs.length := by
    rw [← hm]
    exact hmSource
  rcases htri with hfixed | hlarge | hconcentration
  · obtain ⟨F⟩ := hfixed
    exact Or.inl
      (F.ordinarySpectrumFull_complement_after_widen
        hCtarget htargetSource)
  · obtain ⟨P, hP⟩ := hlarge
    by_cases hwide :
        Nat.card A ≤
          (cappedOccurrenceSelection xs r).card - r + 1
    · have hsumset : P.sumset = Finset.univ :=
        hP.sumset_eq_univ hwide
      let F : OrdinaryFixedCarrierSpectrumFull xs
          (cappedOccurrenceSelection xs r).card r :=
        P.fixedCarrierSpectrumFull_of_sumset_eq_univ hsumset
      exact Or.inl
        (F.ordinarySpectrumFull_complement_after_widen
          hCtarget htargetSource)
    · exact Or.inr (Or.inr
        ⟨P, hP, Nat.lt_of_not_ge hwide⟩)
  · exact Or.inr (Or.inl hconcentration)

#print axioms GaoLean.self_le_cappedFiberMass
#print axioms GaoLean.ordinaryGMOCappedFrontier_of_fixedCarrierStructuralTrichotomy

end GaoLean
