import GaoLean.PGGMOPGroupStructuralTerminal

/-!
# Honest terminal trichotomy for the p-group structural recursion

The large branch of Theorem 2.1 does not by itself make the exact ordinary
spectrum full unless a separate width inequality is available.  This module
therefore retains that branch together with its actual occurrence-labelled
setpartition.  The periodic branch is converted only to the weaker ordinary
concentration object used by the frozen thirteen-page manuscript; this is not
presented as a proof of the full periodic alternative of GMO Theorem 2.1.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The recursive structural consumer has three honest outcomes: the exact
ordinary spectrum is full; an actual replacement partition satisfies the
unweakened large-cardinality alternative; or the source occurrences satisfy
the manuscript's ordinary concentration conclusion. -/
def OrdinaryGMOStructuralTrichotomy
    (xs : List A) (seed : Selection xs) (n : ℕ) : Prop :=
  OrdinarySpectrumFull xs n ∨
    (∃ P : Theorem21SetPartition xs n seed.card,
      GMOTheorem21LargeAlternative xs seed n P) ∨
    Nonempty (OrdinaryGMOConcentration xs)

/-- A terminal source-faithful Theorem E output gives the honest recursive
trichotomy without assuming the width needed to turn a large setpartition
sumset into the whole ambient group.  The count-zero endpoint returns its
direct large alternative, so no strict-source hypothesis is needed. -/
theorem GMOTheoremESourceOutput.structuralTrichotomy_of_terminal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hsourceWide : Nat.card A ≤ xs.length)
    (hterminal : out.partition.commonCosetCount out.H ≤ 1) :
    OrdinaryGMOStructuralTrichotomy xs seed n := by
  classical
  have hlen : n ≤ seed.card := by
    have hmass := length_le_sum_layer_card out.partition.valueCells
      out.partition.valueCells_nonempty
    rw [out.partition.length_valueCells] at hmass
    simpa [Theorem21SetPartition.valueCells, List.map_ofFn,
      List.sum_ofFn, out.partition.sum_card_valueCell] using hmass
  by_cases htop : out.H = ⊤
  · exact Or.inl
      (out.toProjected.ordinarySpectrumFull_of_H_eq_top htop)
  by_cases hbot : out.H = ⊥
  · exact Or.inr (Or.inl
      ⟨out.partition,
        out.toProjected.largeAlternative_of_H_eq_bot hbot hlen⟩)
  have hproper : out.H < ⊤ := lt_top_iff_ne_top.mpr htop
  have hcount :
      out.partition.commonCosetCount out.H = 0 ∨
        out.partition.commonCosetCount out.H = 1 := by
    omega
  rcases hcount with hzero | hone
  · exact Or.inr (Or.inl
      ⟨out.partition,
        out.largeAlternative_of_commonCosetCount_eq_zero hlen hzero⟩)
  · obtain ⟨h21⟩ :=
      out.toProjected.nonempty_theorem21Output_of_count_eq_one
        hbot hproper hone
    rcases h21.alternative with hlarge | hperiodic
    · exact Or.inr (Or.inl ⟨h21.partition, hlarge⟩)
    · obtain ⟨hperiodic⟩ := hperiodic
      have hquotientLe : Nat.card (A ⧸ hperiodic.H) ≤ Nat.card A :=
        Nat.le_of_dvd Nat.card_pos hperiodic.H.card_quotient_dvd_card
      exact Or.inr (Or.inr
        ⟨hperiodic.toOrdinaryGMOConcentration
          (hquotientLe.trans hsourceWide)⟩)

#print axioms GaoLean.GMOTheoremESourceOutput.structuralTrichotomy_of_terminal

end GaoLean
