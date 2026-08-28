import GaoLean.PGGMOTheorem21

/-!
# Terminal cases for the p-group structural recursion

This file isolates the endpoint in which a source-faithful Theorem E output
has common-coset count at most one.  The top and trivial periods, and the
proper nontrivial case with count one, are discharged by the exact existing
Theorem E / Theorem 2.1 adapters.

The count-zero case uses its direct large alternative.  Thus no strict-source
hypothesis is needed at the terminal boundary.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A terminal source-faithful Theorem E output gives the exact structural
ordinary alternative.  At `N = 0` the direct large alternative becomes full
under the same explicit width hypothesis used by every large branch. -/
theorem GMOTheoremESourceOutput.full_or_concentrated_of_terminal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hwide : Nat.card A ≤ seed.card - n + 1)
    (hsourceWide : Nat.card A ≤ xs.length)
    (hterminal : out.partition.commonCosetCount out.H ≤ 1) :
    OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
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
  · have hlarge :=
      out.toProjected.largeAlternative_of_H_eq_bot hbot hlen
    exact Or.inl (hlarge.ordinarySpectrumFull hwide)
  have hproper : out.H < ⊤ := lt_top_iff_ne_top.mpr htop
  have hcount :
      out.partition.commonCosetCount out.H = 0 ∨
        out.partition.commonCosetCount out.H = 1 := by
    omega
  rcases hcount with hzero | hone
  · have hlarge :=
      out.largeAlternative_of_commonCosetCount_eq_zero hlen hzero
    exact Or.inl (hlarge.ordinarySpectrumFull hwide)
  · obtain ⟨h21⟩ :=
      out.toProjected.nonempty_theorem21Output_of_count_eq_one
        hbot hproper hone
    exact h21.full_or_concentrated hwide hsourceWide

#print axioms GaoLean.GMOTheoremESourceOutput.full_or_concentrated_of_terminal

end GaoLean
