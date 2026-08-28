import GaoLean.PGGMOTheorem21

/-!
# Terminal cases for the p-group structural recursion

This file isolates the endpoint in which a source-faithful Theorem E output
has common-coset count at most one.  The top and trivial periods, and the
proper nontrivial case with count one, are discharged by the exact existing
Theorem E / Theorem 2.1 adapters.

The remaining count-zero case is deliberately not hidden: the source output
then says that the replacement support is the whole source.  Consequently it
is excluded here by the explicit strict-source hypothesis
`seed.card < xs.length`.  No stronger conclusion is inferred from the
count-zero case itself.  A later structural driver must derive this strict
inequality separately from the frozen source-length hypotheses before using
this terminal lemma.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A terminal source-faithful Theorem E output gives the exact structural
ordinary alternative.  The strict-source hypothesis is used only to rule out
the proper nontrivial `N = 0` endpoint, where Theorem E otherwise proves only
that the replacement support exhausts the source. -/
theorem GMOTheoremESourceOutput.full_or_concentrated_of_terminal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hwide : Nat.card A ≤ seed.card - n + 1)
    (hsourceWide : Nat.card A ≤ xs.length)
    (hseedProper : seed.card < xs.length)
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
  · have hsupport :=
      out.support_eq_univ_of_commonCosetCount_eq_zero hbot hzero
    have hcard := congrArg Finset.card hsupport
    rw [out.partition.card_support_eq] at hcard
    have hseedFull : seed.card = xs.length := by
      simpa using hcard
    omega
  · obtain ⟨h21⟩ :=
      out.toProjected.nonempty_theorem21Output_of_count_eq_one
        hbot hproper hone
    exact h21.full_or_concentrated hwide hsourceWide

#print axioms GaoLean.GMOTheoremESourceOutput.full_or_concentrated_of_terminal

end GaoLean
