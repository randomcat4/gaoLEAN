import GaoLean.PGGMOClaimBTarget

/-!
# Occurrence-faithful complement bridge for ordinary GMO

If an `r`-cell occurrence partition has full sumset and its literal support
has cardinality `target + r`, then taking complements inside that fixed
support gives the full exact `target`-spectrum.  The construction never
replaces the partition support by the whole source list.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A full `r`-cell sumset on a fixed support of size `target + r`
supplies, for every target value, a literal complement selection of size
`target` inside that support. -/
theorem Theorem21SetPartition.exists_complement_selection_of_sumset_eq_univ
    {xs : List A} {r m target : ℕ}
    (P : Theorem21SetPartition xs r m)
    (hm : m = target + r)
    (hsumset : P.sumset = Finset.univ)
    (y : A) :
    ∃ I : Selection xs,
      I ⊆ P.support ∧ I.card = target ∧
        (∑ i ∈ I, occurrenceValue xs i) = y := by
  classical
  let total : A := ∑ i ∈ P.support, occurrenceValue xs i
  have htarget : total - y ∈ P.sumset := by
    rw [hsumset]
    exact Finset.mem_univ _
  obtain ⟨D, hDsub, hDcard, hDsum⟩ :=
    P.exists_selection_subset_support_of_mem_sumset htarget
  let I : Selection xs := P.support \ D
  refine ⟨I, Finset.sdiff_subset, ?_, ?_⟩
  · dsimp only [I]
    rw [Finset.card_sdiff_of_subset hDsub, P.card_support_eq,
      hDcard, hm]
    omega
  · have hsplit :=
      P.support.sum_inter_add_sum_sdiff D (occurrenceValue xs)
    rw [Finset.inter_eq_right.mpr hDsub, hDsum] at hsplit
    dsimp only [I]
    dsimp only [total] at hsplit
    abel

/-- Fixed-support complement duality turns a full partition sumset into the
ambient exact spectrum at the complementary cardinality. -/
theorem Theorem21SetPartition.ordinarySpectrumFull_of_complement_sumset_eq_univ
    {xs : List A} {r m target : ℕ}
    (P : Theorem21SetPartition xs r m)
    (hm : m = target + r)
    (hsumset : P.sumset = Finset.univ) :
    OrdinarySpectrumFull xs target := by
  intro y
  obtain ⟨I, _hIsub, hIcard, hIsum⟩ :=
    P.exists_complement_selection_of_sumset_eq_univ hm hsumset y
  exact ⟨I, hIcard, hIsum⟩

/-- The numerical large alternative reaches the whole ambient group whenever
its minimum is governed by `Nat.card A`. -/
theorem GMOTheorem21LargeAlternative.sumset_eq_univ
    {xs : List A} {seed : Selection xs} {r : ℕ}
    {P : Theorem21SetPartition xs r seed.card}
    (h : GMOTheorem21LargeAlternative xs seed r P)
    (hwide : Nat.card A ≤ seed.card - r + 1) :
    P.sumset = Finset.univ := by
  classical
  have hcardLower : Nat.card A ≤ P.sumset.card := by
    have hbound := h.card_lower
    rw [min_eq_left hwide] at hbound
    exact hbound
  have hcardUpper : P.sumset.card ≤ Nat.card A := by
    simpa using Finset.card_le_univ P.sumset
  have hcard : P.sumset.card = Fintype.card A := by
    simpa using Nat.le_antisymm hcardUpper hcardLower
  exact Finset.eq_univ_of_card P.sumset hcard

/-- Source-scale large-branch closure: the real replacement support has size
`target + r`, so its `r`-selection witnesses complement to exact
`target`-selection witnesses. -/
theorem GMOTheorem21LargeAlternative.ordinarySpectrumFull_complement
    {xs : List A} {seed : Selection xs} {r target : ℕ}
    {P : Theorem21SetPartition xs r seed.card}
    (h : GMOTheorem21LargeAlternative xs seed r P)
    (hm : seed.card = target + r)
    (hwide : Nat.card A ≤ seed.card - r + 1) :
    OrdinarySpectrumFull xs target :=
  P.ordinarySpectrumFull_of_complement_sumset_eq_univ
    hm (h.sumset_eq_univ hwide)

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.exists_complement_selection_of_sumset_eq_univ
#print axioms GaoLean.Theorem21SetPartition.ordinarySpectrumFull_of_complement_sumset_eq_univ
#print axioms GaoLean.GMOTheorem21LargeAlternative.sumset_eq_univ
#print axioms GaoLean.GMOTheorem21LargeAlternative.ordinarySpectrumFull_complement

