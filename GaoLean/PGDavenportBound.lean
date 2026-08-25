import GaoLean.PGStatements

/-!
# Finite-group bound for the ordinary Davenport constant

This module proves the elementary finite-group inequality `D(A) ≤ |A|`
directly from the occurrence-sensitive definition in `PGStatements`.  The
proof uses `|A| + 1` prefix sums, extracts two equal prefixes by finite
pigeonhole, and selects exactly the intervening source occurrences.
-/

namespace GaoLean

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Sum of the first `n` entries, using zero past the end.  In the main proof
all queried indices are bounded by the source length. -/
noncomputable def finitePrefixSum (s : List A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range n, s.getD k 0

/-- The occurrence-labelled half-open interval `[m,n)` in a source list. -/
noncomputable def intervalSelection (s : List A) (m n : ℕ) : Selection s :=
  Finset.univ.filter fun i => m ≤ i.1 ∧ i.1 < n

omit [AddCommGroup A] [Fintype A] in
theorem intervalSelection_nonempty (s : List A) {m n : ℕ}
    (hmn : m < n) (hn : n ≤ s.length) :
    (intervalSelection s m n).Nonempty := by
  have hm : m < s.length := lt_of_lt_of_le hmn hn
  refine ⟨⟨m, hm⟩, ?_⟩
  simp [intervalSelection, hmn]

omit [Fintype A] in
theorem sum_intervalSelection_eq_sum_Ico (s : List A) {m n : ℕ}
    (hn : n ≤ s.length) :
    (∑ i ∈ intervalSelection s m n, occurrenceValue s i) =
      ∑ k ∈ Finset.Ico m n, s.getD k 0 := by
  refine Finset.sum_bij (fun i _ => i.1) ?_ ?_ ?_ ?_
  · intro i hi
    simpa [intervalSelection] using hi
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Fin.ext heq
  · intro k hk
    have hkn : k < n := (Finset.mem_Ico.mp hk).2
    have hks : k < s.length := lt_of_lt_of_le hkn hn
    let i : Occurrence s := ⟨k, hks⟩
    refine ⟨i, ?_, rfl⟩
    simpa [intervalSelection, i] using hk
  · intro i hi
    exact (List.getD_eq_get s 0 i).symm

omit [Fintype A] in
theorem hasNonemptyZeroSum_of_equal_prefixes (s : List A) {m n : ℕ}
    (hmn : m < n) (hn : n ≤ s.length)
    (heq : finitePrefixSum s m = finitePrefixSum s n) :
    HasNonemptyZeroSum s := by
  refine ⟨intervalSelection s m n,
    intervalSelection_nonempty s hmn hn, ?_⟩
  rw [sum_intervalSelection_eq_sum_Ico s hn]
  rw [Finset.sum_Ico_eq_sub (fun k => s.getD k 0) (Nat.le_of_lt hmn)]
  exact sub_eq_zero.mpr heq.symm

/-- Every list of length `|A|` in a finite additive group has a nonempty
occurrence-labelled zero-sum subsequence. -/
theorem hasNonemptyZeroSum_of_length_natCard (s : List A)
    (hlen : s.length = Nat.card A) :
    HasNonemptyZeroSum s := by
  let f : Fin (Nat.card A + 1) → A := fun i => finitePrefixSum s i.1
  have hnotInjective : ¬Function.Injective f := by
    intro hinjective
    have hcard := Fintype.card_le_of_injective f hinjective
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hcard
    omega
  obtain ⟨i, j, hij, hne⟩ :=
    Function.not_injective_iff.mp hnotInjective
  have hi : i.1 ≤ Nat.card A := by omega
  have hj : j.1 ≤ Nat.card A := by omega
  by_cases hlt : i.1 < j.1
  · apply hasNonemptyZeroSum_of_equal_prefixes s hlt
      (by simpa [hlen] using hj)
    exact hij
  · have hvalne : i.1 ≠ j.1 := by
      intro hval
      apply hne
      exact Fin.ext hval
    have hrev : j.1 < i.1 := by omega
    apply hasNonemptyZeroSum_of_equal_prefixes s hrev
      (by simpa [hlen] using hi)
    exact hij.symm

/-- The exact ordinary Davenport constant of a finite additive group cannot
exceed the group cardinality.  This is derived from its defining lower
counterexample clause and the preceding prefix-sum theorem. -/
theorem ordinaryDavenportConstant_le_natCard (D : ℕ)
    (hD : IsOrdinaryDavenportConstant A D) :
    D ≤ Nat.card A := by
  by_contra hle
  have hlt : Nat.card A < D := Nat.lt_of_not_ge hle
  obtain ⟨s, hlen, hfree⟩ := hD.2 (Nat.card A) hlt
  exact hfree (hasNonemptyZeroSum_of_length_natCard s hlen)

end GaoLean

#print axioms GaoLean.intervalSelection_nonempty
#print axioms GaoLean.sum_intervalSelection_eq_sum_Ico
#print axioms GaoLean.hasNonemptyZeroSum_of_equal_prefixes
#print axioms GaoLean.hasNonemptyZeroSum_of_length_natCard
#print axioms GaoLean.ordinaryDavenportConstant_le_natCard
