import GaoLean.PlusMinus
import GaoLean.PGDavenportBound

/-!
# Internal plus-minus bounds used by the GAO-AR proof

This file formalizes the elementary bounds proved inside the manuscript.  In
particular, these are not literature interfaces and are not allowed to remain
as assumptions of the final theorem.
-/

namespace GaoLean

section BinarySubsetSums

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The elementary comparison `D_±(A) ≤ |A|`: use the ordinary zero-sum
subsequence and give every selected occurrence the positive sign. -/
theorem plusMinusDavenportAtMost_natCard :
    PlusMinusDavenportAtMost A (Nat.card A) := by
  intro s hs
  obtain ⟨I, hI, hsum⟩ := hasNonemptyZeroSum_of_length_natCard s hs
  refine ⟨I, hI, fun _ => .positive, ?_⟩
  simpa [PlusMinusSign.act] using hsum

/-- If the number of subsets of `m` labelled positions exceeds the group
cardinality, two subset sums collide and their symmetric difference is a
nonempty plus-minus zero sum. -/
theorem plusMinusDavenportAtMost_of_natCard_lt_two_pow
    {m : ℕ} (hcard : Nat.card A < 2 ^ m) :
    PlusMinusDavenportAtMost A m := by
  intro s hs
  let subsetSum : Finset (Occurrence s) → A :=
    fun I => ∑ i ∈ I, occurrenceValue s i
  have hnotInjective : ¬ Function.Injective subsetSum := by
    intro hinjective
    have hle := Fintype.card_le_of_injective subsetSum hinjective
    have hle' : 2 ^ m ≤ Nat.card A := by
      simpa [hs, Nat.card_eq_fintype_card] using hle
    exact (Nat.not_le_of_lt hcard) hle'
  obtain ⟨I, J, hsum, hne⟩ := Function.not_injective_iff.mp hnotInjective
  let P := I \ J
  let N := J \ I
  let U := P ∪ N
  have hU : U.Nonempty := by
    by_contra hUempty
    have hno : ∀ i, ¬ (i ∈ I ∧ i ∉ J ∨ i ∈ J ∧ i ∉ I) := by
      intro i hi
      apply hUempty
      refine ⟨i, ?_⟩
      rcases hi with hi | hi
      · simp [U, P, N, hi.1, hi.2]
      · simp [U, P, N, hi.1, hi.2]
    apply hne
    ext i
    by_contra hdifferent
    apply hno i
    simp only [not_iff] at hdifferent
    tauto
  have hPN : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    have hiNotJ : i ∉ J := (Finset.mem_sdiff.mp (by simpa [P] using hiP)).2
    exact hiNotJ (Finset.mem_sdiff.mp (by simpa [N] using hiN)).1
  have hsumPN :
      (∑ i ∈ P, occurrenceValue s i) =
        ∑ i ∈ N, occurrenceValue s i := by
    apply add_left_cancel (a := ∑ i ∈ I ∩ J, occurrenceValue s i)
    calc
      (∑ i ∈ I ∩ J, occurrenceValue s i) +
          ∑ i ∈ P, occurrenceValue s i =
          ∑ i ∈ I, occurrenceValue s i := by
            simpa [P] using I.sum_inter_add_sum_sdiff J (occurrenceValue s)
      _ = ∑ i ∈ J, occurrenceValue s i := hsum
      _ = (∑ i ∈ I ∩ J, occurrenceValue s i) +
          ∑ i ∈ N, occurrenceValue s i := by
            simpa [N, Finset.inter_comm] using
              (J.sum_inter_add_sum_sdiff I (occurrenceValue s)).symm
  refine ⟨U, hU, fun i => if i ∈ P then .positive else .negative, ?_⟩
  rw [Finset.sum_union hPN]
  have hpos :
      (∑ i ∈ P,
          (if i ∈ P then PlusMinusSign.positive else PlusMinusSign.negative).act
            (occurrenceValue s i)) =
        ∑ i ∈ P, occurrenceValue s i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi, PlusMinusSign.act]
  have hneg :
      (∑ i ∈ N,
          (if i ∈ P then PlusMinusSign.positive else PlusMinusSign.negative).act
            (occurrenceValue s i)) =
        -(∑ i ∈ N, occurrenceValue s i) := by
    calc
      (∑ i ∈ N,
          (if i ∈ P then PlusMinusSign.positive else PlusMinusSign.negative).act
            (occurrenceValue s i)) =
          ∑ i ∈ N, -(occurrenceValue s i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiP : i ∉ P := by
              intro hi'
              exact Finset.disjoint_left.mp hPN hi' hi
            simp [hiP, PlusMinusSign.act]
      _ = -(∑ i ∈ N, occurrenceValue s i) := by
        rw [Finset.sum_neg_distrib]
  rw [hpos, hneg, hsumPN, add_neg_cancel]

end BinarySubsetSums

private theorem zmod3sq_triple_hasNonemptyPlusMinusZeroSum
    (x y z : Fin 2 → ZMod 3) :
    HasNonemptyPlusMinusZeroSum [x, y, z] := by
  let v : Fin 3 → (Fin 2 → ZMod 3) :=
    fun i => occurrenceValue [x, y, z] i
  have hdep : ¬ LinearIndependent (ZMod 3) v := by
    intro h
    have hcard := h.fintype_card_le_finrank
    norm_num [v] at hcard
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let I : Selection [x, y, z] := Finset.univ.filter fun i => g i ≠ 0
  have hcoeff (i : Fin 3) (hi : g i ≠ 0) : g i = 1 ∨ g i = -1 := by
    generalize ha : g i = a
    fin_cases a
    · exact (hi ha).elim
    · exact Or.inl rfl
    · right
      change (2 : ZMod 3) = -1
      decide
  refine ⟨I, ⟨i₀, by simp [I, hi₀]⟩,
    fun i => if g i = 1 then .positive else .negative, ?_⟩
  calc
    (∑ i ∈ I,
        (if g i = 1 then PlusMinusSign.positive else PlusMinusSign.negative).act
          (occurrenceValue [x, y, z] i)) =
        ∑ i ∈ I, g i • v i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : g i ≠ 0 := by simpa [I] using hi
      rcases hcoeff i hi0 with hpos | hneg
      · simp [hpos, PlusMinusSign.act, v]
      · have hne : (-1 : ZMod 3) ≠ 1 := by decide
        simp [hneg, hne, PlusMinusSign.act, v]
    _ = ∑ i, g i • v i := by
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i _ hi
      have hzero : g i = 0 := by
        by_contra hne
        exact hi (by simp [I, hne])
      simp [hzero]
    _ = 0 := hg

theorem zmod3sq_plusMinusDavenportAtMost_three :
    PlusMinusDavenportAtMost (Fin 2 → ZMod 3) 3 := by
  intro s hs
  match s with
  | [x, y, z] => exact zmod3sq_triple_hasNonemptyPlusMinusZeroSum x y z
  | [] => simp at hs
  | [_] => simp at hs
  | [_, _] => simp at hs
  | _ :: _ :: _ :: _ :: _ => simp at hs

/-- The elementary numerical inequality behind the binary-subset-sum proof. -/
private theorem sq_lt_two_pow_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    n ^ 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      calc
        (n + 1) ^ 2 < 2 * n ^ 2 := by nlinarith
        _ < 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Manuscript-internal rank-two bound `D_±(F_q²) ≤ q` for odd prime
`q`.  The proof is self-contained: binary subset sums for `q ≥ 5`, and a
three-vector linear-dependence proof for the exceptional prime `q = 3`. -/
theorem primeRankTwo_plusMinusDavenportAtMost
    (q : ℕ) (hq : Nat.Prime q) (hqodd : Odd q) :
    PlusMinusDavenportAtMost (Fin 2 → ZMod q) q := by
  by_cases hq3 : q = 3
  · subst q
    exact zmod3sq_plusMinusDavenportAtMost_three
  · letI : NeZero q := ⟨hq.ne_zero⟩
    apply plusMinusDavenportAtMost_of_natCard_lt_two_pow
    have hq2 : q ≠ 2 := by
      intro h
      subst q
      norm_num at hqodd
    have hq4 : q ≠ 4 := by
      intro h
      subst q
      norm_num at hq
    have hq5 : 5 ≤ q := by
      have := hq.two_le
      omega
    have hpow := sq_lt_two_pow_of_five_le hq5
    simpa [Nat.card_eq_fintype_card, hq.ne_zero] using hpow

/-- Cardinality-only form of the rank-two estimate needed for an arbitrary
two-dimensional subgroup inside `F_q^3`.  The manuscript only needs the
weaker bound `D_±(K) ≤ 2q-1`; binary subset-sum collision proves it without
choosing coordinates on `K`. -/
theorem squareCard_plusMinusDavenportAtMost_two_mul_sub_one
    {K : Type*} [AddCommGroup K] [Fintype K]
    (q : ℕ) (hq : Nat.Prime q) (hqodd : Odd q)
    (hKcard : Nat.card K = q ^ 2) :
    PlusMinusDavenportAtMost K (2 * q - 1) := by
  apply plusMinusDavenportAtMost_of_natCard_lt_two_pow
  rw [hKcard]
  have hq3 : 3 ≤ q := by
    by_contra h
    have hq2 := hq.two_le
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  by_cases hq3eq : q = 3
  · subst q
    norm_num
  · have hq5 : 5 ≤ q := by
      have hq4 : q ≠ 4 := by
        intro h
        subst q
        norm_num at hq
      omega
    have hsquare : q ^ 2 < 2 ^ q := by
      exact sq_lt_two_pow_of_five_le hq5
    exact hsquare.trans_le (Nat.pow_le_pow_right (by omega) (by omega))

end GaoLean

#print axioms GaoLean.plusMinusDavenportAtMost_of_natCard_lt_two_pow
#print axioms GaoLean.plusMinusDavenportAtMost_natCard
#print axioms GaoLean.zmod3sq_plusMinusDavenportAtMost_three
#print axioms GaoLean.primeRankTwo_plusMinusDavenportAtMost
#print axioms GaoLean.squareCard_plusMinusDavenportAtMost_two_mul_sub_one
