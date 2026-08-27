import GaoLean.Sequence
import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import MiscYD.AddCombi.Kneser.Kneser

/-!
# Audited additive-combinatorics foundations for GMO

The frozen manuscript invokes the Grynkiewicz--Marchan--Ordaz theorem, whose
published proof uses Kneser's addition theorem and exact zero-sum results.
This file exposes the two available kernel-checked foundations in the
project's occurrence-labelled vocabulary.  It does not claim GMO itself.
-/

namespace GaoLean

open scoped BigOperators Pointwise

/-- Kneser's addition theorem, re-exported at the exact finite-set boundary
needed by the later GMO setpartition layer. -/
theorem finset_add_kneser
    {A : Type*} [AddCommGroup A] [DecidableEq A]
    (s t : Finset A) :
    (s + (s + t).addStab).card + (t + (s + t).addStab).card ≤
      (s + t).card + (s + t).addStab.card :=
  Finset.add_kneser s t

/-- The Erdős--Ginzburg--Ziv theorem for a list over `ZMod n`, expressed as
an exact selection of source occurrences.  Equal values at different source
positions remain distinct. -/
theorem exists_zmod_zeroSum_selection_of_erdosGinzburgZiv
    {n : ℕ} (xs : List (ZMod n))
    (hlen : 2 * n - 1 ≤ xs.length) :
    ∃ I : Selection xs,
      I.card = n ∧
        ∑ i ∈ I, occurrenceValue xs i = 0 := by
  classical
  obtain ⟨I, -, hcard, hsum⟩ :=
    ZMod.erdos_ginzburg_ziv
      (s := Finset.univ) (fun i : Occurrence xs ↦ occurrenceValue xs i) (by
        simpa using hlen)
  exact ⟨I, hcard, hsum⟩

/-- Iterated occurrence-labelled EGZ: from `(t+1)n-1` labelled terms over
`ZMod n`, choose exactly `t*n` of them with sum zero.  This is the precise
multiple-of-the-group-order form used by the ordinary low-reflection channel
when the kernel is cyclic. -/
theorem exists_zmod_zeroSum_finset_of_card_mul
    {ι : Type*} {n : ℕ} (a : ι → ZMod n)
    (s : Finset ι) (t : ℕ)
    (hlen : (t + 1) * n - 1 ≤ s.card) :
    ∃ I ⊆ s, I.card = t * n ∧ ∑ i ∈ I, a i = 0 := by
  classical
  obtain rfl | hn := n.eq_zero_or_pos
  · exact ⟨∅, by simp⟩
  induction t with
  | zero => exact ⟨∅, by simp⟩
  | succ t ih =>
      have hlen' : (t + 2) * n - 1 ≤ s.card := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hlen
      have hprev : (t + 1) * n - 1 ≤ s.card :=
        (Nat.sub_le_sub_right
          (Nat.mul_le_mul_right n (by omega : t + 1 ≤ t + 2)) 1).trans hlen'
      obtain ⟨I, hIs, hIcard, hIsum⟩ := ih hprev
      have hremcard : 2 * n - 1 ≤ (s \ I).card := by
        rw [Finset.card_sdiff_of_subset hIs, hIcard]
        apply Nat.le_sub_of_add_le
        calc
          2 * n - 1 + t * n = (t + 2) * n - 1 := by
            rw [show (t + 2) * n = t * n + 2 * n by ring]
            omega
          _ ≤ s.card := hlen'
      obtain ⟨J, hJrem, hJcard, hJsum⟩ :=
        ZMod.erdos_ginzburg_ziv (s := s \ I) a hremcard
      have hIJ : Disjoint I J := by
        exact Finset.disjoint_left.mpr fun i hiI hiJ ↦
          (Finset.mem_sdiff.mp (hJrem hiJ)).2 hiI
      refine ⟨I ∪ J, Finset.union_subset hIs (hJrem.trans Finset.sdiff_subset), ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hIJ, hIcard, hJcard]
        simp [Nat.succ_mul]
      · rw [Finset.sum_union hIJ, hIsum, hJsum, add_zero]

/-- List/selection form of the iterated cyclic EGZ theorem. -/
theorem exists_zmod_zeroSum_selection_of_card_mul
    {n : ℕ} (xs : List (ZMod n)) (t : ℕ)
    (hlen : (t + 1) * n - 1 ≤ xs.length) :
    ∃ I : Selection xs,
      I.card = t * n ∧ ∑ i ∈ I, occurrenceValue xs i = 0 := by
  classical
  obtain ⟨I, -, hcard, hsum⟩ :=
    exists_zmod_zeroSum_finset_of_card_mul
      (fun i : Occurrence xs ↦ occurrenceValue xs i) Finset.univ t (by
        simpa using hlen)
  exact ⟨I, hcard, hsum⟩

end GaoLean

#print axioms GaoLean.finset_add_kneser
#print axioms GaoLean.exists_zmod_zeroSum_selection_of_erdosGinzburgZiv
#print axioms GaoLean.exists_zmod_zeroSum_selection_of_card_mul
