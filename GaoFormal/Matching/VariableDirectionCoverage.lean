import GaoFormal.Matching.AffineReverse
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Variable-direction quotient coverage

The hyperplane full-exchange branch supplies `q - 1` labelled cross pairs.
Their quotient increments need not be equal; it is enough that every one is
nonzero.  This file formalizes the Cauchy--Davenport coverage step while
retaining the index labels of repeated increments.
-/

namespace GaoFormal

open scoped BigOperators Pointwise

variable {q : ℕ} [NeZero q] [Fact q.Prime]

/-- All subset sums of an indexed family over a finite label set.  The domain
labels, rather than the values, are put in the powerset, so repeated values
remain independently selectable. -/
noncomputable def labelledSubsetSums {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (inc : ι → ZMod q) : Finset (ZMod q) :=
  A.powerset.image fun T => ∑ i ∈ T, inc i

@[simp] theorem zero_mem_labelledSubsetSums {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (inc : ι → ZMod q) :
    0 ∈ labelledSubsetSums A inc := by
  classical
  refine Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset A), ?_⟩
  simp

/-- Adding one fresh label adds the two-point set `{0, inc a}` to the old
labelled subset-sum set. -/
theorem labelledSubsetSums_insert {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (inc : ι → ZMod q) {a : ι} (ha : a ∉ A) :
    labelledSubsetSums (insert a A) inc =
      labelledSubsetSums A inc + ({0, inc a} : Finset (ZMod q)) := by
  classical
  unfold labelledSubsetSums
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
    have hTsub := Finset.mem_powerset.mp hT
    by_cases haT : a ∈ T
    · let U := T.erase a
      have hUsub : U ⊆ A := by
        intro i hi
        have hiT := Finset.mem_of_mem_erase hi
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        rcases Finset.mem_insert.mp (hTsub hiT) with rfl | hiA
        · exact (hia rfl).elim
        · exact hiA
      have hUsum : (∑ i ∈ T, inc i) = (∑ i ∈ U, inc i) + inc a := by
        rw [show T = insert a U by
          ext i
          simp [U, haT, eq_comm]]
        rw [Finset.sum_insert]
        · abel
        · simp [U]
      rw [hUsum]
      exact Finset.mem_add.mpr ⟨_, Finset.mem_image.mpr
        ⟨U, Finset.mem_powerset.mpr hUsub, rfl⟩, _, by simp, rfl⟩
    · have hTsubA : T ⊆ A := by
        intro i hi
        rcases Finset.mem_insert.mp (hTsub hi) with rfl | hiA
        · exact (haT hi).elim
        · exact hiA
      simpa using (Finset.mem_add.mpr ⟨_, Finset.mem_image.mpr
        ⟨T, Finset.mem_powerset.mpr hTsubA, rfl⟩, 0, by simp, add_zero _⟩)
  · intro hx
    rcases Finset.mem_add.mp hx with ⟨u, hu, v, hv, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨T, hT, rfl⟩
    have hTsub := Finset.mem_powerset.mp hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · refine Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr ?_, by simp⟩
      exact fun i hi => Finset.mem_insert_of_mem (hTsub hi)
    · refine Finset.mem_image.mpr ⟨insert a T, Finset.mem_powerset.mpr ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiT
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hTsub hiT)
      · have haT : a ∉ T := fun haT => ha (hTsub haT)
        rw [Finset.sum_insert haT]
        abel

/-- `q - 1` indexed nonzero increments in the prime cyclic quotient have all
of `ZMod q` as labelled subset sums. -/
theorem exists_labelled_subset_sum_eq_of_nonzero
    (inc : Fin (q - 1) → ZMod q) (hinc : ∀ i, inc i ≠ 0) (a : ZMod q) :
    ∃ T : Finset (Fin (q - 1)), (∑ i ∈ T, inc i) = a := by
  classical
  have hcard : ∀ A : Finset (Fin (q - 1)),
      (∀ i ∈ A, inc i ≠ 0) →
      min q (A.card + 1) ≤ (labelledSubsetSums A inc).card := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        intro _h
        simp [labelledSubsetSums]
    | @insert b A hb ih =>
        intro hnonzero
        have hbzero : inc b ≠ 0 := hnonzero b (Finset.mem_insert_self b A)
        have hA : ∀ i ∈ A, inc i ≠ 0 :=
          fun i hi => hnonzero i (Finset.mem_insert_of_mem hi)
        have hrec := labelledSubsetSums_insert (q := q) A inc hb
        have hcd := ZMod.cauchy_davenport (Fact.out : q.Prime)
          (show (labelledSubsetSums A inc).Nonempty from
            ⟨0, zero_mem_labelledSubsetSums (q := q) A inc⟩)
          (show ({0, inc b} : Finset (ZMod q)).Nonempty by simp)
        rw [← hrec] at hcd
        have hpair : ({0, inc b} : Finset (ZMod q)).card = 2 := by
          rw [Finset.card_insert_of_notMem]
          · simp
          · simp only [Finset.mem_singleton]
            exact fun h => hbzero h.symm
        rw [hpair] at hcd
        have hold := ih hA
        have hleq : (labelledSubsetSums A inc).card ≤ q := by
          simpa using Finset.card_le_univ (labelledSubsetSums A inc)
        simp only [Finset.card_insert_of_notMem hb]
        omega
  have hall := hcard Finset.univ (fun i _hi => hinc i)
  have hqcard : (Finset.univ : Finset (Fin (q - 1))).card + 1 = q := by
    simp
    have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    omega
  rw [hqcard, min_self] at hall
  have hfull : labelledSubsetSums (Finset.univ : Finset (Fin (q - 1))) inc =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    have hle :
        (labelledSubsetSums (Finset.univ : Finset (Fin (q - 1))) inc).card ≤ q := by
      simpa using Finset.card_le_univ
        (labelledSubsetSums (Finset.univ : Finset (Fin (q - 1))) inc)
    have heq :
        (labelledSubsetSums (Finset.univ : Finset (Fin (q - 1))) inc).card = q :=
      Nat.le_antisymm hle hall
    simpa using heq
  have ha : a ∈ labelledSubsetSums (Finset.univ : Finset (Fin (q - 1))) inc := by
    rw [hfull]
    simp
  unfold labelledSubsetSums at ha
  rcases Finset.mem_image.mp ha with ⟨T, _hT, hsum⟩
  exact ⟨T, hsum⟩

end GaoFormal

#print axioms GaoFormal.exists_labelled_subset_sum_eq_of_nonzero
