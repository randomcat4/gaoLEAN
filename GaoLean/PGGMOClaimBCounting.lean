import GaoLean.PGGMOClaimBCore
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The upstream counting step in ordinary GMO Claim B

This module formalizes the counting argument in Section 5, Case 1, of
Grynkiewicz--Marchan--Ordaz.  In particular it derives paper equation (10)
from the source-faithful Theorem E lower bound and the failure of the large
alternative, and then proves the required two-cell pigeonhole conclusion.

The fibers below count the value sets `Aᵢ`, not source occurrences.  The
occurrence/value correspondence from `PGGMOClaimBCore` remains available,
but is not substituted for the value-set count in this argument.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A setpartition into `n` nonempty cells has replacement length at least
`n`. -/
theorem Theorem21SetPartition.numCells_le_length
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) :
    n ≤ m := by
  classical
  have hmass := length_le_sum_layer_card P.valueCells P.valueCells_nonempty
  rw [P.length_valueCells] at hmass
  simpa [Theorem21SetPartition.valueCells, List.map_ofFn,
    List.sum_ofFn, P.sum_card_valueCell] using hmass

/-- Paper equation (10), with `N = commonCosetCount H` and
`e = exceptionDefect H`.  The upper bound is obtained solely from failure
of Theorem 2.1's literal large alternative. -/
theorem GMOTheoremESourceOutput.claimB_equation10_of_not_large
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hN : 2 ≤ out.partition.commonCosetCount out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    (((out.partition.commonCosetCount out.H - 1) * n +
          out.partition.exceptionDefect out.H + 1) * Nat.card out.H ≤
        seed.card - n) := by
  have hnotBound :
      ¬ min (Nat.card A) (seed.card - n + 1) ≤
          out.partition.sumset.card := by
    intro h
    exact hnotLarge ⟨h⟩
  have hstrict :
      out.partition.sumset.card < seed.card - n + 1 :=
    (Nat.lt_of_not_ge hnotBound).trans_le
      (min_le_right (Nat.card A) (seed.card - n + 1))
  have hupper : out.partition.sumset.card ≤ seed.card - n := by
    omega
  have hNdecomp : out.partition.commonCosetCount out.H =
      (out.partition.commonCosetCount out.H - 1) + 1 := by
    omega
  have hcoeff :
      ((out.partition.commonCosetCount out.H * n +
          out.partition.exceptionDefect out.H + 1) - n) =
        (out.partition.commonCosetCount out.H - 1) * n +
          out.partition.exceptionDefect out.H + 1 := by
    calc
      ((out.partition.commonCosetCount out.H * n +
          out.partition.exceptionDefect out.H + 1) - n) =
          ((((out.partition.commonCosetCount out.H - 1) + 1) * n +
            out.partition.exceptionDefect out.H + 1) - n) :=
        congrArg
          (fun t : ℕ ↦
            ((t * n + out.partition.exceptionDefect out.H + 1) - n))
          hNdecomp
      _ = (out.partition.commonCosetCount out.H - 1) * n +
          out.partition.exceptionDefect out.H + 1 := by
        simp only [Nat.add_mul, one_mul]
        have hreorder :
            (out.partition.commonCosetCount out.H - 1) * n + n +
                out.partition.exceptionDefect out.H + 1 =
              n + ((out.partition.commonCosetCount out.H - 1) * n +
                out.partition.exceptionDefect out.H + 1) := by
          omega
        rw [hreorder, Nat.add_sub_cancel_left]
  have hlower := out.card_lower
  rw [hcoeff] at hlower
  exact hlower.trans hupper

/-- Periodicity identifies the number of quotient fibers of the common core
with the source parameter `N`, without any floor loss. -/
theorem Theorem21SetPartition.card_quotientLayer_commonCore_eq_commonCosetCount
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (quotientLayer H (P.commonCore H)).card = P.commonCosetCount H := by
  have hcore := P.card_commonCore_eq_commonCosetCount_mul_natCard H
  have hlayer := P.card_commonCore_eq_natCard_mul_quotientLayer H
  have hmul :
      Nat.card H * (quotientLayer H (P.commonCore H)).card =
        Nat.card H * P.commonCosetCount H := by
    calc
      Nat.card H * (quotientLayer H (P.commonCore H)).card =
          (P.commonCore H).card := hlayer.symm
      _ = P.commonCosetCount H * Nat.card H := hcore
      _ = Nat.card H * P.commonCosetCount H := Nat.mul_comm _ _
  exact Nat.mul_left_cancel Nat.card_pos hmul

/-- On a common-core quotient class, membership in a value-cell fiber is
equivalent to membership in the corresponding filtered common-core part. -/
theorem Theorem21SetPartition.mem_coreValueCell_and_quotient_iff_cosetValueSlice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H)
    (hq : q ∈ quotientLayer H (P.commonCore H)) (x : A) :
    (x ∈ P.coreValueCell H c ∧ QuotientAddGroup.mk' H x = q) ↔
      x ∈ P.cosetValueSlice H c q := by
  classical
  constructor
  · intro hx
    exact (P.mem_cosetValueSlice_iff H c q x).2
      ⟨(P.mem_coreValueCell_iff H c x).1 hx.1 |>.1, hx.2⟩
  · intro hx
    have hx' := (P.mem_cosetValueSlice_iff H c q x).1 hx
    have hxLayer : QuotientAddGroup.mk' H x ∈
        quotientLayer H (P.commonCore H) := by
      simpa [hx'.2] using hq
    have hxCore : x ∈ P.commonCore H :=
      (mem_quotientLayer_iff_of_le_stabilizer H (P.commonCore H)
        (P.commonCore_periodic H) x).1 hxLayer
    exact ⟨(P.mem_coreValueCell_iff H c x).2
      ⟨hx'.1, hxCore⟩, hx'.2⟩

/-- The common quotient fibers of one value cell sum exactly to that
cell's common-core cardinality. -/
theorem Theorem21SetPartition.sum_card_cosetValueSlice_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    (∑ q ∈ quotientLayer H (P.commonCore H),
        (P.cosetValueSlice H c q).card) =
      (P.coreValueCell H c).card := by
  classical
  have hmaps : Set.MapsTo
      (fun x : A ↦ QuotientAddGroup.mk' H x)
      (↑(P.coreValueCell H c) : Set A)
      (↑(quotientLayer H (P.commonCore H)) : Set (A ⧸ H)) := by
    intro x hx
    have hxCore := (P.mem_coreValueCell_iff H c x).1 hx |>.2
    exact (mem_quotientLayer_iff H (P.commonCore H) _).2
      ⟨x, hxCore, rfl⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := P.coreValueCell H c)
    (t := quotientLayer H (P.commonCore H))
    (f := fun x : A ↦ QuotientAddGroup.mk' H x) hmaps
  have hfilter : ∀ q ∈ quotientLayer H (P.commonCore H),
      (P.coreValueCell H c).filter
          (fun x ↦ QuotientAddGroup.mk' H x = q) =
        P.cosetValueSlice H c q := by
    intro q hq
    ext x
    simpa only [Finset.mem_filter] using
      (P.mem_coreValueCell_and_quotient_iff_cosetValueSlice H c q hq x)
  calc
    (∑ q ∈ quotientLayer H (P.commonCore H),
        (P.cosetValueSlice H c q).card) =
        ∑ q ∈ quotientLayer H (P.commonCore H),
          ((P.coreValueCell H c).filter
            (fun x ↦ QuotientAddGroup.mk' H x = q)).card := by
          apply Finset.sum_congr rfl
          intro q hq
          exact congrArg Finset.card
            (hfilter q hq).symm
    _ = (P.coreValueCell H c).card := hfiber.symm

/-- A cyclic reindexing has no fixed cell as soon as there are at least two
cells. -/
theorem finRotate_ne_self_of_two_le
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro hi
  cases n with
  | zero => omega
  | succ k =>
      have hval := congrArg Fin.val hi
      rw [coe_finRotate] at hval
      by_cases hilast : i = Fin.last k
      · simp [hilast] at hval
        omega
      · simp [hilast] at hval

/-- Finite two-cell averaging.  Pair every cell with its cyclic successor;
the successor permutation preserves the sum and has no fixed point. -/
theorem two_mul_sum_le_of_pairwise_two_sum_le
    {n h : ℕ} (hn : 2 ≤ n) (a : Fin n → ℕ)
    (hpair : ∀ j k : Fin n, j ≠ k → a j + a k ≤ h) :
    2 * (∑ j : Fin n, a j) ≤ n * h := by
  classical
  let sigma : Equiv.Perm (Fin n) := finRotate n
  have hpoint : ∀ j : Fin n, a j + a (sigma j) ≤ h := by
    intro j
    exact hpair j (sigma j) (finRotate_ne_self_of_two_le hn j).symm
  have hsum :
      (∑ j : Fin n, (a j + a (sigma j))) ≤
        ∑ _j : Fin n, h :=
    Finset.sum_le_sum fun j _ ↦ hpoint j
  have hsigma : (∑ j : Fin n, a (sigma j)) = ∑ j : Fin n, a j := by
    exact sigma.sum_comp (Finset.univ : Finset (Fin n)) a (by simp)
  rw [Finset.sum_add_distrib, hsigma] at hsum
  simpa [two_mul, Nat.mul_comm] using hsum

/-- If every pair of distinct value cells is small in every common quotient
fiber, the total common-core mass satisfies the paper's pigeonhole upper
bound `2 * coreMass ≤ N n |H|`. -/
theorem Theorem21SetPartition.two_mul_sum_card_coreValueCell_le_of_pairwise
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (hn : 2 ≤ n)
    (hpair : ∀ q ∈ quotientLayer H (P.commonCore H),
      ∀ j k : Fin n, j ≠ k →
        (P.cosetValueSlice H j q).card +
            (P.cosetValueSlice H k q).card ≤ Nat.card H) :
    2 * (∑ c : Fin n, (P.coreValueCell H c).card) ≤
      (quotientLayer H (P.commonCore H)).card * (n * Nat.card H) := by
  classical
  have hfiber : ∀ q ∈ quotientLayer H (P.commonCore H),
      2 * (∑ c : Fin n, (P.cosetValueSlice H c q).card) ≤
        n * Nat.card H := by
    intro q hq
    exact two_mul_sum_le_of_pairwise_two_sum_le hn
      (fun c ↦ (P.cosetValueSlice H c q).card)
      (hpair q hq)
  have hsum := Finset.sum_le_sum hfiber
  have hleft :
      2 * (∑ c : Fin n, (P.coreValueCell H c).card) =
        ∑ q ∈ quotientLayer H (P.commonCore H),
          2 * (∑ c : Fin n, (P.cosetValueSlice H c q).card) := by
    calc
      2 * (∑ c : Fin n, (P.coreValueCell H c).card) =
          2 * (∑ c : Fin n,
            ∑ q ∈ quotientLayer H (P.commonCore H),
              (P.cosetValueSlice H c q).card) := by
            congr 1
            apply Finset.sum_congr rfl
            intro c _
            exact (P.sum_card_cosetValueSlice_commonCore H c).symm
      _ = ∑ q ∈ quotientLayer H (P.commonCore H),
          2 * (∑ c : Fin n, (P.cosetValueSlice H c q).card) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
  rw [← hleft] at hsum
  simpa [Nat.mul_comm] using hsum

/-- Section 5, Case 1, upstream conclusion: in the non-large branch with
`N ≥ 2`, one common-core quotient class contains two distinct value cells
whose fiber cardinalities sum to at least `|H| + 1`. -/
theorem GMOTheoremESourceOutput.exists_commonCore_two_cells_large_slice
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hn : 2 ≤ n)
    (hN : 2 ≤ out.partition.commonCosetCount out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    ∃ g ∈ out.partition.commonCore out.H,
      ∃ j k : Fin n, j ≠ k ∧
        Nat.card out.H + 1 ≤
          (out.partition.cosetValueSlice out.H j
              (QuotientAddGroup.mk' out.H g)).card +
            (out.partition.cosetValueSlice out.H k
              (QuotientAddGroup.mk' out.H g)).card := by
  classical
  by_contra hconclusion
  have hpair :
      ∀ q ∈ quotientLayer out.H
          (out.partition.commonCore out.H),
        ∀ j k : Fin n, j ≠ k →
          (out.partition.cosetValueSlice out.H j q).card +
              (out.partition.cosetValueSlice out.H k q).card ≤
            Nat.card out.H := by
    intro q hq j k hjk
    by_contra hsmall
    have hlarge : Nat.card out.H + 1 ≤
        (out.partition.cosetValueSlice out.H j q).card +
          (out.partition.cosetValueSlice out.H k q).card := by
      omega
    obtain ⟨g, hg, hgq⟩ :=
      (mem_quotientLayer_iff out.H
        (out.partition.commonCore out.H) q).1 hq
    apply hconclusion
    refine ⟨g, hg, j, k, hjk, ?_⟩
    simpa [hgq] using hlarge
  have havg :=
    out.partition.two_mul_sum_card_coreValueCell_le_of_pairwise
      out.H hn hpair
  have hQcard :=
    out.partition.card_quotientLayer_commonCore_eq_commonCosetCount out.H
  rw [hQcard] at havg
  have havg' :
      2 * (∑ c : Fin n,
          (out.partition.coreValueCell out.H c).card) ≤
        out.partition.commonCosetCount out.H * n * Nat.card out.H := by
    simpa [Nat.mul_assoc] using havg
  have hledger :=
    out.partition.sum_card_coreValueCell_add_exceptionDefect out.H
  have hseedAverage :
      2 * seed.card ≤
        out.partition.commonCosetCount out.H * n * Nat.card out.H +
          2 * out.partition.exceptionDefect out.H := by
    calc
      2 * seed.card =
          2 * ((∑ c : Fin n,
            (out.partition.coreValueCell out.H c).card) +
              out.partition.exceptionDefect out.H) :=
        congrArg (fun t : ℕ ↦ 2 * t) hledger.symm
      _ = 2 * (∑ c : Fin n,
            (out.partition.coreValueCell out.H c).card) +
          2 * out.partition.exceptionDefect out.H := by omega
      _ ≤ out.partition.commonCosetCount out.H * n * Nat.card out.H +
          2 * out.partition.exceptionDefect out.H :=
        Nat.add_le_add_right havg'
          (2 * out.partition.exceptionDefect out.H)
  have heq10 := out.claimB_equation10_of_not_large hN hnotLarge
  let N := out.partition.commonCosetCount out.H
  let e := out.partition.exceptionDefect out.H
  let h := Nat.card out.H
  let M := N - 1
  have hN' : 2 ≤ N := hN
  have hM : 1 ≤ M := by
    dsimp [M]
    omega
  have hNdecomp : N = M + 1 := by
    dsimp [M]
    omega
  have hlen : n ≤ seed.card := out.partition.numCells_le_length
  have hweakCoeff : (M * n + e) * h ≤ (M * n + e + 1) * h := by
    exact Nat.mul_le_mul_right h (Nat.le_succ _)
  have heq10' : (M * n + e + 1) * h ≤ seed.card - n := by
    simpa [N, e, h, M] using heq10
  have hbaseSub : (M * n + e) * h ≤ seed.card - n :=
    hweakCoeff.trans heq10'
  have hbase : (M * n + e) * h + n ≤ seed.card := by
    omega
  have hseedAverage' : 2 * seed.card ≤ N * n * h + 2 * e := by
    simpa [N, e, h] using hseedAverage
  have hcombined :
      2 * ((M * n + e) * h + n) ≤ N * n * h + 2 * e :=
    (Nat.mul_le_mul_left 2 hbase).trans hseedAverage'
  rw [hNdecomp] at hcombined
  ring_nf at hcombined
  have hmn : n ≤ M * n := by
    simpa using Nat.mul_le_mul_right n hM
  have hMnh : n * h ≤ M * n * h :=
    Nat.mul_le_mul_right h hmn
  have heh : e ≤ e * h := by
    have hhpos : 1 ≤ h := by
      dsimp [h]
      exact Nat.card_pos
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left e hhpos
  omega

/-- A quotient slice represented by `g` is literally the intersection with
the additive coset `g + H`. -/
theorem Theorem21SetPartition.cosetValueSlice_mk_eq_inter_addCosetFinset
    [DecidableEq A]
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (g : A) :
    P.cosetValueSlice H c (QuotientAddGroup.mk' H g) =
      P.valueCell c ∩ addCosetFinset H g := by
  classical
  ext x
  simp [Theorem21SetPartition.cosetValueSlice,
    mem_addCosetFinset_iff, QuotientAddGroup.eq_iff_sub_mem]

/-- Literal source notation for the preceding theorem:
`|A_k ∩ (g+H)| + |A_j ∩ (g+H)| ≥ |H|+1`. -/
theorem GMOTheoremESourceOutput.exists_commonCore_two_cells_large_intersection
    [DecidableEq A]
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hn : 2 ≤ n)
    (hN : 2 ≤ out.partition.commonCosetCount out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    ∃ g ∈ out.partition.commonCore out.H,
      ∃ j k : Fin n, j ≠ k ∧
        Nat.card out.H + 1 ≤
          (out.partition.valueCell j ∩ addCosetFinset out.H g).card +
            (out.partition.valueCell k ∩ addCosetFinset out.H g).card := by
  obtain ⟨g, hg, j, k, hjk, hcard⟩ :=
    out.exists_commonCore_two_cells_large_slice hn hN hnotLarge
  refine ⟨g, hg, j, k, hjk, ?_⟩
  simpa only [out.partition.cosetValueSlice_mk_eq_inter_addCosetFinset]
    using hcard

end GaoLean

#print axioms GaoLean.GMOTheoremESourceOutput.claimB_equation10_of_not_large
#print axioms GaoLean.Theorem21SetPartition.sum_card_cosetValueSlice_commonCore
#print axioms GaoLean.GMOTheoremESourceOutput.exists_commonCore_two_cells_large_slice
#print axioms GaoLean.GMOTheoremESourceOutput.exists_commonCore_two_cells_large_intersection
