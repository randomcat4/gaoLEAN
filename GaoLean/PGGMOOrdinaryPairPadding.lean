import GaoLean.PGGMOOrdinaryStep1

/-!
# Fixed-cardinality padding from a disjoint zero reserve

This module isolates the labelled padding argument used after a target sum
has already been realized inside a pool.  Starting from a witness `I` in the
pool, the maximal zero-sum construction is applied only to `pool \ I`.  Its
zero-valued reserve padding is therefore disjoint from `I`, and their union
has exactly the cardinality of the original pool while retaining the target
sum.
-/

namespace GaoLean

open scoped BigOperators

universe u v

variable {X : Type v} [Fintype X] [DecidableEq X]
variable {B : Type u} [AddCommGroup B]

/-- Extend one labelled target-sum witness in `pool` to a witness having
exactly `pool.card` labels.  The additional labels are a zero-sum block built
from the unused part of the pool and the disjoint zero reserve. -/
theorem exists_fixedCard_sum_eq_of_pool_witness
    (pool reserve : Finset X) (f : X → B) (D : ℕ)
    (hD : OrdinaryDavenportAtMost B D)
    (hdis : Disjoint pool reserve)
    (hreserveZero : ∀ x ∈ reserve, f x = 0)
    (hreserveCard : D - 1 ≤ reserve.card)
    (y : B) (I : Finset X)
    (hIpool : I ⊆ pool) (hIsum : (∑ x ∈ I, f x) = y) :
    ∃ T : Finset X,
      T ⊆ pool ∪ reserve ∧ T.card = pool.card ∧
        (∑ x ∈ T, f x) = y := by
  classical
  have hremainingReserve : Disjoint (pool \ I) reserve :=
    hdis.mono_left Finset.sdiff_subset
  obtain ⟨Z, hZsub, hZcard, hZsum⟩ :=
    exists_zeroSum_padded_selection (pool \ I) reserve f D
      hD hremainingReserve hreserveZero hreserveCard
  have hIZ : Disjoint I Z := by
    rw [Finset.disjoint_left]
    intro x hxI hxZ
    rcases Finset.mem_union.mp (hZsub hxZ) with hxRemaining | hxReserve
    · exact (Finset.mem_sdiff.mp hxRemaining).2 hxI
    · exact (Finset.disjoint_left.mp hdis) (hIpool hxI) hxReserve
  refine ⟨I ∪ Z, ?_, ?_, ?_⟩
  · apply Finset.union_subset
    · exact hIpool.trans Finset.subset_union_left
    · intro x hxZ
      rcases Finset.mem_union.mp (hZsub hxZ) with hxRemaining | hxReserve
      · exact Finset.mem_union_left reserve (Finset.mem_sdiff.mp hxRemaining).1
      · exact Finset.mem_union_right pool hxReserve
  · rw [Finset.card_union_of_disjoint hIZ, hZcard,
      Finset.card_sdiff_of_subset hIpool]
    exact Nat.add_sub_of_le (Finset.card_le_card hIpool)
  · rw [Finset.sum_union hIZ, hIsum, hZsum, add_zero]

/-- If every value is represented by a labelled subset of `pool`, then every
value is represented on exactly `pool.card` labels drawn from the pool and
the zero reserve. -/
theorem forall_exists_fixedCard_sum_eq_of_pool
    (pool reserve : Finset X) (f : X → B) (D : ℕ)
    (hD : OrdinaryDavenportAtMost B D)
    (hdis : Disjoint pool reserve)
    (hreserveZero : ∀ x ∈ reserve, f x = 0)
    (hreserveCard : D - 1 ≤ reserve.card)
    (hcover : ∀ y : B, ∃ I : Finset X,
      I ⊆ pool ∧ (∑ x ∈ I, f x) = y) :
    ∀ y : B, ∃ T : Finset X,
      T ⊆ pool ∪ reserve ∧ T.card = pool.card ∧
        (∑ x ∈ T, f x) = y := by
  intro y
  obtain ⟨I, hIpool, hIsum⟩ := hcover y
  exact exists_fixedCard_sum_eq_of_pool_witness pool reserve f D
    hD hdis hreserveZero hreserveCard y I hIpool hIsum

/-- Finite-target version: it is enough that the original pool realizes the
values in `targets`. -/
theorem forall_mem_exists_fixedCard_sum_eq_of_pool
    (pool reserve : Finset X) (f : X → B) (D : ℕ)
    (hD : OrdinaryDavenportAtMost B D)
    (hdis : Disjoint pool reserve)
    (hreserveZero : ∀ x ∈ reserve, f x = 0)
    (hreserveCard : D - 1 ≤ reserve.card)
    (targets : Finset B)
    (hcover : ∀ y ∈ targets, ∃ I : Finset X,
      I ⊆ pool ∧ (∑ x ∈ I, f x) = y) :
    ∀ y ∈ targets, ∃ T : Finset X,
      T ⊆ pool ∪ reserve ∧ T.card = pool.card ∧
        (∑ x ∈ T, f x) = y := by
  intro y hy
  obtain ⟨I, hIpool, hIsum⟩ := hcover y hy
  exact exists_fixedCard_sum_eq_of_pool_witness pool reserve f D
    hD hdis hreserveZero hreserveCard y I hIpool hIsum

end GaoLean

#print axioms GaoLean.exists_fixedCard_sum_eq_of_pool_witness
#print axioms GaoLean.forall_exists_fixedCard_sum_eq_of_pool
#print axioms GaoLean.forall_mem_exists_fixedCard_sum_eq_of_pool
