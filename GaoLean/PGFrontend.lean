import GaoLean.PGStatements
import Mathlib.GroupTheory.OrderOfElement

/-!
# Load-bearing p-group front-end leaves

This file contains unconditional algebra and arithmetic used around the
middle-reflection regime.  It deliberately does not state GMO's prescribed
length theorem or claim that any of its spectrum branches have been produced.
-/

namespace GaoLean

section OddQuotient

variable {B A : Type*} [AddCommGroup B] [Fintype B]

/-- A finite additive group of odd cardinality has no nonzero element killed
by `2`. -/
theorem eq_zero_of_two_nsmul_eq_zero_of_card_odd
    (hcard : Odd (Fintype.card B)) {x : B} (hx : 2 • x = 0) : x = 0 := by
  have hordTwo : addOrderOf x ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero hx
  have hordCard : addOrderOf x ∣ Fintype.card B := addOrderOf_dvd_card
  rcases (Nat.dvd_prime Nat.prime_two).mp hordTwo with hord | hord
  · exact AddMonoid.addOrderOf_eq_one_iff.mp hord
  · exfalso
    have htwoCard : 2 ∣ Fintype.card B := by simpa [hord] using hordCard
    exact (Nat.not_even_iff_odd.mpr hcard) (even_iff_two_dvd.mpr htwoCard)

variable [AddCommGroup A]

/-- If the quotient `A/K` has odd cardinality, membership of `2 • x` in `K`
already forces membership of `x`. -/
theorem mem_of_two_nsmul_mem_of_quotient_card_odd
    (K : AddSubgroup A) [Fintype (A ⧸ K)]
    (hcard : Odd (Fintype.card (A ⧸ K))) {x : A} (hx : 2 • x ∈ K) :
    x ∈ K := by
  let q : A ⧸ K := QuotientAddGroup.mk x
  have hmk : (QuotientAddGroup.mk (2 • x) : A ⧸ K) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hx
  have hq : 2 • q = 0 := by simpa [q] using hmk
  have qzero : q = 0 :=
    eq_zero_of_two_nsmul_eq_zero_of_card_odd hcard hq
  exact (QuotientAddGroup.eq_zero_iff x).1 qzero

/-- The dangerous proper-subgroup entry used after GMO's weighted-coset
output.  The hypotheses are the difference-form versions of
`{x, -x} ⊆ β + K`. -/
theorem mem_of_pos_neg_mem_same_coset_of_quotient_card_odd
    (K : AddSubgroup A) [Fintype (A ⧸ K)]
    (hcard : Odd (Fintype.card (A ⧸ K))) {x β : A}
    (hx : x - β ∈ K) (hneg : -x - β ∈ K) : x ∈ K := by
  have htwo : 2 • x ∈ K := by
    have hsub := K.sub_mem hx hneg
    have heq : (x - β) - (-x - β) = 2 • x := by abel
    rwa [heq] at hsub
  exact mem_of_two_nsmul_mem_of_quotient_card_odd K hcard htwo

end OddQuotient

section MiddleBookkeeping

/-- Largest even number not exceeding `a`; it is the number of reflections
retained in the middle regime. -/
def pairedReflectionCount (a : ℕ) : ℕ := 2 * (a / 2)

/-- Rotation target paired with `pairedReflectionCount`. -/
def middleRotationTarget (Q a : ℕ) : ℕ :=
  2 * Q - pairedReflectionCount a

theorem pairedReflectionCount_even (a : ℕ) :
    Even (pairedReflectionCount a) := by
  refine ⟨a / 2, ?_⟩
  simp [pairedReflectionCount, two_mul]

theorem pairedReflectionCount_bounds {a : ℕ} (ha : 2 ≤ a) :
    2 ≤ pairedReflectionCount a ∧
      pairedReflectionCount a ≤ a ∧
      a ≤ pairedReflectionCount a + 1 := by
  simp only [pairedReflectionCount]
  omega

/-- Complete arithmetic package for the middle regime: the retained
reflection count is positive/even, the rotation target is at least `|A|`, and
the two counts total exactly `2|A|`. -/
theorem middle_target_bookkeeping {Q D a : ℕ}
    (hDQ : D ≤ Q) (ha2 : 2 ≤ a) (haD : a ≤ D) :
    let e := pairedReflectionCount a
    let ell := middleRotationTarget Q a
    Even e ∧ 2 ≤ e ∧ e ≤ a ∧ a ≤ e + 1 ∧
      Q ≤ ell ∧ e + ell = 2 * Q := by
  dsimp only
  have he := pairedReflectionCount_even a
  have hb := pairedReflectionCount_bounds ha2
  simp only [middleRotationTarget]
  refine ⟨he, hb.1, hb.2.1, hb.2.2, ?_, ?_⟩
  · omega
  · apply Nat.add_sub_of_le
    omega

/-- If the ambient sequence has `b = 2Q + D - a` rotations, the middle target
leaves at least `D - 1` surplus rotations.  This is the exact numerical gate
needed before applying a plus-minus prescribed-length theorem. -/
theorem middle_rotation_surplus {Q D a b : ℕ}
    (hDQ : D ≤ Q) (ha2 : 2 ≤ a) (haD : a ≤ D)
    (hb : b = 2 * Q + D - a) :
    middleRotationTarget Q a ≤ b ∧
      D - 1 ≤ b - middleRotationTarget Q a := by
  have hbook := middle_target_bookkeeping hDQ ha2 haD
  dsimp only at hbook
  simp only [middleRotationTarget]
  have hp := pairedReflectionCount_bounds ha2
  omega

/-- The three reflection-count regimes are mutually exhaustive at the level
of inequalities used by the proof. -/
theorem reflection_count_trichotomy (a D : ℕ) :
    a ≤ 1 ∨ D + 1 ≤ a ∨ (2 ≤ a ∧ a ≤ D) := by
  omega

/-- Odd `D` gives the exact number of same-type pairs after leaving the single
unpaired occurrence from an odd total `2Q + D`. -/
theorem same_type_pair_count {Q D a b : ℕ}
    (hD : Odd D) (hab : a + b = 2 * Q + D) :
    a / 2 + b / 2 = Q + (D - 1) / 2 := by
  rcases hD with ⟨d, hd⟩
  omega

/-- In the high-reflection regime there are fewer than `Q` rotation pairs, so
any selection of `Q` same-type pairs must include a reflection pair. -/
theorem selected_pairs_force_reflection {Q rotationPairs selectedPairs : ℕ}
    (hQ : 0 < Q) (hrot : rotationPairs ≤ Q - 1) (hsel : Q ≤ selectedPairs)
    (hallRotation : selectedPairs ≤ rotationPairs) : False := by
  omega

/-- The two inequalities used in the `K = 0` leaf imply that the required
number of identity fillers is nonnegative and available. -/
theorem identity_padding_amount_bounds {Q m0 used : ℕ}
    (hlower : 2 * Q - m0 ≤ used) (hupper : used ≤ 2 * Q) :
    2 * Q - used ≤ m0 := by
  omega

/-- Occurrence-level identity padding: from a disjoint pool of `m0` identity
positions, choose exactly enough fresh labels to extend `used` positions to
`2Q`.  This theorem is only the label/cardinality layer; preservation of the
product-one ordering uses that the chosen positions carry the identity. -/
theorem exists_disjoint_identity_padding {ι : Type*} [DecidableEq ι]
    (P identities : Finset ι) {Q m0 : ℕ}
    (hidentities : identities.card = m0) (hdis : Disjoint P identities)
    (hlower : 2 * Q - m0 ≤ P.card) (hupper : P.card ≤ 2 * Q) :
    ∃ J : Finset ι, J ⊆ identities ∧ Disjoint P J ∧
      (P ∪ J).card = 2 * Q := by
  have havail : 2 * Q - P.card ≤ identities.card := by
    rw [hidentities]
    exact identity_padding_amount_bounds hlower hupper
  obtain ⟨J, hJ, hcard⟩ := Finset.exists_subset_card_eq havail
  refine ⟨J, hJ, hdis.mono_right hJ, ?_⟩
  rw [Finset.card_union_of_disjoint (hdis.mono_right hJ), hcard]
  omega

end MiddleBookkeeping

section TranslationPullback

variable {A : Type*} [AddCommGroup A]

/-- Translating every term of an additive list adds `length • α` to its sum. -/
theorem sum_map_add_const (s : List A) (α : A) :
    (s.map (fun x => x + α)).sum = s.sum + s.length • α := by
  induction s with
  | nil => simp
  | cons x s ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
      rw [add_nsmul, one_nsmul]
      abel

/-- The exact all-rotation pullback leaf: translating an exact `2Q`-term
rotation block does not change its sum when `Q • α = 0`. -/
theorem sum_map_add_const_of_twice_card {s : List A} {Q : ℕ} {α : A}
    (hlen : s.length = 2 * Q) (hQ : Q • α = 0) :
    (s.map (fun x => x + α)).sum = s.sum := by
  rw [sum_map_add_const, hlen]
  have htwo : (2 * Q) • α = 0 := by
    rw [Nat.mul_comm 2 Q, mul_nsmul, hQ, nsmul_zero]
  rw [htwo, add_zero]

end TranslationPullback

end GaoLean

#print axioms GaoLean.eq_zero_of_two_nsmul_eq_zero_of_card_odd
#print axioms GaoLean.mem_of_two_nsmul_mem_of_quotient_card_odd
#print axioms GaoLean.mem_of_pos_neg_mem_same_coset_of_quotient_card_odd
#print axioms GaoLean.middle_target_bookkeeping
#print axioms GaoLean.middle_rotation_surplus
#print axioms GaoLean.same_type_pair_count
#print axioms GaoLean.exists_disjoint_identity_padding
#print axioms GaoLean.sum_map_add_const_of_twice_card
