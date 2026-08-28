import GaoLean.PGOlson
import GaoLean.PGIteratedKneser

/-!
# Canonical Davenport invariant for the finite abelian p-group GMO induction

This module deliberately does not manufacture invariant-factor
`DStarPresentation` data.  It uses the canonical exact ordinary Davenport
threshold and subtracts one, which is the invariant actually consumed by the
p-group subgroup--quotient induction.  The equality with Olson's displayed
invariant-factor sum is recorded only through already proved exact Davenport
statements.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

/-- The canonical ordinary `d*` used in the p-group induction: the least
exact ordinary Davenport threshold, minus one.  The definition makes sense
for every finite additive group; p-group structure is needed only for the
Olson interpretation. -/
noncomputable def pGroupDStar
    (B : Type u) [AddCommGroup B] [Finite B] : ℕ :=
  ordinaryDavenportValue B - 1

/-- The canonical threshold is positive, so adding back one recovers it
exactly rather than merely up to truncated subtraction. -/
theorem pGroupDStar_add_one
    (B : Type u) [AddCommGroup B] [Finite B] :
    pGroupDStar B + 1 = ordinaryDavenportValue B := by
  unfold pGroupDStar
  exact Nat.sub_add_cancel
    (ordinaryDavenportConstant_pos _ (ordinaryDavenportValue_spec B))

/-- Exact ordinary Davenport specification of the canonical `d*`. -/
theorem pGroupDStar_spec
    (B : Type u) [AddCommGroup B] [Finite B] :
    IsOrdinaryDavenportConstant B (pGroupDStar B + 1) := by
  rw [pGroupDStar_add_one B]
  exact ordinaryDavenportValue_spec B

section PGroupInheritance

variable {A : Type u} [AddCommGroup A] [Finite A]

/-- A subgroup of an additive p-group is again a p-group, with the additive
subtype transported through `Multiplicative`. -/
theorem isPGroup_multiplicative_addSubgroup
    (p : ℕ) (hA : IsPGroup p (Multiplicative A))
    (H : AddSubgroup A) :
    IsPGroup p (Multiplicative H) := by
  apply hA.of_injective H.subtype.toMultiplicative
  intro x y hxy
  exact congrArg (fun z : H ↦ Multiplicative.ofAdd z)
    (H.subtype_injective
      (congrArg (fun z : Multiplicative A ↦ z.toAdd) hxy))

/-- An additive quotient of a p-group is again a p-group. -/
theorem isPGroup_multiplicative_quotient
    (p : ℕ) (hA : IsPGroup p (Multiplicative A))
    (H : AddSubgroup A) :
    IsPGroup p (Multiplicative (A ⧸ H)) := by
  apply hA.of_surjective (QuotientAddGroup.mk' H).toMultiplicative
  intro q
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective H q.toAdd
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  simpa using congrArg (fun z : A ⧸ H ↦ Multiplicative.ofAdd z) ha

end PGroupInheritance

section DavenportConvolution

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Canonical ordinary `d*` is subadditive across every subgroup--quotient
pair.  This is a direct arithmetic restatement of the proved exact ordinary
Davenport convolution theorem. -/
theorem pGroupDStar_subgroup_quotient_le
    (H : AddSubgroup A) :
    pGroupDStar H + pGroupDStar (A ⧸ H) ≤ pGroupDStar A := by
  have hconv := ordinaryDavenport_subgroup_quotient H
    (ordinaryDavenportValue A)
    (ordinaryDavenportValue H)
    (ordinaryDavenportValue (A ⧸ H))
    (ordinaryDavenportValue_spec A)
    (ordinaryDavenportValue_spec H)
    (ordinaryDavenportValue_spec (A ⧸ H))
  have hA := pGroupDStar_add_one A
  have hH := pGroupDStar_add_one H
  have hQ := pGroupDStar_add_one (A ⧸ H)
  omega

/-- The same convolution inside an intermediate subgroup `L`.  A later
`K ≤ L` consumer may take `K'` to be the comap of `K` along `L.subtype`;
identifying its canonical invariant with that of `K` requires an explicit
additive equivalence and is therefore not hidden in this statement. -/
theorem pGroupDStar_internal_subgroup_quotient_le
    (L : AddSubgroup A) (K' : AddSubgroup L) :
    pGroupDStar K' + pGroupDStar (L ⧸ K') ≤ pGroupDStar L := by
  letI : Fintype L := Fintype.ofFinite L
  exact pGroupDStar_subgroup_quotient_le (A := L) K'

/-- Proper subgroup inclusion strictly lowers the finite cardinality. -/
theorem natCard_addSubgroup_lt_of_lt_top
    (H : AddSubgroup A) (hH : H < ⊤) :
    Nat.card H < Nat.card A := by
  letI : Fintype H := Fintype.ofFinite H
  have hnotSurj : ¬Function.Surjective (fun x : H ↦ (x : A)) := by
    intro hsurj
    have htop : H = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨y, hy⟩ := hsurj x
      simpa [← hy] using y.property
    exact (ne_of_lt hH) htop
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_injective_not_surjective
      (fun x : H ↦ (x : A)) Subtype.coe_injective hnotSurj

/-- Quotienting by a nontrivial subgroup strictly lowers the finite
cardinality. -/
theorem natCard_quotient_lt_of_addSubgroup_ne_bot
    (H : AddSubgroup A) (hH : H ≠ ⊥) :
    Nat.card (A ⧸ H) < Nat.card A := by
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hHone : Nat.card H ≠ 1 := by
    simpa using hH
  have hHgt : 1 < Nat.card H := by omega
  rw [H.card_eq_card_quotient_mul_card_addSubgroup]
  exact lt_mul_of_one_lt_right Nat.card_pos hHgt

/-- Both recursive ambient types in the proper-nontrivial p-group branch
have strictly smaller finite cardinality. -/
theorem pGroup_recursive_cardinalities_lt
    (H : AddSubgroup A) (hHbot : H ≠ ⊥) (hHtop : H < ⊤) :
    Nat.card H < Nat.card A ∧ Nat.card (A ⧸ H) < Nat.card A :=
  ⟨natCard_addSubgroup_lt_of_lt_top H hHtop,
    natCard_quotient_lt_of_addSubgroup_ne_bot H hHbot⟩

end DavenportConvolution

section OrdinarySpanning

variable {B : Type u} [AddCommGroup B] [Fintype B] [DecidableEq B]

/-- Membership in an exact iterated sum of one finite set is equivalently an
ordered representation of the prescribed length. -/
theorem mem_iteratedFinsetSum_replicate_iff
    (U : Finset B) (k : ℕ) (x : B) :
    x ∈ iteratedFinsetSum (List.replicate k U) ↔
      ∃ w : List B, w.length = k ∧
        (∀ y ∈ w, y ∈ U) ∧ w.sum = x := by
  induction k generalizing x with
  | zero =>
      simp [iteratedFinsetSum, eq_comm]
  | succ k ih =>
      rw [List.replicate_succ, iteratedFinsetSum_cons]
      constructor
      · intro hx
        obtain ⟨a, ha, y, hy, hxy⟩ := Finset.mem_add.mp hx
        obtain ⟨w, hwlen, hwU, hwsum⟩ := (ih y).1 hy
        refine ⟨a :: w, by simp [hwlen], ?_, ?_⟩
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact ha
          · exact hwU z hz
        · simp only [List.sum_cons, hwsum]
          exact hxy
      · rintro ⟨w, hwlen, hwU, hwsum⟩
        obtain ⟨a, tail, rfl⟩ : ∃ a tail, w = a :: tail := by
          cases w with
          | nil => simp at hwlen
          | cons a tail => exact ⟨a, tail, rfl⟩
        have htailLen : tail.length = k := by simpa using hwlen
        have ha : a ∈ U := hwU a (by simp)
        have htailU : ∀ y ∈ tail, y ∈ U := by
          intro y hy
          exact hwU y (by simp [hy])
        have htail : tail.sum ∈
            iteratedFinsetSum (List.replicate k U) :=
          (ih tail.sum).2 ⟨tail, htailLen, htailU, rfl⟩
        exact Finset.mem_add.mpr
          ⟨a, ha, tail.sum, htail, by simpa using hwsum⟩

/-- Summing the values of all labelled occurrences recovers the literal list
sum. -/
theorem sum_occurrenceValue_univ (w : List B) :
    (∑ i : Occurrence w, occurrenceValue w i) = w.sum := by
  simpa [occurrenceValue, List.get_eq_getElem] using
    (Fin.sum_univ_fun_getElem w)

/-- If a representation has at least the Davenport threshold many terms,
delete a nonempty zero-sum occurrence selection to obtain a strictly shorter
representation by elements of the same finite set. -/
theorem exists_shorter_list_sum_of_davenport
    (U : Finset B) (D : ℕ) (hD : OrdinaryDavenportAtMost B D)
    (w : List B) (hwU : ∀ y ∈ w, y ∈ U) (hlen : D ≤ w.length) :
    ∃ v : List B, v.length < w.length ∧
      (∀ y ∈ v, y ∈ U) ∧ v.sum = w.sum := by
  classical
  have hzeroTake : HasNonemptyZeroSum (w.take D) := by
    apply hD
    simp [List.length_take, Nat.min_eq_left hlen]
  have hzero : HasNonemptyZeroSum w :=
    hasNonemptyZeroSum_of_take w D hlen hzeroTake
  obtain ⟨J, hJne, hJsum⟩ := hzero
  let R : Selection w := (Finset.univ : Selection w) \ J
  let v : List B := R.toList.map (occurrenceValue w)
  have hcardSplit : R.card + J.card = w.length := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ J)
    simpa [R] using h
  have hvlen : v.length < w.length := by
    have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
    simp only [v, List.length_map, Finset.length_toList]
    omega
  have hvU : ∀ y ∈ v, y ∈ U := by
    intro y hy
    obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hy
    exact hwU (occurrenceValue w i) (List.get_mem w i)
  have hsplit :=
    (Finset.univ : Selection w).sum_inter_add_sum_sdiff J
      (occurrenceValue w)
  have hRsum : (∑ i ∈ R, occurrenceValue w i) = w.sum := by
    rw [Finset.inter_eq_right.mpr (Finset.subset_univ J), hJsum,
      zero_add] at hsplit
    rw [sum_occurrenceValue_univ] at hsplit
    simpa [R] using hsplit
  have hvsum : v.sum = w.sum := by
    simpa [v] using hRsum
  exact ⟨v, hvlen, hvU, hvsum⟩

/-- In a finite group, subgroup generation by `U` equals additive-monoid
generation by `U`; hence every element has a `U`-list representation.  A
minimal such representation has length strictly below any ordinary
Davenport upper threshold. -/
theorem exists_list_sum_length_lt_davenport
    (U : Finset B) (D : ℕ) (hD : OrdinaryDavenportAtMost B D)
    (hgen : AddSubgroup.closure (U : Set B) = ⊤) (x : B) :
    ∃ w : List B, w.length < D ∧
      (∀ y ∈ w, y ∈ U) ∧ w.sum = x := by
  classical
  have hmonoid : AddSubmonoid.closure (U : Set B) = ⊤ := by
    rw [← AddSubgroup.closure_toAddSubmonoid_of_finite, hgen]
    rfl
  have hx : x ∈ AddSubmonoid.closure (U : Set B) := by
    rw [hmonoid]
    exact trivial
  obtain ⟨w₀, hw₀U, hw₀sum⟩ :=
    AddSubmonoid.exists_list_of_mem_closure hx
  let Rep : ℕ → Prop := fun m ↦
    ∃ w : List B, w.length = m ∧
      (∀ y ∈ w, y ∈ U) ∧ w.sum = x
  have hRep : ∃ m, Rep m :=
    ⟨w₀.length, w₀, rfl, hw₀U, hw₀sum⟩
  let m := Nat.find hRep
  obtain ⟨w, hwlen, hwU, hwsum⟩ := Nat.find_spec hRep
  have hmD : m < D := by
    by_contra hnot
    have hDm : D ≤ m := Nat.le_of_not_gt hnot
    obtain ⟨v, hvlt, hvU, hvsum⟩ :=
      exists_shorter_list_sum_of_davenport U D hD w hwU (by
        calc
          D ≤ m := hDm
          _ = w.length := hwlen.symm)
    have hvltm : v.length < m := by
      calc
        v.length < w.length := hvlt
        _ = m := hwlen
    have hnotRep : ¬Rep v.length :=
      Nat.find_min hRep hvltm
    exact hnotRep ⟨v, rfl, hvU, hvsum.trans hwsum⟩
  exact ⟨w, hwlen.trans_lt hmD, hwU, hwsum⟩

/-- Every element belongs to the exact `(D-1)`-fold sumset of a generating
finite set containing zero.  Padding the minimal representation by zeros is
what changes the at-most bound into the source's exact-length statement. -/
theorem mem_iteratedFinsetSum_replicate_pred_of_davenport
    (U : Finset B) (D : ℕ) (hzero : 0 ∈ U)
    (hgen : AddSubgroup.closure (U : Set B) = ⊤)
    (hD : OrdinaryDavenportAtMost B D) (x : B) :
    x ∈ iteratedFinsetSum (List.replicate (D - 1) U) := by
  obtain ⟨w, hwlt, hwU, hwsum⟩ :=
    exists_list_sum_length_lt_davenport U D hD hgen x
  have hwle : w.length ≤ D - 1 := by omega
  let v := List.replicate (D - 1 - w.length) (0 : B) ++ w
  apply (mem_iteratedFinsetSum_replicate_iff U (D - 1) x).2
  refine ⟨v, ?_, ?_, ?_⟩
  · simp [v]
    omega
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · have hy0 : y = 0 := List.eq_of_mem_replicate hy
      simpa [hy0] using hzero
    · exact hwU y hy
  · simp [v, hwsum]

/-- Ordinary Lemma 4.2 in exact finite-sumset form. -/
theorem iteratedFinsetSum_replicate_pred_eq_univ_of_davenport
    (U : Finset B) (D : ℕ) (hzero : 0 ∈ U)
    (hgen : AddSubgroup.closure (U : Set B) = ⊤)
    (hD : OrdinaryDavenportAtMost B D) :
    iteratedFinsetSum (List.replicate (D - 1) U) = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  exact mem_iteratedFinsetSum_replicate_pred_of_davenport
    U D hzero hgen hD x

end OrdinarySpanning

end GaoLean
