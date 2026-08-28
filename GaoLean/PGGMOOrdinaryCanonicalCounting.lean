import GaoLean.PGGMOOrdinaryCanonicalOutside
import GaoLean.PGGMOOrdinaryLiftedSubgroupCore
import GaoLean.PGGMOOrdinaryPairSubgroup

/-!
# Counting and finite-set assembly for canonical subgroup enlargement

This module contains the arithmetic and literal-label bookkeeping used when
a canonical Step 1 subgroup `H` is enlarged by a subgroup `J ≤ A / H`.
The enlarged subgroup is the full preimage `K`.  All results are stated for
an already supplied labelled pair-subgroup certificate; no existence or
later structural conclusion is assumed.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance ordinaryCanonicalCountingQuotientFintype
    (H : AddSubgroup A) : Fintype (A ⧸ H) :=
  Fintype.ofFinite (A ⧸ H)

/-! ## Cardinal and `d*` budgets -/

/-- The elementary positive-factor inequality underlying the lifted
subgroup carrier count. -/
theorem add_sub_one_le_mul_of_pos
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b - 1 ≤ a * b := by
  by_cases haOne : a = 1
  · simp [haOne]
  by_cases hbOne : b = 1
  · simp [hbOne]
  have haTwo : 2 ≤ a := by omega
  have hbTwo : 2 ≤ b := by omega
  have hab := Nat.add_le_mul haTwo hbTwo
  omega

/-- Applied to finite subgroup orders, the additive essential-core cost is
bounded by the order of the lifted subgroup. -/
theorem natCard_add_natCard_sub_one_le_lifted
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    Nat.card H + Nat.card J - 1 ≤
      Nat.card (liftedAddSubgroup H J) := by
  rw [natCard_liftedAddSubgroup H J]
  exact add_sub_one_le_mul_of_pos (Nat.card H) (Nat.card J)
    Nat.card_pos Nat.card_pos

/-- The two internal `d*` budgets fit inside the canonical budget of their
lifted subgroup. -/
theorem pGroupDStar_H_add_J_le_lifted
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    pGroupDStar H + pGroupDStar J ≤
      pGroupDStar (liftedAddSubgroup H J) :=
  pGroupDStar_add_lifted_le H J

/-- The old `H` core, a `|J|-1` pair core, and the two canonical padding
budgets together fit inside `|K| + d*(K)`. -/
theorem essentialCarrierSize_le_lifted
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    Nat.card H + pGroupDStar H + (Nat.card J - 1) + pGroupDStar J ≤
      Nat.card (liftedAddSubgroup H J) +
        pGroupDStar (liftedAddSubgroup H J) := by
  have hcard := natCard_add_natCard_sub_one_le_lifted H J
  have hdstar := pGroupDStar_H_add_J_le_lifted H J
  have hJpos : 1 ≤ Nat.card J := Nat.card_pos
  omega

/-- After adding the fixed filler that raises the selected length from
`|H| + |J| - 1` to `|K|`, the entire essential carrier still fits inside
`|K| + d*(K)`. -/
theorem essentialCarrierSize_with_filler_le_lifted
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    Nat.card H + pGroupDStar H + (Nat.card J - 1) + pGroupDStar J +
        (Nat.card (liftedAddSubgroup H J) -
          (Nat.card H + Nat.card J - 1)) ≤
      Nat.card (liftedAddSubgroup H J) +
        pGroupDStar (liftedAddSubgroup H J) := by
  have hcard := natCard_add_natCard_sub_one_le_lifted H J
  have hdstar := pGroupDStar_H_add_J_le_lifted H J
  have hJpos : 1 ≤ Nat.card J := Nat.card_pos
  omega

/-! ## Literal retained labels and the enlarged canonical container -/

namespace CanonicalOrdinaryGMOStep1Core

/-- Embed a finset of literal outside indices back into the original source
occurrence type. -/
noncomputable def mapOutsideSelection
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (s : Finset (↑C.outsideOccurrences)) : Selection xs :=
  s.map {
    toFun := fun i ↦ i.1
    inj' := fun _ _ h ↦ Subtype.ext h
  }

/-- The enlarged literal container consists of the complete old `H` coset
and every outside label whose centered quotient value lies in `J`. -/
noncomputable def liftedCanonicalContainer
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue) :
    Selection xs :=
  C.container ∪ C.mapOutsideSelection P.retained

theorem disjoint_container_mapOutsideSelection
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (s : Finset (↑C.outsideOccurrences)) :
    Disjoint C.container (C.mapOutsideSelection s) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiContainer hiMap
  obtain ⟨j, _hj, hji⟩ := Finset.mem_map.mp hiMap
  have hval : j.1 = i := hji
  have hjOutside := (Finset.mem_sdiff.mp j.2).2
  exact hjOutside (hval.symm ▸ hiContainer)

@[simp]
theorem card_mapOutsideSelection
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (s : Finset (↑C.outsideOccurrences)) :
    (C.mapOutsideSelection s).card = s.card := by
  classical
  exact Finset.card_map _

/-- Exact labelled cardinality of the assembled enlarged container. -/
theorem card_liftedCanonicalContainer
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue) :
    (C.liftedCanonicalContainer P).card =
      C.container.card + P.retained.card := by
  classical
  unfold liftedCanonicalContainer
  rw [Finset.card_union_of_disjoint
      (C.disjoint_container_mapOutsideSelection P.retained),
    C.card_mapOutsideSelection]

/-- The assembled container is exactly the complete source fiber over the
lifted affine coset.  In particular, retained labels are not an arbitrary
subset of that coset. -/
theorem liftedCanonicalContainer_eq_occurrencesInAddCoset
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue) :
    C.liftedCanonicalContainer P =
      occurrencesInAddCoset xs (liftedAddSubgroup C.H P.J) C.beta := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hiOld | hiRetained
    · apply (mem_occurrencesInAddCoset_iff xs
          (liftedAddSubgroup C.H P.J) C.beta i).2
      exact (le_liftedAddSubgroup C.H P.J)
        ((mem_addCosetFinset_iff C.H C.beta _).1
          (C.container_in_coset i hiOld))
    · obtain ⟨j, hjRetained, hji⟩ :=
        Finset.mem_map.mp hiRetained
      have hval : j.1 = i := hji
      have hjJ : C.outsideQuotientValue j ∈ P.J :=
        (P.mem_retained_iff j).1 hjRetained
      apply (mem_occurrencesInAddCoset_iff xs
        (liftedAddSubgroup C.H P.J) C.beta i).2
      change QuotientAddGroup.mk' C.H
        (occurrenceValue xs i - C.beta) ∈ P.J
      simpa [outsideQuotientValue, quotientDisplacement, hval]
        using hjJ
  · intro hiLifted
    by_cases hiOld : i ∈ C.container
    · exact Finset.mem_union_left _ hiOld
    · have hiOutside : i ∈ C.outsideOccurrences := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiOld⟩
      let j : ↑C.outsideOccurrences := ⟨i, hiOutside⟩
      have hiCentered : occurrenceValue xs i - C.beta ∈
          liftedAddSubgroup C.H P.J :=
        (mem_occurrencesInAddCoset_iff xs
          (liftedAddSubgroup C.H P.J) C.beta i).1 hiLifted
      have hjJ : C.outsideQuotientValue j ∈ P.J := by
        change QuotientAddGroup.mk' C.H
          (occurrenceValue xs i - C.beta) ∈ P.J
        exact hiCentered
      have hjRetained : j ∈ P.retained :=
        (P.mem_retained_iff j).2 hjJ
      apply Finset.mem_union_right C.container
      apply Finset.mem_map.mpr
      exact ⟨j, hjRetained, rfl⟩

/-! ## The source-coset threshold count -/

/-- Pure truncated-natural count: an exact split with at most `q-2`
omissions leaves at least `length-q+2` retained labels. -/
theorem retained_count_lower_of_omitted_bound
    (length old retained omitted q : ℕ)
    (hsplit : old + retained + omitted = length)
    (homitted : omitted ≤ q - 2) (hq : 2 ≤ q)
    (hqLength : q ≤ length) :
    length - q + 2 ≤ old + retained := by
  omega

/-- A proper quotient certificate gives the exact canonical concentration
threshold count for the lifted container.  Properness of `J` is necessary:
when `J = top`, the lifted subgroup is top and this threshold becomes one
larger than the whole source. -/
theorem card_liftedCanonicalContainer_lower
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (hJproper : P.J < ⊤)
    (hqSource : Nat.card (A ⧸ liftedAddSubgroup C.H P.J) ≤ xs.length) :
    xs.length - Nat.card (A ⧸ liftedAddSubgroup C.H P.J) + 2 ≤
      (C.liftedCanonicalContainer P).card := by
  letI : DecidableEq (↑C.outsideOccurrences) :=
    pairSubgroupDecidableEq
  let omitted :=
    ((Finset.univ : Finset (↑C.outsideOccurrences)) \ P.retained).card
  have hcontainerLe : C.container.card ≤ xs.length := by
    simpa using Finset.card_le_univ C.container
  have houtside := C.card_outsideOccurrences
  have hcertSplit : P.retained.card + omitted =
      C.outsideOccurrences.card := by
    dsimp only [omitted]
    simpa [Nat.card_eq_fintype_card] using P.card_retained_add_omitted
  have hsplit : C.container.card + P.retained.card + omitted =
      xs.length := by
    omega
  have homitted : omitted ≤
      Nat.card ((A ⧸ C.H) ⧸ P.J) - 2 := by
    simpa only [omitted] using P.omitted_bound
  letI : Nontrivial ((A ⧸ C.H) ⧸ P.J) :=
    QuotientAddGroup.nontrivial_iff.mpr hJproper.ne
  have hqTwo : 2 ≤ Nat.card ((A ⧸ C.H) ⧸ P.J) :=
    Finite.one_lt_card
  have hqSource' : Nat.card ((A ⧸ C.H) ⧸ P.J) ≤ xs.length := by
    rw [← natCard_quotient_liftedAddSubgroup C.H P.J]
    exact hqSource
  have hcount := retained_count_lower_of_omitted_bound
    xs.length C.container.card P.retained.card omitted
      (Nat.card ((A ⧸ C.H) ⧸ P.J))
      hsplit homitted hqTwo hqSource'
  rw [C.card_liftedCanonicalContainer]
  rw [natCard_quotient_liftedAddSubgroup C.H P.J]
  exact hcount

/-- The assembled lifted container always retains the ambient Step 1
budget under the exact global source-length hypothesis.  For `J = top` the
lifted container is the whole source.  For proper `J`, the omitted-label
bound and the subgroup--quotient cardinal factorization give the result. -/
theorem card_liftedCanonicalContainer_ambient_lower
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (P : OrdinaryPairSubgroupCertificate C.outsideQuotientValue)
    (hlen : Nat.card A + pGroupDStar A ≤ xs.length) :
    Nat.card (liftedAddSubgroup C.H P.J) + pGroupDStar A ≤
      (C.liftedCanonicalContainer P).card := by
  by_cases hJtop : P.J = ⊤
  · have hKtop : liftedAddSubgroup C.H P.J = ⊤ := by
      ext x
      simp [liftedAddSubgroup, hJtop]
    have hcontainerTop : C.liftedCanonicalContainer P =
        (Finset.univ : Selection xs) := by
      rw [C.liftedCanonicalContainer_eq_occurrencesInAddCoset P, hKtop]
      ext i
      simp [mem_occurrencesInAddCoset_iff]
    have hKcard : Nat.card (liftedAddSubgroup C.H P.J) = Nat.card A := by
      rw [hKtop]
      exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
    rw [hcontainerTop, hKcard]
    simpa using hlen
  · have hJproper : P.J < ⊤ := lt_top_iff_ne_top.mpr hJtop
    have hKproper : liftedAddSubgroup C.H P.J < ⊤ :=
      liftedAddSubgroup_lt_top_of_lt_top C.H P.J hJproper
    letI : Nontrivial (A ⧸ liftedAddSubgroup C.H P.J) :=
      QuotientAddGroup.nontrivial_iff.mpr hKproper.ne
    have hqTwo : 2 ≤
        Nat.card (A ⧸ liftedAddSubgroup C.H P.J) :=
      Finite.one_lt_card
    have hqLeA :
        Nat.card (A ⧸ liftedAddSubgroup C.H P.J) ≤ Nat.card A :=
      Nat.le_of_dvd Nat.card_pos
        (liftedAddSubgroup C.H P.J).card_quotient_dvd_card
    have hqSource :
        Nat.card (A ⧸ liftedAddSubgroup C.H P.J) ≤ xs.length := by
      exact hqLeA.trans (by omega)
    have hthreshold :=
      C.card_liftedCanonicalContainer_lower P hJproper hqSource
    have hfactor :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (liftedAddSubgroup C.H P.J)
    have hpositiveProduct := add_sub_one_le_mul_of_pos
      (Nat.card (A ⧸ liftedAddSubgroup C.H P.J))
      (Nat.card (liftedAddSubgroup C.H P.J))
      (by omega) Nat.card_pos
    omega

end CanonicalOrdinaryGMOStep1Core

end GaoLean

#print axioms GaoLean.natCard_add_natCard_sub_one_le_lifted
#print axioms GaoLean.pGroupDStar_H_add_J_le_lifted
#print axioms GaoLean.essentialCarrierSize_le_lifted
#print axioms GaoLean.essentialCarrierSize_with_filler_le_lifted
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.card_liftedCanonicalContainer
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.liftedCanonicalContainer_eq_occurrencesInAddCoset
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.retained_count_lower_of_omitted_bound
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.card_liftedCanonicalContainer_lower
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.card_liftedCanonicalContainer_ambient_lower
