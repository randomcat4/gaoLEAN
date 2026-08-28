import GaoLean.PGGMOClaimBAlgebra
import GaoLean.PGGMOQuotientLift

/-!
# The internal quotient of a lifted subgroup

For `H ≤ A` and `J ≤ A / H`, let `K` be the full preimage of `J` in
`A`.  This file records the short exact sequence

`H → K → J`

in the concrete subtype form used by the ordinary Step 1 construction.  In
particular, the quotient map is restricted to `K`, its kernel is identified
with the internal copy of `H`, and the resulting first-isomorphism equivalence
is exposed on quotient representatives.  The final lemmas are only membership
transport; no extension or structural conclusion is stored here.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance ordinaryLiftedSubgroupCoreQuotientFintype
    (H : AddSubgroup A) : Fintype (A ⧸ H) :=
  Fintype.ofFinite (A ⧸ H)

/-! ## The restricted quotient map -/

/-- The ambient quotient map restricted from the full preimage of `J` to
`J` itself. -/
def liftedAddSubgroupRestrictedMap
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    liftedAddSubgroup H J →+ J where
  toFun x := ⟨QuotientAddGroup.mk' H x.1, x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem liftedAddSubgroupRestrictedMap_apply
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (x : liftedAddSubgroup H J) :
    ((liftedAddSubgroupRestrictedMap H J x : J) : A ⧸ H) =
      QuotientAddGroup.mk' H x.1 :=
  rfl

/-- Surjectivity is genuine: every element of `J` has an ambient
representative, and that representative belongs to the full preimage. -/
theorem liftedAddSubgroupRestrictedMap_surjective
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    Function.Surjective (liftedAddSubgroupRestrictedMap H J) := by
  intro q
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective H q.1
  have haK : a ∈ liftedAddSubgroup H J := by
    change QuotientAddGroup.mk' H a ∈ J
    rw [ha]
    exact q.2
  refine ⟨⟨a, haK⟩, ?_⟩
  apply Subtype.ext
  exact ha

/-- The kernel of the restricted quotient map is exactly the internal copy
of `H` in its full preimage `K`. -/
theorem liftedAddSubgroupRestrictedMap_ker
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    (liftedAddSubgroupRestrictedMap H J).ker =
      internalAddSubgroup H (liftedAddSubgroup H J) := by
  ext x
  change liftedAddSubgroupRestrictedMap H J x = 0 ↔ x.1 ∈ H
  constructor
  · intro hx
    have hxq : QuotientAddGroup.mk' H x.1 = 0 :=
      congrArg Subtype.val hx
    have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hxq
    simpa using hmem
  · intro hx
    apply Subtype.ext
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa using hx

/-! ## First isomorphism and exact cardinality -/

/-- The internal quotient of the lifted subgroup is additively equivalent
to the quotient subgroup `J`. -/
noncomputable def liftedInternalQuotientEquiv
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    liftedAddSubgroup H J ⧸
        internalAddSubgroup H (liftedAddSubgroup H J) ≃+ J :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (liftedAddSubgroupRestrictedMap_ker H J).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (liftedAddSubgroupRestrictedMap H J)
      (liftedAddSubgroupRestrictedMap_surjective H J))

/-- Evaluation of the first-isomorphism equivalence on a concrete class.
This is the representative-level bridge used by later sum constructions. -/
@[simp]
theorem liftedInternalQuotientEquiv_mk
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H))
    (x : liftedAddSubgroup H J) :
    liftedInternalQuotientEquiv H J
        (QuotientAddGroup.mk'
          (internalAddSubgroup H (liftedAddSubgroup H J)) x) =
      liftedAddSubgroupRestrictedMap H J x := by
  have hfirst :
      (QuotientAddGroup.quotientAddEquivOfEq
          (liftedAddSubgroupRestrictedMap_ker H J).symm)
          (QuotientAddGroup.mk'
            (internalAddSubgroup H (liftedAddSubgroup H J)) x) =
        QuotientAddGroup.mk'
          (liftedAddSubgroupRestrictedMap H J).ker x := by
    exact QuotientAddGroup.quotientAddEquivOfEq_mk _ x
  apply Subtype.ext
  change ↑((QuotientAddGroup.quotientKerEquivOfSurjective
      (liftedAddSubgroupRestrictedMap H J)
      (liftedAddSubgroupRestrictedMap_surjective H J))
    ((QuotientAddGroup.quotientAddEquivOfEq
      (liftedAddSubgroupRestrictedMap_ker H J).symm)
      (QuotientAddGroup.mk'
        (internalAddSubgroup H (liftedAddSubgroup H J)) x))) =
      QuotientAddGroup.mk' H x.1
  rw [hfirst]
  rfl

/-- Exact order formula for a lifted subgroup. -/
theorem natCard_liftedAddSubgroup
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    Nat.card (liftedAddSubgroup H J) = Nat.card H * Nat.card J := by
  let K := liftedAddSubgroup H J
  let Hinside := internalAddSubgroup H K
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Hinside
  have hH : Nat.card Hinside = Nat.card H :=
    Nat.card_congr
      (internalAddSubgroupEquiv H K (le_liftedAddSubgroup H J)).toEquiv
  have hJ : Nat.card (K ⧸ Hinside) = Nat.card J :=
    Nat.card_congr (liftedInternalQuotientEquiv H J).toEquiv
  calc
    Nat.card K = Nat.card (K ⧸ Hinside) * Nat.card Hinside := hfactor
    _ = Nat.card J * Nat.card H := by rw [hJ, hH]
    _ = Nat.card H * Nat.card J := Nat.mul_comm _ _

/-- The canonical subgroup--quotient convolution, expressed directly using
`H`, `J`, and their full preimage. -/
theorem pGroupDStar_add_lifted_le
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) :
    pGroupDStar H + pGroupDStar J ≤
      pGroupDStar (liftedAddSubgroup H J) := by
  have hconv := pGroupDStar_internal_of_le H (liftedAddSubgroup H J)
    (le_liftedAddSubgroup H J)
  have heq :
      pGroupDStar
          (liftedAddSubgroup H J ⧸
            internalAddSubgroup H (liftedAddSubgroup H J)) =
        pGroupDStar J :=
    pGroupDStar_addEquiv (liftedInternalQuotientEquiv H J)
  simpa only [heq] using hconv

/-- A nonzero quotient subgroup makes its full preimage strictly larger than
the quotient kernel. -/
theorem lt_liftedAddSubgroup
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) (hJ : J ≠ ⊥) :
    H < liftedAddSubgroup H J :=
  lt_liftedAddSubgroup_of_ne_bot H J hJ

/-! ## Membership transport for Step 1 -/

@[simp]
theorem mem_liftedAddSubgroup_iff
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) (x : A) :
    x ∈ liftedAddSubgroup H J ↔ QuotientAddGroup.mk' H x ∈ J :=
  Iff.rfl

/-- Centered membership with the quotient center kept as the actual image of
the ambient center. -/
theorem mk_sub_mk_mem_iff_sub_mem_liftedAddSubgroup
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) (a x : A) :
    QuotientAddGroup.mk' H x - QuotientAddGroup.mk' H a ∈ J ↔
      x - a ∈ liftedAddSubgroup H J := by
  exact quotient_sub_mem_iff_sub_mem_liftedAddSubgroup H J
    (QuotientAddGroup.mk' H a) a x rfl

/-- Affine-coset membership pulls back without choosing a quotient
representative. -/
theorem mk_mem_liftedAddCoset_iff
    (H : AddSubgroup A) (J : AddSubgroup (A ⧸ H)) (a x : A) :
    QuotientAddGroup.mk' H x ∈
        addCosetFinset J (QuotientAddGroup.mk' H a) ↔
      x ∈ addCosetFinset (liftedAddSubgroup H J) a := by
  exact mk_mem_addCosetFinset_iff_mem_liftedAddCoset H J
    (QuotientAddGroup.mk' H a) a x rfl

end GaoLean

#print axioms GaoLean.liftedAddSubgroupRestrictedMap_surjective
#print axioms GaoLean.liftedAddSubgroupRestrictedMap_ker
#print axioms GaoLean.liftedInternalQuotientEquiv
#print axioms GaoLean.liftedInternalQuotientEquiv_mk
#print axioms GaoLean.natCard_liftedAddSubgroup
#print axioms GaoLean.pGroupDStar_add_lifted_le
#print axioms GaoLean.lt_liftedAddSubgroup
#print axioms GaoLean.mk_mem_liftedAddCoset_iff
