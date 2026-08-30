import GaoLean.PGGeneralWeightedStrongRecursionState
import GaoLean.PGDavenportBridge
import GaoLean.PGDGMAmbientQuotient

/-!
# Quotient transport of the general-weighted overgroup input

This file supplies the first non-conditional bridge needed by the strong
recursion.  If `L ≤ G`, quotienting the ambient group by `L` sends the
equation-(3) affine input over `G` to the corresponding affine input over the
image of `G` in the quotient.

Occurrences are transported by the canonical equivalence of positions of a
list and its `List.map`.  Thus equal source values at different positions stay
distinct throughout the construction.
-/

namespace GaoLean

universe u

variable {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]

/-- The recursive overgroup seen in the ambient quotient by `L`. -/
def generalWeightedQuotientSubgroup
    (L G : AddSubgroup G₀) : AddSubgroup (G₀ ⧸ L) :=
  G.map (QuotientAddGroup.mk' L)

/-- The ambient quotient map restricted to the recursive overgroup and with
codomain restricted to its image. -/
def generalWeightedQuotientRestrictedMap
    (L G : AddSubgroup G₀) :
    G →+ generalWeightedQuotientSubgroup L G where
  toFun x := ⟨QuotientAddGroup.mk' L x.1, ⟨x.1, x.2, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem generalWeightedQuotientRestrictedMap_apply
    (L G : AddSubgroup G₀) (x : G) :
    ((generalWeightedQuotientRestrictedMap L G x :
        generalWeightedQuotientSubgroup L G) : G₀ ⧸ L) =
      QuotientAddGroup.mk' L x.1 :=
  rfl

theorem generalWeightedQuotientRestrictedMap_surjective
    (L G : AddSubgroup G₀) :
    Function.Surjective (generalWeightedQuotientRestrictedMap L G) := by
  intro q
  rcases q.2 with ⟨x, hxG, hxq⟩
  refine ⟨⟨x, hxG⟩, ?_⟩
  apply Subtype.ext
  exact hxq

/-- If `L ≤ G`, the kernel of the restricted quotient map is the internal
copy of `L` inside `G`. -/
theorem generalWeightedQuotientRestrictedMap_ker
    (L G : AddSubgroup G₀) (hLG : L ≤ G) :
    (generalWeightedQuotientRestrictedMap L G).ker =
      L.addSubgroupOf G := by
  ext x
  change generalWeightedQuotientRestrictedMap L G x = 0 ↔ x.1 ∈ L
  constructor
  · intro hx
    have hxq : QuotientAddGroup.mk' L x.1 = 0 :=
      congrArg Subtype.val hx
    have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hxq
    simpa using hmem
  · intro hx
    apply Subtype.ext
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa using hx

/-- The internal quotient `G/L` is additively equivalent to the image of the
recursive overgroup in the ambient quotient by `L`. -/
noncomputable def generalWeightedInternalQuotientEquiv
    (L G : AddSubgroup G₀) (hLG : L ≤ G) :
    G ⧸ L.addSubgroupOf G ≃+
      generalWeightedQuotientSubgroup L G :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (generalWeightedQuotientRestrictedMap_ker L G hLG).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (generalWeightedQuotientRestrictedMap L G)
      (generalWeightedQuotientRestrictedMap_surjective L G))

/-- Exact weighted Davenport data transports from the internal quotient to
the corresponding quotient-image subgroup. -/
theorem isWeightedDavenportConstant_generalWeightedQuotientSubgroup
    {W : Set ℤ} (L G : AddSubgroup G₀) (hLG : L ≤ G) (DQ : ℕ)
    (hDQ : IsWeightedDavenportConstant W
      (G ⧸ L.addSubgroupOf G) DQ) :
    IsWeightedDavenportConstant W
      (generalWeightedQuotientSubgroup L G) DQ :=
  isWeightedDavenportConstant_addEquiv W
    (generalWeightedInternalQuotientEquiv L G hLG) hDQ

/-- Every quotient subgroup's exact weighted Davenport constant is at most
the exact constant of the recursive quotient image containing it. -/
theorem weightedDavenportConstant_le_overgroupQuotient
    {W : Set ℤ} (L G : AddSubgroup G₀) (hLG : L ≤ G)
    (J : AddSubgroup (G₀ ⧸ L))
    (hJ : J ≤ generalWeightedQuotientSubgroup L G)
    (DJ DQ : ℕ)
    (hDJ : IsWeightedDavenportConstant W J DJ)
    (hDQ : IsWeightedDavenportConstant W
      (G ⧸ L.addSubgroupOf G) DQ) :
    DJ ≤ DQ := by
  let QG := generalWeightedQuotientSubgroup L G
  let Jin := J.addSubgroupOf QG
  have hQG : IsWeightedDavenportConstant W QG DQ :=
    isWeightedDavenportConstant_generalWeightedQuotientSubgroup
      L G hLG DQ hDQ
  have hJin : IsWeightedDavenportConstant W Jin DJ :=
    isWeightedDavenportConstant_addEquiv W
      (AddSubgroup.addSubgroupOfEquivOfLe hJ).symm hDJ
  exact weightedDavenportConstant_le_of_atMost W Jin hJin
    (weightedDavenportAtMost_subgroup W Jin DQ hQG.1)

/-- The image of the full recursive overgroup in any ambient quotient is the
full quotient group. -/
theorem generalWeightedQuotientSubgroup_top
    (L : AddSubgroup G₀) :
    generalWeightedQuotientSubgroup L (⊤ : AddSubgroup G₀) = ⊤ := by
  apply top_unique
  intro q _hq
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L q
  exact ⟨x, by simp, rfl⟩

/-- At the full overgroup, the internal quotient cardinal is exactly the
ambient quotient cardinal. -/
theorem natCard_internalQuotient_top
    (L : AddSubgroup G₀) :
    Nat.card ((⊤ : AddSubgroup G₀) ⧸
        L.addSubgroupOf (⊤ : AddSubgroup G₀)) =
      Nat.card (G₀ ⧸ L) := by
  calc
    Nat.card ((⊤ : AddSubgroup G₀) ⧸
        L.addSubgroupOf (⊤ : AddSubgroup G₀)) =
        Nat.card (generalWeightedQuotientSubgroup L
          (⊤ : AddSubgroup G₀)) :=
      Nat.card_congr
        (generalWeightedInternalQuotientEquiv L
          (⊤ : AddSubgroup G₀) le_top)
    _ = Nat.card (⊤ : AddSubgroup (G₀ ⧸ L)) := by
      rw [generalWeightedQuotientSubgroup_top]
    _ = Nat.card (G₀ ⧸ L) :=
      Nat.card_congr AddSubgroup.topEquiv

/-- The position-preserving equivalence between a source and its quotient
list.  Its existence uses only `List.length_map`, never source values. -/
def quotientMapOccurrenceEquiv
  (L : AddSubgroup G₀) (xs : List G₀) :
    Occurrence xs ≃
      Occurrence (xs.map (QuotientAddGroup.mk' L)) :=
  ConcreteGDihedral.mapOccurrenceEquiv (QuotientAddGroup.mk' L) xs

@[simp]
theorem quotientMapOccurrenceEquiv_val
    (L : AddSubgroup G₀) (xs : List G₀) (i : Occurrence xs) :
    (quotientMapOccurrenceEquiv L xs i).1 = i.1 := by
  rfl

@[simp]
theorem occurrenceValue_quotientMapOccurrenceEquiv
    (L : AddSubgroup G₀) (xs : List G₀) (i : Occurrence xs) :
    occurrenceValue (xs.map (QuotientAddGroup.mk' L))
        (quotientMapOccurrenceEquiv L xs i) =
      QuotientAddGroup.mk' L (occurrenceValue xs i) := by
  simpa [quotientMapOccurrenceEquiv] using
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
      (QuotientAddGroup.mk' L) xs i

/-- Every quotient occurrence has a unique original source position, and its
value is the quotient of the value at that exact position. -/
theorem occurrenceValue_quotientMapOccurrenceEquiv_symm
    (L : AddSubgroup G₀) (xs : List G₀)
    (j : Occurrence (xs.map (QuotientAddGroup.mk' L))) :
    occurrenceValue (xs.map (QuotientAddGroup.mk' L)) j =
      QuotientAddGroup.mk' L
        (occurrenceValue xs ((quotientMapOccurrenceEquiv L xs).symm j)) := by
  simpa only [Equiv.apply_symm_apply] using
    occurrenceValue_quotientMapOccurrenceEquiv L xs
      ((quotientMapOccurrenceEquiv L xs).symm j)

/-- When `L ≤ G`, membership in the image subgroup loses no information about
membership in `G`.  This is the subgroup form of the third isomorphism
picture used by the recursive quotient step. -/
@[simp]
theorem mk_mem_generalWeightedQuotientSubgroup_iff
    {L G : AddSubgroup G₀} (hLG : L ≤ G) (x : G₀) :
    QuotientAddGroup.mk' L x ∈ generalWeightedQuotientSubgroup L G ↔
      x ∈ G := by
  constructor
  · rintro ⟨g, hg, hq⟩
    have hxgL : x - g ∈ L := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      exact hq.symm
    have hxgG : x - g ∈ G := hLG hxgL
    have hx : x = (x - g) + g := by abel
    rw [hx]
    exact G.add_mem hxgG hg
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Quotienting a recursive overgroup by a nontrivial subgroup strictly
lowers the cardinality of that recursive overgroup.

The rank is the cardinality of `G`, not that of the ambient type `G₀`.  This
is the exact decrease needed by the cross-type strong-induction scheduler. -/
theorem natCard_generalWeightedQuotientSubgroup_lt
    {L G : AddSubgroup G₀} (hLG : L ≤ G) (hL : ⊥ < L) :
    Nat.card (generalWeightedQuotientSubgroup L G) < Nat.card G := by
  classical
  have hLcard : 2 ≤ Nat.card L := by
    have hcardlt : Nat.card (⊥ : AddSubgroup G₀) < Nat.card L :=
      natCard_lt_of_addSubgroup_lt hL
    have hbotcard : Nat.card (⊥ : AddSubgroup G₀) = 1 := by simp
    rw [hbotcard] at hcardlt
    omega
  have hqpos : 0 < Nat.card (generalWeightedQuotientSubgroup L G) :=
    Nat.card_pos
  have hfactor := natCard_mul_natCard_map_quotient L G hLG
  change Nat.card L * Nat.card (generalWeightedQuotientSubgroup L G) =
    Nat.card G at hfactor
  nlinarith

/-- Quotienting equation (3) by a subgroup inside its recursive overgroup
preserves both affine centres and every labelled source occurrence.

The weight set is not enumerated or changed, so this applies to infinite
`W : Set ℤ` as well. -/
theorem GeneralWeightedOvergroupInput.quotient
    {W : Set ℤ} {L G : AddSubgroup G₀} {gamma delta : G₀}
    {xs : List G₀}
    (hLG : L ≤ G)
    (h : GeneralWeightedOvergroupInput W G gamma delta xs) :
    GeneralWeightedOvergroupInput W
      (generalWeightedQuotientSubgroup L G)
      (QuotientAddGroup.mk' L gamma)
      (QuotientAddGroup.mk' L delta)
      (xs.map (QuotientAddGroup.mk' L)) := by
  constructor
  · intro j
    let i : Occurrence xs :=
      (quotientMapOccurrenceEquiv L xs).symm j
    have hi : occurrenceValue xs i - gamma ∈ G := h.source_mem i
    have hqi :=
      (mk_mem_generalWeightedQuotientSubgroup_iff hLG
        (occurrenceValue xs i - gamma)).2 hi
    simpa only [map_sub,
      occurrenceValue_quotientMapOccurrenceEquiv_symm] using hqi
  · intro j w hw
    let i : Occurrence xs :=
      (quotientMapOccurrenceEquiv L xs).symm j
    have hi : w • occurrenceValue xs i - delta ∈ G :=
      h.weighted_mem i w hw
    have hqi :=
      (mk_mem_generalWeightedQuotientSubgroup_iff hLG
        (w • occurrenceValue xs i - delta)).2 hi
    simpa only [map_sub, map_zsmul,
      occurrenceValue_quotientMapOccurrenceEquiv_symm] using hqi

end GaoLean

#print axioms GaoLean.quotientMapOccurrenceEquiv_val
#print axioms GaoLean.generalWeightedQuotientRestrictedMap_apply
#print axioms GaoLean.generalWeightedQuotientRestrictedMap_surjective
#print axioms GaoLean.generalWeightedQuotientRestrictedMap_ker
#print axioms GaoLean.generalWeightedInternalQuotientEquiv
#print axioms GaoLean.isWeightedDavenportConstant_generalWeightedQuotientSubgroup
#print axioms GaoLean.weightedDavenportConstant_le_overgroupQuotient
#print axioms GaoLean.generalWeightedQuotientSubgroup_top
#print axioms GaoLean.natCard_internalQuotient_top
#print axioms GaoLean.occurrenceValue_quotientMapOccurrenceEquiv
#print axioms GaoLean.occurrenceValue_quotientMapOccurrenceEquiv_symm
#print axioms GaoLean.mk_mem_generalWeightedQuotientSubgroup_iff
#print axioms GaoLean.natCard_generalWeightedQuotientSubgroup_lt
#print axioms GaoLean.GeneralWeightedOvergroupInput.quotient
