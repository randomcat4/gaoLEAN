import GaoLean.PGGeneralWeightedStrongRecursionState
import GaoLean.PGDavenportBridge

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
#print axioms GaoLean.occurrenceValue_quotientMapOccurrenceEquiv
#print axioms GaoLean.occurrenceValue_quotientMapOccurrenceEquiv_symm
#print axioms GaoLean.mk_mem_generalWeightedQuotientSubgroup_iff
#print axioms GaoLean.GeneralWeightedOvergroupInput.quotient
