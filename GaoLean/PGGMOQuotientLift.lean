import GaoLean.PGGMOTheorem21

/-!
# Pulling quotient-periodic structure back to the ambient group

This module packages the correspondence and third-isomorphism algebra used
to lift a subgroup of `A / K` back to `A`.  All affine membership statements
retain an explicit representative equation; equality in a quotient is never
silently strengthened to equality in the ambient group.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientLiftFintype (K : AddSubgroup A) :
    Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- The full preimage in `A` of a subgroup `J ≤ A / K`. -/
def liftedAddSubgroup (K : AddSubgroup A)
    (J : AddSubgroup (A ⧸ K)) : AddSubgroup A :=
  J.comap (QuotientAddGroup.mk' K)

/-- The quotient kernel is contained in every lifted subgroup. -/
theorem le_liftedAddSubgroup (K : AddSubgroup A)
    (J : AddSubgroup (A ⧸ K)) :
    K ≤ liftedAddSubgroup K J := by
  exact QuotientAddGroup.le_comap_mk' K J

/-- Mapping the lifted subgroup back down recovers the original quotient
subgroup exactly. -/
@[simp]
theorem map_liftedAddSubgroup (K : AddSubgroup A)
    (J : AddSubgroup (A ⧸ K)) :
    (liftedAddSubgroup K J).map (QuotientAddGroup.mk' K) = J := by
  unfold liftedAddSubgroup
  exact AddSubgroup.map_comap_eq_self (by simp)

/-- A proper quotient subgroup has a proper full preimage. -/
theorem liftedAddSubgroup_ne_top_of_ne_top
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (hJ : J ≠ ⊤) :
    liftedAddSubgroup K J ≠ ⊤ := by
  intro hL
  apply hJ
  calc
    J = (liftedAddSubgroup K J).map (QuotientAddGroup.mk' K) :=
      (map_liftedAddSubgroup K J).symm
    _ = (⊤ : AddSubgroup A).map (QuotientAddGroup.mk' K) :=
      congrArg (fun L : AddSubgroup A ↦
        L.map (QuotientAddGroup.mk' K)) hL
    _ = ⊤ := AddSubgroup.map_top_of_surjective _
      (QuotientAddGroup.mk'_surjective K)

/-- Strict properness is preserved by full preimage. -/
theorem liftedAddSubgroup_lt_top_of_lt_top
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (hJ : J < ⊤) :
    liftedAddSubgroup K J < ⊤ := by
  exact lt_top_iff_ne_top.mpr
    (liftedAddSubgroup_ne_top_of_ne_top K J hJ.ne)

/-- A nonzero subgroup in the quotient lifts strictly above the kernel. -/
theorem lt_liftedAddSubgroup_of_ne_bot
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (hJ : J ≠ ⊥) :
    K < liftedAddSubgroup K J := by
  refine lt_of_le_of_ne (le_liftedAddSubgroup K J) ?_
  intro hKL
  apply hJ
  calc
    J = (liftedAddSubgroup K J).map (QuotientAddGroup.mk' K) :=
      (map_liftedAddSubgroup K J).symm
    _ = K.map (QuotientAddGroup.mk' K) :=
      congrArg (fun L : AddSubgroup A ↦
        L.map (QuotientAddGroup.mk' K)) hKL.symm
    _ = ⊥ := QuotientAddGroup.map_mk'_self K

/-- Noether's third isomorphism theorem in the form needed for a quotient
subgroup presented directly as `J ≤ A / K`. -/
noncomputable def liftedQuotientEquiv
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K)) :
    A ⧸ liftedAddSubgroup K J ≃+ (A ⧸ K) ⧸ J :=
  (QuotientAddGroup.quotientQuotientEquivQuotient K
      (liftedAddSubgroup K J) (le_liftedAddSubgroup K J)).symm.trans
    (QuotientAddGroup.quotientAddEquivOfEq
      (map_liftedAddSubgroup K J))

/-- The two quotient groups in the lifted third-isomorphism square have
exactly the same cardinality. -/
theorem natCard_quotient_liftedAddSubgroup
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K)) :
    Nat.card (A ⧸ liftedAddSubgroup K J) =
      Nat.card ((A ⧸ K) ⧸ J) := by
  exact Nat.card_congr (liftedQuotientEquiv K J).toEquiv

/-- A canonical representative of one quotient element.  Later statements
also expose an explicit-representative form, so no conclusion depends on the
particular classical choice made here. -/
noncomputable def liftedQuotientRepresentative
    (K : AddSubgroup A) (alpha : A ⧸ K) : A :=
  Classical.choose (QuotientAddGroup.mk'_surjective K alpha)

@[simp]
theorem mk_liftedQuotientRepresentative
    (K : AddSubgroup A) (alpha : A ⧸ K) :
    QuotientAddGroup.mk' K (liftedQuotientRepresentative K alpha) = alpha :=
  Classical.choose_spec (QuotientAddGroup.mk'_surjective K alpha)

/-- Centered quotient membership is exactly membership of the ambient
difference in the lifted subgroup.  The equation `mk' K a = alpha` is kept
explicit. -/
theorem quotient_sub_mem_iff_sub_mem_liftedAddSubgroup
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (alpha : A ⧸ K) (a x : A)
    (ha : QuotientAddGroup.mk' K a = alpha) :
    QuotientAddGroup.mk' K x - alpha ∈ J ↔
      x - a ∈ liftedAddSubgroup K J := by
  change QuotientAddGroup.mk' K x - alpha ∈ J ↔
    QuotientAddGroup.mk' K (x - a) ∈ J
  rw [map_sub, ha]

/-- Affine-coset membership pulls back exactly along the quotient map. -/
theorem mk_mem_addCosetFinset_iff_mem_liftedAddCoset
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (alpha : A ⧸ K) (a x : A)
    (ha : QuotientAddGroup.mk' K a = alpha) :
    QuotientAddGroup.mk' K x ∈ addCosetFinset J alpha ↔
      x ∈ addCosetFinset (liftedAddSubgroup K J) a := by
  rw [mem_addCosetFinset_iff, mem_addCosetFinset_iff]
  exact quotient_sub_mem_iff_sub_mem_liftedAddSubgroup K J alpha a x ha

/-- Canonical-representative specialization of affine-coset pullback. -/
theorem mk_mem_addCosetFinset_iff_mem_liftedAddCoset_rep
    (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (alpha : A ⧸ K) (x : A) :
    QuotientAddGroup.mk' K x ∈ addCosetFinset J alpha ↔
      x ∈ addCosetFinset (liftedAddSubgroup K J)
        (liftedQuotientRepresentative K alpha) := by
  exact mk_mem_addCosetFinset_iff_mem_liftedAddCoset K J alpha
    (liftedQuotientRepresentative K alpha) x
    (mk_liftedQuotientRepresentative K alpha)

/-- The occurrence filter of a quotient coset is the labelled image of the
ambient lifted-coset filter.  The list-map occurrence equivalence preserves
positions, so repeated values remain distinct labels. -/
theorem mapSelection_occurrencesInAddCoset_lifted
    (xs : List A) (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (alpha : A ⧸ K) (a : A)
    (ha : QuotientAddGroup.mk' K a = alpha) :
    mapSelection (QuotientAddGroup.mk' K) xs
        (occurrencesInAddCoset xs (liftedAddSubgroup K J) a) =
      occurrencesInAddCoset (xs.map (QuotientAddGroup.mk' K)) J alpha := by
  classical
  ext q
  let e := ConcreteGDihedral.mapOccurrenceEquiv
    (QuotientAddGroup.mk' K) xs
  constructor
  · intro hq
    unfold mapSelection at hq
    obtain ⟨i, hi, hiq⟩ := Finset.mem_map.mp hq
    apply (mem_occurrencesInAddCoset_iff
      (xs.map (QuotientAddGroup.mk' K)) J alpha q).2
    have hiLift := (mem_occurrencesInAddCoset_iff xs
      (liftedAddSubgroup K J) a i).1 hi
    have hiQuot :=
      (quotient_sub_mem_iff_sub_mem_liftedAddSubgroup
        K J alpha a (occurrenceValue xs i) ha).2 hiLift
    rw [← hiq]
    have hv :
        occurrenceValue (xs.map (QuotientAddGroup.mk' K))
            ((ConcreteGDihedral.mapOccurrenceEquiv
              (QuotientAddGroup.mk' K) xs).toEmbedding i) =
          QuotientAddGroup.mk' K (occurrenceValue xs i) :=
      ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
        (QuotientAddGroup.mk' K) xs i
    rw [hv]
    exact hiQuot
  · intro hq
    let i : Occurrence xs := e.symm q
    unfold mapSelection
    apply Finset.mem_map.mpr
    refine ⟨i, ?_, ?_⟩
    · apply (mem_occurrencesInAddCoset_iff xs
        (liftedAddSubgroup K J) a i).2
      apply (quotient_sub_mem_iff_sub_mem_liftedAddSubgroup
        K J alpha a (occurrenceValue xs i) ha).1
      have hqQuot := (mem_occurrencesInAddCoset_iff
        (xs.map (QuotientAddGroup.mk' K)) J alpha q).1 hq
      have hv :
          QuotientAddGroup.mk' K
              (occurrenceValue xs
                ((ConcreteGDihedral.mapOccurrenceEquiv
                  (QuotientAddGroup.mk' K) xs).symm q)) =
            occurrenceValue (xs.map (QuotientAddGroup.mk' K)) q :=
        ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm
          (QuotientAddGroup.mk' K) xs q
      change QuotientAddGroup.mk' K
          (occurrenceValue xs
            ((ConcreteGDihedral.mapOccurrenceEquiv
              (QuotientAddGroup.mk' K) xs).symm q)) - alpha ∈ J
      rw [hv]
      exact hqQuot
    · change e i = q
      exact e.apply_symm_apply q

/-- Consequently, quotient-coset and lifted ambient-coset filters have the
same labelled occurrence count. -/
theorem card_occurrencesInAddCoset_lifted
    (xs : List A) (K : AddSubgroup A) (J : AddSubgroup (A ⧸ K))
    (alpha : A ⧸ K) (a : A)
    (ha : QuotientAddGroup.mk' K a = alpha) :
    (occurrencesInAddCoset (xs.map (QuotientAddGroup.mk' K)) J alpha).card =
      (occurrencesInAddCoset xs (liftedAddSubgroup K J) a).card := by
  rw [← mapSelection_occurrencesInAddCoset_lifted xs K J alpha a ha,
    card_mapSelection]

end GaoLean

#print axioms GaoLean.liftedQuotientEquiv
#print axioms GaoLean.natCard_quotient_liftedAddSubgroup
#print axioms GaoLean.quotient_sub_mem_iff_sub_mem_liftedAddSubgroup
#print axioms GaoLean.mapSelection_occurrencesInAddCoset_lifted
#print axioms GaoLean.card_occurrencesInAddCoset_lifted
