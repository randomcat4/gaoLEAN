import GaoLean.PGGMOClaimBAssembly
import GaoLean.PGGMOClaimBCounting
import GaoLean.PGGMOClaimBSubgroup
import GaoLean.PGDavenportBound

/-!
# Honest inputs for the ordinary GMO Claim B Case-1 driver

This module derives the structural, p-group, cardinal, and labelled-
occurrence inputs consumed by the final Case-1 assembly.  It constructs no
Claim-B output and assumes no saturation conclusion.

The literal unused-occurrence clause of Theorem E has an `H ≠ ⊥` guard.
In the non-large Case-1 branch this guard is proved, rather than assumed:
the existing trivial-period endpoint would otherwise give the large
alternative immediately.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

section NontrivialIntermediateSubgroup

/-- Centering is a translation of the common quotient layer, so its
cardinality is exactly the source parameter `N`. -/
theorem Theorem21SetPartition.card_centeredCommonCoreQuotient_eq_commonCosetCount
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) :
    (centeredCommonCoreQuotient P H g).card = P.commonCosetCount H := by
  classical
  unfold centeredCommonCoreQuotient
  calc
    ((quotientLayer H (P.commonCore H)).image fun q ↦
        q - QuotientAddGroup.mk' H g).card =
        (quotientLayer H (P.commonCore H)).card :=
      Finset.card_image_of_injective _ (by
        intro q r hqr
        have hqr' := congrArg
          (fun z : A ⧸ H ↦ z + QuotientAddGroup.mk' H g) hqr
        simpa [sub_add_cancel] using hqr')
    _ = P.commonCosetCount H :=
      P.card_quotientLayer_commonCore_eq_commonCosetCount H

/-- If `N ≥ 2`, the centered quotient generators cannot generate the
trivial subgroup.  This also covers `H = ⊥`. -/
theorem claimBIntermediateQuotientSubgroup_ne_bot_of_two_le_commonCosetCount
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A)
    (hN : 2 ≤ P.commonCosetCount H) :
    claimBIntermediateQuotientSubgroup P H g ≠ ⊥ := by
  classical
  have hU : 1 < (centeredCommonCoreQuotient P H g).card := by
    rw [P.card_centeredCommonCoreQuotient_eq_commonCosetCount H g]
    omega
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp hU
  intro hL
  have hqL : q ∈ claimBIntermediateQuotientSubgroup P H g :=
    AddSubgroup.subset_closure hq
  have hrL : r ∈ claimBIntermediateQuotientSubgroup P H g :=
    AddSubgroup.subset_closure hr
  rw [hL] at hqL hrL
  have hq0 : q = 0 := by simpa using hqL
  have hr0 : r = 0 := by simpa using hrL
  exact hqr (hq0.trans hr0.symm)

/-- The full preimage `K` is nontrivial whenever the centered quotient
subgroup is nontrivial. -/
theorem claimBIntermediateSubgroup_ne_bot_of_intermediateQuotient_ne_bot
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A)
    (hL : claimBIntermediateQuotientSubgroup P H g ≠ ⊥) :
    claimBIntermediateSubgroup P H g ≠ ⊥ := by
  let L := claimBIntermediateQuotientSubgroup P H g
  let K := claimBIntermediateSubgroup P H g
  letI : Nontrivial L :=
    (AddSubgroup.nontrivial_iff_ne_bot L).2 hL
  obtain ⟨q, hq⟩ := exists_ne (0 : L)
  obtain ⟨x, hx⟩ := claimBIntermediateMap_surjective P H g q
  intro hK
  have hxzero : x = 0 := by
    apply Subtype.ext
    have hxbot : x.1 ∈ (⊥ : AddSubgroup A) := by
      rw [← hK]
      exact x.2
    simpa using hxbot
  apply hq
  rw [← hx, hxzero, map_zero]

/-- The Case-1 input `N ≥ 2` forces the intermediate subgroup `K` to be
nontrivial, with no separate assumption on `H`. -/
theorem claimBIntermediateSubgroup_ne_bot_of_two_le_commonCosetCount
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A)
    (hN : 2 ≤ P.commonCosetCount H) :
    claimBIntermediateSubgroup P H g ≠ ⊥ :=
  claimBIntermediateSubgroup_ne_bot_of_intermediateQuotient_ne_bot P H g
    (claimBIntermediateQuotientSubgroup_ne_bot_of_two_le_commonCosetCount
      P H g hN)

end NontrivialIntermediateSubgroup

section PGroupInheritance

variable (p : ℕ)

/-- The Theorem-E period subgroup inherits the ambient p-group property. -/
theorem isPGroup_claimBPeriodSubgroup
    (hA : IsPGroup p (Multiplicative A)) (H : AddSubgroup A) :
    IsPGroup p (Multiplicative H) :=
  isPGroup_multiplicative_addSubgroup p hA H

/-- The intermediate preimage subgroup `K` inherits the ambient p-group
property. -/
theorem isPGroup_claimBIntermediateSubgroup
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) :
    IsPGroup p
      (Multiplicative (claimBIntermediateSubgroup P H g)) :=
  isPGroup_multiplicative_addSubgroup p hA
    (claimBIntermediateSubgroup P H g)

/-- The centered quotient subgroup `L ≤ A/H` is a p-group. -/
theorem isPGroup_claimBIntermediateQuotientSubgroup
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) :
    IsPGroup p
      (Multiplicative (claimBIntermediateQuotientSubgroup P H g)) := by
  have hQ : IsPGroup p (Multiplicative (A ⧸ H)) :=
    isPGroup_multiplicative_quotient p hA H
  exact isPGroup_multiplicative_addSubgroup p hQ
    (claimBIntermediateQuotientSubgroup P H g)

/-- The internal quotient `K/H` used by subgroup--quotient convolution is
also a p-group. -/
theorem isPGroup_claimBInternalQuotient
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) :
    IsPGroup p
      (Multiplicative
        (claimBIntermediateSubgroup P H g ⧸
          internalAddSubgroup H (claimBIntermediateSubgroup P H g))) := by
  have hK : IsPGroup p
      (Multiplicative (claimBIntermediateSubgroup P H g)) :=
    isPGroup_claimBIntermediateSubgroup p hA P H g
  exact isPGroup_multiplicative_quotient p hK
    (internalAddSubgroup H (claimBIntermediateSubgroup P H g))

end PGroupInheritance

section DavenportLength

/-- Subgroup--quotient convolution bounds the intermediate `d*(K)` by the
canonical ambient `d*(A)`.  Thus the ambient Davenport budget supplies the
embedding length needed by the labelled subpartition assembly. -/
theorem pGroupDStar_claimBIntermediateSubgroup_le_of_ambient_budget
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A)
    (hambient : pGroupDStar A ≤ n) :
    pGroupDStar (claimBIntermediateSubgroup P H g) ≤ n := by
  let K := claimBIntermediateSubgroup P H g
  have hconv := pGroupDStar_subgroup_quotient_le K
  dsimp [K] at hconv ⊢
  omega

end DavenportLength

section CommonCoreOccurrenceInputs

/-- A common-core representative supplies a genuine labelled occurrence
in the common-core part of every original cell. -/
theorem Theorem21SetPartition.insideCoreCell_nonempty_of_mem_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H)
    (c : Fin n) :
    (P.insideCoreCell H c).Nonempty := by
  classical
  have hqCommon : QuotientAddGroup.mk' H g ∈
      quotientLayer H (P.commonCore H) :=
    (mem_quotientLayer_iff H (P.commonCore H) _).2 ⟨g, hg, rfl⟩
  have hqCell : QuotientAddGroup.mk' H g ∈
      quotientLayer H (P.coreValueCell H c) := by
    rw [P.quotientLayer_coreValueCell_eq_commonCore H c]
    exact hqCommon
  obtain ⟨x, hxCoreCell, -⟩ :=
    (mem_quotientLayer_iff H (P.coreValueCell H c) _).1 hqCell
  obtain ⟨i, hi, -⟩ :=
    (P.mem_coreValueCell_iff_exists_insideCoreCell H c x).1 hxCoreCell
  exact ⟨i, hi⟩

/-- Every labelled occurrence selected from an inside-core cell has value
in the single coset `g + K`. -/
theorem Theorem21SetPartition.insideCoreCell_value_mem_claimBCoset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H)
    (c : Fin n) (i : Occurrence xs)
    (hi : i ∈ P.insideCoreCell H c) :
    occurrenceValue xs i ∈
      addCosetFinset (claimBIntermediateSubgroup P H g) g := by
  have hiCore := (P.mem_insideCoreCell_iff H c i).1 hi |>.2
  exact commonCore_subset_addCosetFinset_claimBIntermediateSubgroup
    P H g hg hiCore

/-- The common-core representative therefore gives the cellwise labelled
choice used to retain one term from every omitted original layer. -/
noncomputable def Theorem21SetPartition.claimBCellCosetOccurrenceChoice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H) :
    P.CellCosetOccurrenceChoice
      (claimBIntermediateSubgroup P H g) g :=
  P.cellCosetOccurrenceChoice
    (claimBIntermediateSubgroup P H g) g fun c ↦ by
      obtain ⟨i, hi⟩ := P.insideCoreCell_nonempty_of_mem_commonCore H g hg c
      exact ⟨i, (P.mem_insideCoreCell_iff H c i).1 hi |>.1,
        P.insideCoreCell_value_mem_claimBCoset H g hg c i hi⟩

end CommonCoreOccurrenceInputs

section UnusedOccurrences

/-- In the non-large branch the Theorem-E period cannot be trivial.  This
uses the source-faithful output only through its proved projected endpoint;
the required `n ≤ |S'|` follows from nonempty setpartition cells. -/
theorem GMOTheoremESourceOutput.period_ne_bot_of_not_large
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    out.H ≠ ⊥ := by
  intro hH
  apply hnotLarge
  exact out.toProjected.largeAlternative_of_H_eq_bot hH
    out.partition.numCells_le_length

/-- Source-faithful Theorem E's nontrivial-period clause, in support form:
every labelled occurrence outside the common core belongs to the replacement
support. -/
theorem GMOTheoremESourceOutput.outsideCommonCore_subset_support_of_ne_bot
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I) (hH : out.H ≠ ⊥) :
    (Finset.univ : Selection xs) \
        out.partition.occurrencesInCommonCore out.H ⊆
      out.partition.support := by
  intro i hi
  by_contra hisupport
  have hcore := out.unused_mem_commonCore hH i hisupport
  have hnotcore : occurrenceValue xs i ∉
      out.partition.commonCore out.H := by
    intro hmem
    exact (Finset.mem_sdiff.mp hi).2
      ((out.partition.mem_occurrencesInCommonCore_iff out.H i).2 hmem)
  exact hnotcore hcore

/-- Non-large source-faithful Theorem E therefore supplies the preceding
support inclusion without an extra period hypothesis. -/
theorem GMOTheoremESourceOutput.outsideCommonCore_subset_support
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    (Finset.univ : Selection xs) \
        out.partition.occurrencesInCommonCore out.H ⊆
      out.partition.support :=
  out.outsideCommonCore_subset_support_of_ne_bot
    (out.period_ne_bot_of_not_large hnotLarge)

/-- Consequently every labelled source occurrence outside the replacement
support lies in `g + K`.  The `H ≠ ⊥` guard is exactly the guard present in
source Theorem E and is discharged by the non-large branch. -/
theorem GMOTheoremESourceOutput.unused_value_mem_claimBCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (g : A) (hg : g ∈ out.partition.commonCore out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition)
    (i : Occurrence xs) (hi : i ∉ out.partition.support) :
    occurrenceValue xs i ∈
      addCosetFinset
        (claimBIntermediateSubgroup out.partition out.H g) g := by
  have hiCore : occurrenceValue xs i ∈
      out.partition.commonCore out.H := by
    by_contra hnotCore
    have hiOutside : i ∈
        (Finset.univ : Selection xs) \
          out.partition.occurrencesInCommonCore out.H := by
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_univ i, fun hiOccurrenceCore ↦
        hnotCore
          ((out.partition.mem_occurrencesInCommonCore_iff out.H i).1
            hiOccurrenceCore)⟩
    exact hi (out.outsideCommonCore_subset_support hnotLarge hiOutside)
  exact commonCore_subset_addCosetFinset_claimBIntermediateSubgroup
    out.partition out.H g hg hiCore

end UnusedOccurrences

end GaoLean

#print axioms GaoLean.claimBIntermediateSubgroup_ne_bot_of_two_le_commonCosetCount
#print axioms GaoLean.isPGroup_claimBIntermediateSubgroup
#print axioms GaoLean.isPGroup_claimBIntermediateQuotientSubgroup
#print axioms GaoLean.isPGroup_claimBInternalQuotient
#print axioms GaoLean.pGroupDStar_claimBIntermediateSubgroup_le_of_ambient_budget
#print axioms GaoLean.Theorem21SetPartition.insideCoreCell_nonempty_of_mem_commonCore
#print axioms GaoLean.GMOTheoremESourceOutput.period_ne_bot_of_not_large
#print axioms GaoLean.GMOTheoremESourceOutput.unused_value_mem_claimBCoset
