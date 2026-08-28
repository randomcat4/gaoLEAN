import GaoLean.PGGMOTheorem21

/-!
# Claim B common-core and quotient-fiber ledger

This module adds the occurrence-faithful bookkeeping used in the proper
subgroup branch of the ordinary GMO induction.  It does not assert Claim B
or any remaining source theorem.  The statements below only identify the
labelled parts of a setpartition cell, their value images, and their fibers
modulo a subgroup.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Labelled occurrences of one cell whose values belong to the common
`H`-periodic core. -/
noncomputable def Theorem21SetPartition.insideCoreCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) : Selection xs := by
  classical
  exact (P.cells c).filter fun i ↦
    occurrenceValue xs i ∈ P.commonCore H

/-- Values of one cell that belong to the common core. -/
noncomputable def Theorem21SetPartition.coreValueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) : Finset A := by
  classical
  exact P.valueCell c ∩ P.commonCore H

/-- The labelled fiber of one cell above a quotient class modulo `H`. -/
noncomputable def Theorem21SetPartition.cosetSlice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) : Selection xs := by
  classical
  exact (P.cells c).filter fun i ↦
    QuotientAddGroup.mk' H (occurrenceValue xs i) = q

/-- The value-set fiber corresponding to `cosetSlice`. -/
noncomputable def Theorem21SetPartition.cosetValueSlice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) : Finset A := by
  classical
  exact (P.valueCell c).filter fun x ↦ QuotientAddGroup.mk' H x = q

@[simp]
theorem Theorem21SetPartition.mem_insideCoreCell_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (i : Occurrence xs) :
    i ∈ P.insideCoreCell H c ↔
      i ∈ P.cells c ∧ occurrenceValue xs i ∈ P.commonCore H := by
  classical
  simp [Theorem21SetPartition.insideCoreCell]

@[simp]
theorem Theorem21SetPartition.mem_coreValueCell_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (x : A) :
    x ∈ P.coreValueCell H c ↔
      x ∈ P.valueCell c ∧ x ∈ P.commonCore H := by
  classical
  simp [Theorem21SetPartition.coreValueCell]

@[simp]
theorem Theorem21SetPartition.mem_cosetSlice_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) (i : Occurrence xs) :
    i ∈ P.cosetSlice H c q ↔
      i ∈ P.cells c ∧
        QuotientAddGroup.mk' H (occurrenceValue xs i) = q := by
  classical
  simp [Theorem21SetPartition.cosetSlice]

@[simp]
theorem Theorem21SetPartition.mem_cosetValueSlice_iff
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) (x : A) :
    x ∈ P.cosetValueSlice H c q ↔
      x ∈ P.valueCell c ∧ QuotientAddGroup.mk' H x = q := by
  classical
  simp [Theorem21SetPartition.cosetValueSlice]

/-- Exact elementwise correspondence between the labelled common-core part
and the cell's value/core intersection. -/
theorem Theorem21SetPartition.mem_coreValueCell_iff_exists_insideCoreCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (x : A) :
    x ∈ P.coreValueCell H c ↔
      ∃ i ∈ P.insideCoreCell H c, occurrenceValue xs i = x := by
  classical
  constructor
  · intro hx
    have hx' := (P.mem_coreValueCell_iff H c x).1 hx
    obtain ⟨i, hi, hivalue⟩ := Finset.mem_image.mp hx'.1
    exact ⟨i, (P.mem_insideCoreCell_iff H c i).2
      ⟨hi, hivalue ▸ hx'.2⟩, hivalue⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' := (P.mem_insideCoreCell_iff H c i).1 hi
    exact (P.mem_coreValueCell_iff H c _).2
      ⟨Finset.mem_image.mpr ⟨i, hi'.1, rfl⟩, hi'.2⟩

/-- The same exact occurrence/value correspondence holds fiberwise modulo
`H`. -/
theorem Theorem21SetPartition.mem_cosetValueSlice_iff_exists_cosetSlice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) (x : A) :
    x ∈ P.cosetValueSlice H c q ↔
      ∃ i ∈ P.cosetSlice H c q, occurrenceValue xs i = x := by
  classical
  constructor
  · intro hx
    have hx' := (P.mem_cosetValueSlice_iff H c q x).1 hx
    obtain ⟨i, hi, hivalue⟩ := Finset.mem_image.mp hx'.1
    exact ⟨i, (P.mem_cosetSlice_iff H c q i).2
      ⟨hi, hivalue ▸ hx'.2⟩, hivalue⟩
  · rintro ⟨i, hi, rfl⟩
    have hi' := (P.mem_cosetSlice_iff H c q i).1 hi
    exact (P.mem_cosetValueSlice_iff H c q _).2
      ⟨Finset.mem_image.mpr ⟨i, hi'.1, rfl⟩, hi'.2⟩

/-- Cellwise value injectivity loses no labels on the common-core part. -/
theorem Theorem21SetPartition.card_insideCoreCell_eq_card_coreValueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    (P.insideCoreCell H c).card = (P.coreValueCell H c).card := by
  classical
  have hinj : Set.InjOn (occurrenceValue xs)
      (P.insideCoreCell H c : Set (Occurrence xs)) :=
    (P.value_injective c).mono (by
      intro i hi
      exact (P.mem_insideCoreCell_iff H c i).1 hi |>.1)
  let image : Finset A :=
    (P.insideCoreCell H c).image (occurrenceValue xs)
  have himage : image = P.coreValueCell H c := by
    ext x
    simpa [image] using
      (P.mem_coreValueCell_iff_exists_insideCoreCell H c x).symm
  calc
    (P.insideCoreCell H c).card = image.card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = (P.coreValueCell H c).card := congrArg Finset.card himage

/-- Cellwise value injectivity also loses no labels on a quotient fiber. -/
theorem Theorem21SetPartition.card_cosetSlice_eq_card_cosetValueSlice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) :
    (P.cosetSlice H c q).card = (P.cosetValueSlice H c q).card := by
  classical
  have hinj : Set.InjOn (occurrenceValue xs)
      (P.cosetSlice H c q : Set (Occurrence xs)) :=
    (P.value_injective c).mono (by
      intro i hi
      exact (P.mem_cosetSlice_iff H c q i).1 hi |>.1)
  let image : Finset A := (P.cosetSlice H c q).image (occurrenceValue xs)
  have himage : image = P.cosetValueSlice H c q := by
    ext x
    simpa [image] using
      (P.mem_cosetValueSlice_iff_exists_cosetSlice H c q x).symm
  calc
    (P.cosetSlice H c q).card = image.card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ = (P.cosetValueSlice H c q).card := congrArg Finset.card himage

/-- A labelled quotient fiber is nonempty exactly when its quotient class
is represented by the value cell. -/
theorem Theorem21SetPartition.cosetSlice_nonempty_iff_mem_quotientLayer
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (q : A ⧸ H) :
    (P.cosetSlice H c q).Nonempty ↔ q ∈ quotientLayer H (P.valueCell c) := by
  classical
  rw [← Finset.card_pos, P.card_cosetSlice_eq_card_cosetValueSlice,
    Finset.card_pos]
  constructor
  · rintro ⟨x, hx⟩
    have hx' := (P.mem_cosetValueSlice_iff H c q x).1 hx
    exact (mem_quotientLayer_iff H (P.valueCell c) q).2
      ⟨x, hx'.1, hx'.2⟩
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_quotientLayer_iff H (P.valueCell c) q).1 hq
    exact ⟨x, (P.mem_cosetValueSlice_iff H c q x).2 ⟨hx, hxq⟩⟩

/-- Periodicity makes the common-core cardinality exactly its number of
quotient classes times `|H|`. -/
theorem Theorem21SetPartition.card_commonCore_eq_natCard_mul_quotientLayer
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (P.commonCore H).card =
      Nat.card H * (quotientLayer H (P.commonCore H)).card := by
  exact card_eq_natCard_mul_card_quotientLayer_of_le_stabilizer
    H (P.commonCore H) (P.commonCore_periodic H)

/-- Consequently the quotient in the definition of `commonCosetCount` is
exact: there is no floor loss. -/
theorem Theorem21SetPartition.card_commonCore_eq_commonCosetCount_mul_natCard
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (P.commonCore H).card = P.commonCosetCount H * Nat.card H := by
  have hcard := P.card_commonCore_eq_natCard_mul_quotientLayer H
  have hdiv : Nat.card H ∣ (P.commonCore H).card := by
    refine ⟨(quotientLayer H (P.commonCore H)).card, ?_⟩
    exact hcard
  unfold Theorem21SetPartition.commonCosetCount
  exact (Nat.div_mul_cancel hdiv).symm

/-- Every common quotient class has a representative inside every cell's
literal value/core intersection, and there are no other classes there. -/
theorem Theorem21SetPartition.quotientLayer_coreValueCell_eq_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    quotientLayer H (P.coreValueCell H c) =
      quotientLayer H (P.commonCore H) := by
  classical
  apply Finset.Subset.antisymm
  · intro q hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_quotientLayer_iff H (P.coreValueCell H c) q).1 hq
    exact (mem_quotientLayer_iff H (P.commonCore H) q).2
      ⟨x, (P.mem_coreValueCell_iff H c x).1 hx |>.2, hxq⟩
  · intro q hq
    have hqcell := P.quotientLayer_commonCore_subset_valueCell H c hq
    obtain ⟨y, hycell, hyq⟩ :=
      (mem_quotientLayer_iff H (P.valueCell c) q).1 hqcell
    have hyqcore : QuotientAddGroup.mk' H y ∈
        quotientLayer H (P.commonCore H) := by
      simpa [hyq] using hq
    have hycore : y ∈ P.commonCore H :=
      (mem_quotientLayer_iff_of_le_stabilizer H (P.commonCore H)
        (P.commonCore_periodic H) y).1 hyqcore
    exact (mem_quotientLayer_iff H (P.coreValueCell H c) q).2
      ⟨y, (P.mem_coreValueCell_iff H c y).2 ⟨hycell, hycore⟩, hyq⟩

/-- The core part and the cell defect give the exact value-cell cardinality. -/
theorem Theorem21SetPartition.card_coreValueCell_add_cellExceptionDefect
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) :
    (P.coreValueCell H c).card + P.cellExceptionDefect H c =
      (P.valueCell c).card := by
  classical
  have hsub : P.coreValueCell H c ⊆ P.valueCell c := by
    intro x hx
    exact (P.mem_coreValueCell_iff H c x).1 hx |>.1
  have hle := Finset.card_le_card hsub
  unfold Theorem21SetPartition.cellExceptionDefect
  change (P.valueCell c ∩ P.commonCore H).card +
      ((P.valueCell c).card -
        (P.valueCell c ∩ P.commonCore H).card) =
      (P.valueCell c).card
  exact Nat.add_sub_of_le hle

/-- Summed exact ledger: common-core values plus Theorem E's exception
defect exhaust the replacement length. -/
theorem Theorem21SetPartition.sum_card_coreValueCell_add_exceptionDefect
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (∑ c : Fin n, (P.coreValueCell H c).card) +
        P.exceptionDefect H = m := by
  classical
  unfold Theorem21SetPartition.exceptionDefect
  rw [← Finset.sum_add_distrib]
  calc
    (∑ c : Fin n,
        ((P.coreValueCell H c).card + P.cellExceptionDefect H c)) =
        ∑ c : Fin n, (P.valueCell c).card := by
          apply Finset.sum_congr rfl
          intro c _
          exact P.card_coreValueCell_add_cellExceptionDefect H c
    _ = m := P.sum_card_valueCell

/-- The same exact ledger in labelled-occurrence form. -/
theorem Theorem21SetPartition.sum_card_insideCoreCell_add_exceptionDefect
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) :
    (∑ c : Fin n, (P.insideCoreCell H c).card) +
        P.exceptionDefect H = m := by
  classical
  rw [Finset.sum_congr rfl (fun c _ ↦
    P.card_insideCoreCell_eq_card_coreValueCell H c)]
  exact P.sum_card_coreValueCell_add_exceptionDefect H

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.mem_coreValueCell_iff_exists_insideCoreCell
#print axioms GaoLean.Theorem21SetPartition.mem_cosetValueSlice_iff_exists_cosetSlice
#print axioms GaoLean.Theorem21SetPartition.card_commonCore_eq_commonCosetCount_mul_natCard
#print axioms GaoLean.Theorem21SetPartition.quotientLayer_coreValueCell_eq_commonCore
#print axioms GaoLean.Theorem21SetPartition.sum_card_insideCoreCell_add_exceptionDefect
