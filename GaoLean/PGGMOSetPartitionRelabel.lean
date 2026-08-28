import GaoLean.PGGMOTheorem21

/-!
# Relabelling only the used support of a Theorem 2.1 setpartition

The relabelling map in this module is deliberately defined only on the
labelled occurrences that occur in the setpartition support.  This is the
source-faithful interface needed when an auxiliary sequence contains padded
values that have no corresponding source label: unused auxiliary positions
never have to be mapped.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

omit [AddCommGroup A] [Fintype A] in
/-- Every occurrence in one cell belongs to the labelled support. -/
theorem Theorem21SetPartition.cell_subset_support
    {ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (c : Fin r) : Q.cells c ⊆ Q.support := by
  intro q hq
  exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, hq⟩

omit [AddCommGroup A] [Fintype A] in
/-- Restrict a support embedding to one cell.  Its domain is the cell
subtype, while its intermediate argument to `f` carries the proved support
membership. -/
def Theorem21SetPartition.cellSupportRelabelEmbedding
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (c : Fin r) : {q : Occurrence ys // q ∈ Q.cells c} ↪ Occurrence xs where
  toFun q := f ⟨q.1, Q.cell_subset_support c q.2⟩
  inj' := by
    intro q q' h
    have hs := f.injective h
    exact Subtype.ext
      (congrArg
        (fun z : {q : Occurrence ys // q ∈ Q.support} ↦ z.1) hs)

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem Theorem21SetPartition.cellSupportRelabelEmbedding_apply
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (c : Fin r) (q : {q : Occurrence ys // q ∈ Q.cells c}) :
    Q.cellSupportRelabelEmbedding f c q =
      f ⟨q.1, Q.cell_subset_support c q.2⟩ := rfl

/-- Cell family obtained by mapping precisely the labelled occurrences in
each used cell through the support embedding. -/
noncomputable def Theorem21SetPartition.supportRelabelCells
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs) :
    Fin r → Selection xs := by
  classical
  exact fun c ↦ (Q.cells c).attach.map
    (Q.cellSupportRelabelEmbedding f c)

/-- The union of the relabelled cells is exactly the image of the old
support.  No occurrence outside `Q.support` enters the construction. -/
theorem Theorem21SetPartition.biUnion_supportRelabelCells
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs) :
    Finset.univ.biUnion (Q.supportRelabelCells f) =
      Q.support.attach.map f := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨c, -, hic⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hic
    apply Finset.mem_map.mpr
    refine ⟨⟨q.1, Q.cell_subset_support c q.2⟩, by simp, ?_⟩
    simpa [Theorem21SetPartition.supportRelabelCells] using hqi
  · intro hi
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hi
    obtain ⟨c, -, hqc⟩ := Finset.mem_biUnion.mp q.2
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ c, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨q.1, hqc⟩, by simp, ?_⟩
    change f ⟨q.1, Q.cell_subset_support c hqc⟩ = i
    calc
      f ⟨q.1, Q.cell_subset_support c hqc⟩ = f q := by
        congr 1
      _ = i := hqi

/-- Relabel a setpartition using only an embedding of its actual support.
The hypothesis says that the source value at every used auxiliary label is
preserved by the embedding. -/
noncomputable def Theorem21SetPartition.supportRelabel
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (hvalue : ∀ q : {q : Occurrence ys // q ∈ Q.support},
      occurrenceValue xs (f q) = occurrenceValue ys q.1) :
    Theorem21SetPartition xs r m := by
  classical
  refine {
    cells := Q.supportRelabelCells f
    cells_nonempty := ?_
    cells_pairwise_disjoint := ?_
    value_injective := ?_
    card_support := ?_
  }
  · intro c
    obtain ⟨q, hq⟩ := Q.cells_nonempty c
    refine ⟨f ⟨q, Q.cell_subset_support c hq⟩, ?_⟩
    apply Finset.mem_map.mpr
    exact ⟨⟨q, hq⟩, by simp, rfl⟩
  · intro c d hcd
    rw [Finset.disjoint_left]
    intro i hic hid
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hic
    obtain ⟨q', -, hq'i⟩ := Finset.mem_map.mp hid
    have hff :
        f ⟨q.1, Q.cell_subset_support c q.2⟩ =
          f ⟨q'.1, Q.cell_subset_support d q'.2⟩ := by
      exact hqi.trans hq'i.symm
    have hs := f.injective hff
    have hqq : q.1 = q'.1 := congrArg Subtype.val hs
    exact (Finset.disjoint_left.mp (Q.cells_pairwise_disjoint hcd))
      q.2 (hqq ▸ q'.2)
  · intro c i hi j hj hij
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hi
    obtain ⟨q', -, hq'j⟩ := Finset.mem_map.mp hj
    have hsourceValue :
        occurrenceValue ys q.1 = occurrenceValue ys q'.1 := by
      calc
        occurrenceValue ys q.1 =
            occurrenceValue xs
              (f ⟨q.1, Q.cell_subset_support c q.2⟩) :=
          (hvalue ⟨q.1, Q.cell_subset_support c q.2⟩).symm
        _ = occurrenceValue xs i := congrArg (occurrenceValue xs) hqi
        _ = occurrenceValue xs j := hij
        _ = occurrenceValue xs
              (f ⟨q'.1, Q.cell_subset_support c q'.2⟩) :=
          congrArg (occurrenceValue xs) hq'j.symm
        _ = occurrenceValue ys q'.1 :=
          hvalue ⟨q'.1, Q.cell_subset_support c q'.2⟩
    have hqq : q.1 = q'.1 :=
      Q.value_injective c q.2 q'.2 hsourceValue
    calc
      i = f ⟨q.1, Q.cell_subset_support c q.2⟩ := hqi.symm
      _ = f ⟨q'.1, Q.cell_subset_support c q'.2⟩ := by
        exact congrArg f (Subtype.ext hqq)
      _ = j := hq'j
  · rw [Q.biUnion_supportRelabelCells f]
    simpa using Q.card_support_eq

@[simp]
theorem Theorem21SetPartition.cells_supportRelabel
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (hvalue : ∀ q : {q : Occurrence ys // q ∈ Q.support},
      occurrenceValue xs (f q) = occurrenceValue ys q.1)
    (c : Fin r) :
    (Q.supportRelabel f hvalue).cells c =
      (Q.cells c).attach.map (Q.cellSupportRelabelEmbedding f c) := rfl

/-- Exact support image ledger for support-only relabelling. -/
theorem Theorem21SetPartition.support_supportRelabel
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (hvalue : ∀ q : {q : Occurrence ys // q ∈ Q.support},
      occurrenceValue xs (f q) = occurrenceValue ys q.1) :
    (Q.supportRelabel f hvalue).support = Q.support.attach.map f := by
  classical
  change Finset.univ.biUnion (Q.supportRelabelCells f) = _
  exact Q.biUnion_supportRelabelCells f

/-- Each relabelled cell has exactly the same finite value set as the old
cell. -/
theorem Theorem21SetPartition.valueCell_supportRelabel
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (hvalue : ∀ q : {q : Occurrence ys // q ∈ Q.support},
      occurrenceValue xs (f q) = occurrenceValue ys q.1)
    (c : Fin r) :
    (Q.supportRelabel f hvalue).valueCell c = Q.valueCell c := by
  classical
  ext a
  constructor
  · intro ha
    unfold Theorem21SetPartition.valueCell at ha ⊢
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [Q.cells_supportRelabel f hvalue c] at hi
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hi
    apply Finset.mem_image.mpr
    refine ⟨q.1, q.2, ?_⟩
    change f ⟨q.1, Q.cell_subset_support c q.2⟩ = i at hqi
    calc
      occurrenceValue ys q.1 =
          occurrenceValue xs
            (f ⟨q.1, Q.cell_subset_support c q.2⟩) :=
        (hvalue ⟨q.1, Q.cell_subset_support c q.2⟩).symm
      _ = occurrenceValue xs i := congrArg (occurrenceValue xs) hqi
  · intro ha
    unfold Theorem21SetPartition.valueCell at ha ⊢
    obtain ⟨q, hqc, hqa⟩ := Finset.mem_image.mp ha
    let qs : {q : Occurrence ys // q ∈ Q.support} :=
      ⟨q, Q.cell_subset_support c hqc⟩
    apply Finset.mem_image.mpr
    refine ⟨f qs, ?_, ?_⟩
    · rw [Q.cells_supportRelabel f hvalue c]
      apply Finset.mem_map.mpr
      exact ⟨⟨q, hqc⟩, by simp, rfl⟩
    · calc
        occurrenceValue xs (f qs) = occurrenceValue ys q := hvalue qs
        _ = a := hqa

/-- Exact ordered value-cell ledger. -/
theorem Theorem21SetPartition.valueCells_supportRelabel
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (hvalue : ∀ q : {q : Occurrence ys // q ∈ Q.support},
      occurrenceValue xs (f q) = occurrenceValue ys q.1) :
    (Q.supportRelabel f hvalue).valueCells = Q.valueCells := by
  classical
  simp [Theorem21SetPartition.valueCells,
    Q.valueCell_supportRelabel f hvalue]

/-- Support-only relabelling preserves the full layer sumset exactly. -/
theorem Theorem21SetPartition.sumset_supportRelabel
    {xs ys : List A} {r m : ℕ} (Q : Theorem21SetPartition ys r m)
    (f : {q : Occurrence ys // q ∈ Q.support} ↪ Occurrence xs)
    (hvalue : ∀ q : {q : Occurrence ys // q ∈ Q.support},
      occurrenceValue xs (f q) = occurrenceValue ys q.1) :
    (Q.supportRelabel f hvalue).sumset = Q.sumset := by
  classical
  unfold Theorem21SetPartition.sumset
  rw [Q.valueCells_supportRelabel f hvalue]

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.support_supportRelabel
#print axioms GaoLean.Theorem21SetPartition.valueCell_supportRelabel
#print axioms GaoLean.Theorem21SetPartition.sumset_supportRelabel
