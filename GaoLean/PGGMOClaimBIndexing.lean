import GaoLean.PGGMOClaimBAssembly

/-!
# Honest indexing and block ledgers for ordinary GMO Claim B

The constructions in this module only reorder and slice the value cells of
the genuine embedded common-core partition.  In particular, no set of the
same cardinality is substituted for an original Theorem-E cell.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

omit [AddCommGroup A] [Fintype A] in
/-- A permutation which sends the first two indices to the prescribed,
distinct indices `j` and `k`.  The second swap is made after the first, so it
does not undo the image of zero. -/
def pairFrontPermutation {n : ℕ} (hn : 2 ≤ n) (j k : Fin n) (hjk : j ≠ k) :
    Equiv.Perm (Fin n) := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let tau : Equiv.Perm (Fin n) := Equiv.swap z j
  exact tau.trans (Equiv.swap (tau o) k)

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem pairFrontPermutation_apply_zero {n : ℕ} (hn : 2 ≤ n)
    (j k : Fin n) (hjk : j ≠ k) :
    pairFrontPermutation hn j k hjk ⟨0, by omega⟩ = j := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let tau : Equiv.Perm (Fin n) := Equiv.swap z j
  have hzo : z ≠ o := by
    intro h
    have := congrArg Fin.val h
    simp [z, o] at this
  have htauz : tau z = j := Equiv.swap_apply_left z j
  have hjtauo : j ≠ tau o := by
    intro h
    apply hzo
    apply tau.injective
    exact htauz.trans h
  change (Equiv.swap (tau o) k) (tau z) = j
  rw [htauz]
  exact Equiv.swap_apply_of_ne_of_ne hjtauo hjk

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem pairFrontPermutation_apply_one {n : ℕ} (hn : 2 ≤ n)
    (j k : Fin n) (hjk : j ≠ k) :
    pairFrontPermutation hn j k hjk ⟨1, by omega⟩ = k := by
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let tau : Equiv.Perm (Fin n) := Equiv.swap z j
  change (Equiv.swap (tau o) k) (tau o) = k
  exact Equiv.swap_apply_left (tau o) k

omit [AddCommGroup A] [Fintype A] in
/-- An honest embedding of `r` original cells whose first two images are the
prescribed distinct original indices.  The hypothesis `2 ≤ r` deliberately
excludes the `r = 0, 1` branches: Claim B's two distinguished layers do not
exist in those widths. -/
def pairFrontEmbedding {r n : ℕ} (hr : r ≤ n) (htwo : 2 ≤ r)
    (j k : Fin n) (hjk : j ≠ k) : Fin r ↪ Fin n :=
  (initialCellEmbedding hr).trans
    (pairFrontPermutation (le_trans htwo hr) j k hjk).toEmbedding

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem pairFrontEmbedding_apply_zero {r n : ℕ} (hr : r ≤ n)
    (htwo : 2 ≤ r) (j k : Fin n) (hjk : j ≠ k) :
    pairFrontEmbedding hr htwo j k hjk ⟨0, by omega⟩ = j := by
  change pairFrontPermutation (le_trans htwo hr) j k hjk ⟨0, by omega⟩ = j
  exact pairFrontPermutation_apply_zero (le_trans htwo hr) j k hjk

omit [AddCommGroup A] [Fintype A] in
@[simp]
theorem pairFrontEmbedding_apply_one {r n : ℕ} (hr : r ≤ n)
    (htwo : 2 ≤ r) (j k : Fin n) (hjk : j ≠ k) :
    pairFrontEmbedding hr htwo j k hjk ⟨1, by omega⟩ = k := by
  change pairFrontPermutation (le_trans htwo hr) j k hjk ⟨1, by omega⟩ = k
  exact pairFrontPermutation_apply_one (le_trans htwo hr) j k hjk

omit [AddCommGroup A] [Fintype A] in
theorem card_selectedCellIndices {r n : ℕ} (e : Fin r ↪ Fin n) :
    (selectedCellIndices e).card = r := by
  classical
  unfold selectedCellIndices
  rw [Finset.card_image_of_injective Finset.univ e.injective]
  simp

omit [AddCommGroup A] [Fintype A] in
theorem pairFront_mem_selected {r n : ℕ} (hr : r ≤ n) (htwo : 2 ≤ r)
    (j k : Fin n) (hjk : j ≠ k) :
    j ∈ selectedCellIndices (pairFrontEmbedding hr htwo j k hjk) ∧
      k ∈ selectedCellIndices (pairFrontEmbedding hr htwo j k hjk) := by
  constructor
  · rw [mem_selectedCellIndices_iff]
    exact ⟨⟨0, by omega⟩, pairFrontEmbedding_apply_zero hr htwo j k hjk⟩
  · rw [mem_selectedCellIndices_iff]
    exact ⟨⟨1, by omega⟩, pairFrontEmbedding_apply_one hr htwo j k hjk⟩

omit [AddCommGroup A] [Fintype A] in
theorem pairFront_not_mem_unselected {r n : ℕ} (hr : r ≤ n) (htwo : 2 ≤ r)
    (j k : Fin n) (hjk : j ≠ k) :
    j ∉ unselectedCellIndices (pairFrontEmbedding hr htwo j k hjk) ∧
      k ∉ unselectedCellIndices (pairFrontEmbedding hr htwo j k hjk) := by
  have hsel := pairFront_mem_selected hr htwo j k hjk
  simp only [unselectedCellIndices, Finset.mem_sdiff, Finset.mem_univ, true_and,
    not_not]
  exact hsel

omit [AddCommGroup A] [Fintype A] in
/-- Exact selected-index ledger: the distinguished pair followed by the
genuine images of indices `2, ..., r-1`. -/
theorem mem_pairFront_selected_iff {r n : ℕ} (hr : r ≤ n) (htwo : 2 ≤ r)
    (j k c : Fin n) (hjk : j ≠ k) :
    c ∈ selectedCellIndices (pairFrontEmbedding hr htwo j k hjk) ↔
      c = j ∨ c = k ∨
        ∃ q : Fin r, 2 ≤ q.val ∧ pairFrontEmbedding hr htwo j k hjk q = c := by
  rw [mem_selectedCellIndices_iff]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hq0 : q.val = 0
    · left
      have hq : q = ⟨0, by omega⟩ := Fin.ext hq0
      rw [hq]
      exact pairFrontEmbedding_apply_zero hr htwo j k hjk
    by_cases hq1 : q.val = 1
    · right; left
      have hq : q = ⟨1, by omega⟩ := Fin.ext hq1
      rw [hq]
      exact pairFrontEmbedding_apply_one hr htwo j k hjk
    · right; right
      exact ⟨q, by omega, rfl⟩
  · rintro (hcj | hck | ⟨q, hq, hqc⟩)
    · exact ⟨⟨0, by omega⟩,
        (pairFrontEmbedding_apply_zero hr htwo j k hjk).trans hcj.symm⟩
    · exact ⟨⟨1, by omega⟩,
        (pairFrontEmbedding_apply_one hr htwo j k hjk).trans hck.symm⟩
    · exact ⟨q, hqc⟩

omit [AddCommGroup A] [Fintype A] in
/-- Exact complement ledger for the same embedding. -/
theorem mem_pairFront_unselected_iff {r n : ℕ} (hr : r ≤ n) (htwo : 2 ≤ r)
    (j k c : Fin n) (hjk : j ≠ k) :
    c ∈ unselectedCellIndices (pairFrontEmbedding hr htwo j k hjk) ↔
      c ≠ j ∧ c ≠ k ∧
        ∀ q : Fin r, 2 ≤ q.val → pairFrontEmbedding hr htwo j k hjk q ≠ c := by
  rw [mem_unselectedCellIndices_iff]
  constructor
  · intro hc
    refine ⟨?_, ?_, ?_⟩
    · intro hcj
      exact hc ⟨0, by omega⟩
        ((pairFrontEmbedding_apply_zero hr htwo j k hjk).trans hcj.symm)
    · intro hck
      exact hc ⟨1, by omega⟩
        ((pairFrontEmbedding_apply_one hr htwo j k hjk).trans hck.symm)
    · intro q hq
      exact hc q
  · rintro ⟨hcj, hck, htail⟩ q
    by_cases hq0 : q.val = 0
    · have hq : q = ⟨0, by omega⟩ := Fin.ext hq0
      rw [hq, pairFrontEmbedding_apply_zero]
      exact hcj.symm
    by_cases hq1 : q.val = 1
    · have hq : q = ⟨1, by omega⟩ := Fin.ext hq1
      rw [hq, pairFrontEmbedding_apply_one]
      exact hck.symm
    · exact htail q (by omega)

/-- Ordered value cells of an honest embedded common-core partition. -/
noncomputable def Theorem21SetPartition.embeddedCoreValueCells
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) : List (Finset A) :=
  List.ofFn fun q : Fin r ↦ P.coreValueCell H (e q)

@[simp]
theorem Theorem21SetPartition.length_embeddedCoreValueCells
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) :
    (P.embeddedCoreValueCells H e).length = r := by
  simp [Theorem21SetPartition.embeddedCoreValueCells]

/-- The two distinguished leading layers. -/
noncomputable def Theorem21SetPartition.claimBFrontBlock
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) : List (Finset A) :=
  (P.embeddedCoreValueCells H e).take 2

/-- The subsequent block assigned to the `H`-stage saturation argument. -/
noncomputable def Theorem21SetPartition.claimBHBlock
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) (hLen : ℕ) : List (Finset A) :=
  ((P.embeddedCoreValueCells H e).drop 2).take hLen

/-- The subsequent block assigned to the `L`-stage saturation argument. -/
noncomputable def Theorem21SetPartition.claimBLBlock
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) (hLen lLen : ℕ) : List (Finset A) :=
  ((P.embeddedCoreValueCells H e).drop (2 + hLen)).take lLen

/-- The final padding block.  It is still a literal slice of the original
embedded value-cell ledger. -/
noncomputable def Theorem21SetPartition.claimBPaddingBlock
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n)
    (hLen lLen padLen : ℕ) : List (Finset A) :=
  ((P.embeddedCoreValueCells H e).drop (2 + hLen + lLen)).take padLen

theorem Theorem21SetPartition.length_claimBFrontBlock
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) (htwo : 2 ≤ r) :
    (P.claimBFrontBlock H e).length = 2 := by
  simp [Theorem21SetPartition.claimBFrontBlock,
    Theorem21SetPartition.embeddedCoreValueCells, Nat.min_eq_left htwo]

theorem Theorem21SetPartition.length_claimBHBlock
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r) :
    (P.claimBHBlock H e hLen).length = hLen := by
  simp [Theorem21SetPartition.claimBHBlock,
    Theorem21SetPartition.embeddedCoreValueCells]
  omega

theorem Theorem21SetPartition.length_claimBLBlock
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r) :
    (P.claimBLBlock H e hLen lLen).length = lLen := by
  simp [Theorem21SetPartition.claimBLBlock,
    Theorem21SetPartition.embeddedCoreValueCells]
  omega

theorem Theorem21SetPartition.length_claimBPaddingBlock
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r) :
    (P.claimBPaddingBlock H e hLen lLen padLen).length = padLen := by
  simp [Theorem21SetPartition.claimBPaddingBlock,
    Theorem21SetPartition.embeddedCoreValueCells]
  omega

/-- Exact four-block decomposition of the genuine ordered value-cell ledger. -/
theorem Theorem21SetPartition.claimB_blocks_append
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r) :
    P.claimBFrontBlock H e ++ P.claimBHBlock H e hLen ++
        P.claimBLBlock H e hLen lLen ++
        P.claimBPaddingBlock H e hLen lLen padLen =
      P.embeddedCoreValueCells H e := by
  let values := P.embeddedCoreValueCells H e
  have hpad : (values.drop (2 + hLen + lLen)).take padLen =
      values.drop (2 + hLen + lLen) := by
    rw [List.take_eq_self_iff]
    simp [values, Theorem21SetPartition.embeddedCoreValueCells]
    omega
  change values.take 2 ++ (values.drop 2).take hLen ++
      (values.drop (2 + hLen)).take lLen ++
      (values.drop (2 + hLen + lLen)).take padLen = values
  rw [hpad]
  simp only [List.append_assoc]
  rw [List.drop_take_append_drop values (2 + hLen) lLen]
  rw [List.drop_take_append_drop values 2 hLen]
  exact List.take_append_drop 2 values

theorem Theorem21SetPartition.getElem_claimBFrontBlock
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) (htwo : 2 ≤ r)
    (q : ℕ) (hq : q < 2) :
    (P.claimBFrontBlock H e)[q]'(by
      rw [P.length_claimBFrontBlock H e htwo]
      exact hq) = P.coreValueCell H (e ⟨q, by omega⟩) := by
  simp [Theorem21SetPartition.claimBFrontBlock,
    Theorem21SetPartition.embeddedCoreValueCells]

theorem Theorem21SetPartition.getElem_claimBHBlock
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r)
    (q : ℕ) (hq : q < hLen) :
    (P.claimBHBlock H e hLen)[q]'(by
      rw [P.length_claimBHBlock H e hsum]
      exact hq) = P.coreValueCell H (e ⟨2 + q, by omega⟩) := by
  simp [Theorem21SetPartition.claimBHBlock,
    Theorem21SetPartition.embeddedCoreValueCells]

theorem Theorem21SetPartition.getElem_claimBLBlock
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r)
    (q : ℕ) (hq : q < lLen) :
    (P.claimBLBlock H e hLen lLen)[q]'(by
      rw [P.length_claimBLBlock H e hsum]
      exact hq) = P.coreValueCell H (e ⟨2 + hLen + q, by omega⟩) := by
  simp [Theorem21SetPartition.claimBLBlock,
    Theorem21SetPartition.embeddedCoreValueCells]

theorem Theorem21SetPartition.getElem_claimBPaddingBlock
    {xs : List A} {n m r hLen lLen padLen : ℕ}
    (P : Theorem21SetPartition xs n m) (H : AddSubgroup A)
    (e : Fin r ↪ Fin n) (hsum : 2 + hLen + lLen + padLen = r)
    (q : ℕ) (hq : q < padLen) :
    (P.claimBPaddingBlock H e hLen lLen padLen)[q]'(by
      rw [P.length_claimBPaddingBlock H e hsum]
      exact hq) =
        P.coreValueCell H (e ⟨2 + hLen + lLen + q, by omega⟩) := by
  simp [Theorem21SetPartition.claimBPaddingBlock,
    Theorem21SetPartition.embeddedCoreValueCells]

/-- For the prescribed pair-front embedding, the first block consists of the
actual core value cells of `j` and `k`, in that order. -/
theorem Theorem21SetPartition.claimBFrontBlock_pairFront
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (hr : r ≤ n) (htwo : 2 ≤ r)
    (j k : Fin n) (hjk : j ≠ k) :
    P.claimBFrontBlock H (pairFrontEmbedding hr htwo j k hjk) =
      [P.coreValueCell H j, P.coreValueCell H k] := by
  apply List.ext_get
  · simp [P.length_claimBFrontBlock H
      (pairFrontEmbedding hr htwo j k hjk) htwo]
  · intro q hqLeft hqRight
    have hq : q < 2 := by simpa using hqRight
    have hq_cases : q = 0 ∨ q = 1 := by omega
    rcases hq_cases with hq | hq
    · subst q
      simpa using P.getElem_claimBFrontBlock H
        (pairFrontEmbedding hr htwo j k hjk) htwo 0 (by omega)
    · subst q
      simpa using P.getElem_claimBFrontBlock H
        (pairFrontEmbedding hr htwo j k hjk) htwo 1 (by omega)

end GaoLean
