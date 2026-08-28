import GaoLean.PGGMOClaimBCase1

/-!
# Occurrence-faithful quotient infrastructure for ordinary GMO Claim B

The quotient sequence below is indexed by the literal labelled occurrences
outside the support of the Claim-B partition.  Its entries are displacements
from the Claim-B center `g`, modulo `K`.  The source-position embedding is
kept explicitly, so equal values at different positions are never identified.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- All labelled source occurrences not used by the genuine Claim-B
partition. -/
noncomputable def OrdinaryGMOClaimBOutput.remainingOccurrences
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) : Selection xs := by
  classical
  exact (Finset.univ : Selection xs) \ W.partition.support

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_remainingOccurrences_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (i : Occurrence xs) :
    i ∈ W.remainingOccurrences ↔ i ∉ W.partition.support := by
  classical
  simp [OrdinaryGMOClaimBOutput.remainingOccurrences]

/-- Exact size of the literal complement of the Claim-B support. -/
theorem OrdinaryGMOClaimBOutput.card_remainingOccurrences
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.remainingOccurrences.card = xs.length - W.supportCard := by
  classical
  simpa [OrdinaryGMOClaimBOutput.remainingOccurrences] using
    W.partition.card_unused

/-- A deterministic ledger of the remaining labelled source positions. -/
noncomputable def OrdinaryGMOClaimBOutput.remainingOccurrenceList
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) : List (Occurrence xs) :=
  W.remainingOccurrences.toList

@[simp]
theorem OrdinaryGMOClaimBOutput.length_remainingOccurrenceList
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.remainingOccurrenceList.length = W.remainingOccurrences.card := by
  simp [OrdinaryGMOClaimBOutput.remainingOccurrenceList]

/-- Quotient displacement of one original labelled occurrence. -/
def OrdinaryGMOClaimBOutput.quotientDisplacement
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (i : Occurrence xs) : A ⧸ W.K :=
  QuotientAddGroup.mk' W.K (occurrenceValue xs i - W.g)

/-- The occurrence-faithful quotient sequence of the complement.  Mapping a
list, rather than a value-set, retains equal quotient values at distinct
source positions. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientDisplacementSequence
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) : List (A ⧸ W.K) :=
  W.remainingOccurrenceList.map W.quotientDisplacement

@[simp]
theorem OrdinaryGMOClaimBOutput.length_quotientDisplacementSequence
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.quotientDisplacementSequence.length = W.remainingOccurrences.card := by
  simp [OrdinaryGMOClaimBOutput.quotientDisplacementSequence]

@[simp]
theorem OrdinaryGMOClaimBOutput.length_quotientDisplacementSequence_eq
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.quotientDisplacementSequence.length = xs.length - W.supportCard := by
  rw [W.length_quotientDisplacementSequence,
    W.card_remainingOccurrences]

/-- Convert a quotient-sequence position to the corresponding position of
the remaining-occurrence ledger. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientListIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) :
    Fin W.remainingOccurrenceList.length :=
  ⟨q.val, by simpa [OrdinaryGMOClaimBOutput.quotientDisplacementSequence]
    using q.isLt⟩

/-- The original labelled occurrence underlying a quotient-sequence
position. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientSourceOccurrence
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) : Occurrence xs :=
  W.remainingOccurrenceList.get (W.quotientListIndex q)

/-- Distinct quotient-sequence positions come from distinct original
positions.  This deliberately says nothing about distinctness of values. -/
theorem OrdinaryGMOClaimBOutput.quotientSourceOccurrence_injective
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Function.Injective W.quotientSourceOccurrence := by
  intro q r hqr
  change W.remainingOccurrenceList.get (W.quotientListIndex q) =
    W.remainingOccurrenceList.get (W.quotientListIndex r) at hqr
  have hindex : W.quotientListIndex q = W.quotientListIndex r :=
    W.remainingOccurrences.nodup_toList.injective_get hqr
  apply Fin.ext
  exact congrArg
    (fun x : Fin W.remainingOccurrenceList.length ↦ x.val) hindex

/-- The source-position embedding used for every quotient pullback. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientSourceEmbedding
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Occurrence W.quotientDisplacementSequence ↪ Occurrence xs where
  toFun := W.quotientSourceOccurrence
  inj' := W.quotientSourceOccurrence_injective

theorem OrdinaryGMOClaimBOutput.quotientSourceOccurrence_mem_remaining
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) :
    W.quotientSourceOccurrence q ∈ W.remainingOccurrences := by
  have hmem : W.remainingOccurrenceList.get (W.quotientListIndex q) ∈
      W.remainingOccurrenceList := List.get_mem _ _
  change W.remainingOccurrenceList.get (W.quotientListIndex q) ∈
    W.remainingOccurrences
  exact Finset.mem_toList.mp hmem

/-- The source embedding enumerates the complement exactly. -/
theorem OrdinaryGMOClaimBOutput.map_univ_quotientSourceEmbedding
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    (Finset.univ : Selection W.quotientDisplacementSequence).map
        W.quotientSourceEmbedding = W.remainingOccurrences := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hi
    exact W.quotientSourceOccurrence_mem_remaining q
  · intro hi
    have hiList : i ∈ W.remainingOccurrenceList := by
      simpa [OrdinaryGMOClaimBOutput.remainingOccurrenceList] using hi
    obtain ⟨q, hq⟩ := List.mem_iff_get.mp hiList
    let q' : Occurrence W.quotientDisplacementSequence :=
      ⟨q.val, by
        simpa [OrdinaryGMOClaimBOutput.quotientDisplacementSequence]
          using q.isLt⟩
    apply Finset.mem_map.mpr
    refine ⟨q', Finset.mem_univ _, ?_⟩
    simpa [OrdinaryGMOClaimBOutput.quotientSourceEmbedding,
      OrdinaryGMOClaimBOutput.quotientSourceOccurrence,
      OrdinaryGMOClaimBOutput.quotientListIndex, q'] using hq

/-- Quotient values are exactly the displacements of their recorded source
occurrences. -/
theorem OrdinaryGMOClaimBOutput.occurrenceValue_quotientDisplacementSequence
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) :
    occurrenceValue W.quotientDisplacementSequence q =
      W.quotientDisplacement (W.quotientSourceOccurrence q) := by
  simp [occurrenceValue,
    OrdinaryGMOClaimBOutput.quotientDisplacementSequence,
    OrdinaryGMOClaimBOutput.quotientSourceOccurrence,
    OrdinaryGMOClaimBOutput.quotientListIndex]

/-- Displacement vanishes exactly for a value in the Claim-B coset. -/
theorem OrdinaryGMOClaimBOutput.quotientDisplacement_eq_zero_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (i : Occurrence xs) :
    W.quotientDisplacement i = 0 ↔
      occurrenceValue xs i ∈ addCosetFinset W.K W.g := by
  change (QuotientAddGroup.mk (occurrenceValue xs i - W.g) : A ⧸ W.K) = 0 ↔
    occurrenceValue xs i ∈ addCosetFinset W.K W.g
  rw [QuotientAddGroup.eq_zero_iff]
  exact (mem_addCosetFinset_iff W.K W.g (occurrenceValue xs i)).symm

theorem OrdinaryGMOClaimBOutput.quotientDisplacement_ne_zero_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (i : Occurrence xs) :
    W.quotientDisplacement i ≠ 0 ↔
      occurrenceValue xs i ∉ addCosetFinset W.K W.g := by
  exact not_congr (W.quotientDisplacement_eq_zero_iff i)

theorem OrdinaryGMOClaimBOutput.occurrenceValue_quotient_eq_zero_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) :
    occurrenceValue W.quotientDisplacementSequence q = 0 ↔
      occurrenceValue xs (W.quotientSourceOccurrence q) ∈
        addCosetFinset W.K W.g := by
  rw [W.occurrenceValue_quotientDisplacementSequence q,
    W.quotientDisplacement_eq_zero_iff]

theorem OrdinaryGMOClaimBOutput.occurrenceValue_quotient_ne_zero_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) :
    occurrenceValue W.quotientDisplacementSequence q ≠ 0 ↔
      occurrenceValue xs (W.quotientSourceOccurrence q) ∉
        addCosetFinset W.K W.g := by
  exact not_congr (W.occurrenceValue_quotient_eq_zero_iff q)

/-- Quotient multiplicity is counted by quotient-sequence positions, not by
the cardinality of a value-set. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    Selection W.quotientDisplacementSequence := by
  classical
  exact Finset.univ.filter fun q ↦
    occurrenceValue W.quotientDisplacementSequence q = z

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_quotientFiber_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K)
    (q : Occurrence W.quotientDisplacementSequence) :
    q ∈ W.quotientFiber z ↔
      occurrenceValue W.quotientDisplacementSequence q = z := by
  classical
  simp [OrdinaryGMOClaimBOutput.quotientFiber]

/-- The zero fiber pulls back to exactly the labelled remaining occurrences
in `g + K`. -/
theorem OrdinaryGMOClaimBOutput.map_zeroQuotientFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    (W.quotientFiber 0).map W.quotientSourceEmbedding =
      W.partition.unusedInAddCoset W.K W.g := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
    apply (W.partition.mem_unusedInAddCoset_iff W.K W.g _).2
    exact ⟨W.quotientSourceOccurrence_mem_remaining q |>
        (W.mem_remainingOccurrences_iff _).1,
      (W.occurrenceValue_quotient_eq_zero_iff q).1
        ((W.mem_quotientFiber_iff 0 q).1 hq)⟩
  · intro hi
    have hi' := (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1 hi
    have hiRemaining : i ∈ W.remainingOccurrences :=
      (W.mem_remainingOccurrences_iff i).2 hi'.1
    have hiRange : i ∈
        (Finset.univ : Selection W.quotientDisplacementSequence).map
          W.quotientSourceEmbedding := by
      rw [W.map_univ_quotientSourceEmbedding]
      exact hiRemaining
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hiRange
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, hqi⟩
    apply (W.mem_quotientFiber_iff 0 q).2
    apply (W.occurrenceValue_quotient_eq_zero_iff q).2
    change occurrenceValue xs (W.quotientSourceEmbedding q) ∈
      addCosetFinset W.K W.g
    rw [hqi]
    exact hi'.2

/-- Exact zero multiplicity and the paper's lower bound on it. -/
theorem OrdinaryGMOClaimBOutput.card_zeroQuotientFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    (W.quotientFiber 0).card =
      (W.partition.unusedInAddCoset W.K W.g).card := by
  have hcard := congrArg Finset.card W.map_zeroQuotientFiber
  simpa using hcard

theorem OrdinaryGMOClaimBOutput.zeroQuotientFiber_lower
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    n - pGroupDStar W.K + (xs.length - seed.card) ≤
      (W.quotientFiber 0).card := by
  rw [W.card_zeroQuotientFiber]
  exact W.remaining_in_coset

/-- Pull a quotient selection back to the original source positions. -/
noncomputable def OrdinaryGMOClaimBOutput.pullbackQuotientSelection
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (J : Selection W.quotientDisplacementSequence) : Selection xs :=
  J.map W.quotientSourceEmbedding

@[simp]
theorem OrdinaryGMOClaimBOutput.card_pullbackQuotientSelection
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (J : Selection W.quotientDisplacementSequence) :
    (W.pullbackQuotientSelection J).card = J.card := by
  simp [OrdinaryGMOClaimBOutput.pullbackQuotientSelection]

theorem OrdinaryGMOClaimBOutput.pullbackQuotientSelection_subset_remaining
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (J : Selection W.quotientDisplacementSequence) :
    W.pullbackQuotientSelection J ⊆ W.remainingOccurrences := by
  intro i hi
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hi
  exact W.quotientSourceOccurrence_mem_remaining q

/-- Pull back every cell of a quotient setpartition through the labelled
source-position embedding.  The result is a genuine partition of original
occurrences.  No assertion of injectivity between *values* of distinct
source positions is made. -/
noncomputable def OrdinaryGMOClaimBOutput.pullbackQuotientPartition
    {xs : List A} {seed : Selection xs} {n r m : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (Q : Theorem21SetPartition W.quotientDisplacementSequence r m) :
    Theorem21SetPartition xs r m := by
  classical
  let emb := W.quotientSourceEmbedding
  let cells : Fin r → Selection xs := fun c ↦ (Q.cells c).map emb
  refine {
    cells := cells
    cells_nonempty := ?_
    cells_pairwise_disjoint := ?_
    value_injective := ?_
    card_support := ?_
  }
  · intro c
    obtain ⟨q, hq⟩ := Q.cells_nonempty c
    exact ⟨emb q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  · intro c d hcd
    exact (Finset.disjoint_map emb).2 (Q.cells_pairwise_disjoint hcd)
  · intro c x hx y hy hxy
    obtain ⟨qx, hqx, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨qy, hqy, rfl⟩ := Finset.mem_map.mp hy
    have hqvalue : occurrenceValue W.quotientDisplacementSequence qx =
        occurrenceValue W.quotientDisplacementSequence qy := by
      rw [W.occurrenceValue_quotientDisplacementSequence,
        W.occurrenceValue_quotientDisplacementSequence]
      exact congrArg (fun a : A ↦ QuotientAddGroup.mk' W.K (a - W.g)) hxy
    exact congrArg emb (Q.value_injective c hqx hqy hqvalue)
  · have hsupport : Finset.univ.biUnion cells = Q.support.map emb := by
      ext i
      constructor
      · intro hi
        obtain ⟨c, -, hic⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨q, hq, hqi⟩ := Finset.mem_map.mp (by
          simpa [cells] using hic)
        apply Finset.mem_map.mpr
        refine ⟨q, ?_, hqi⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨c, Finset.mem_univ c, hq⟩
      · intro hi
        obtain ⟨q, hqSupport, hqi⟩ := Finset.mem_map.mp hi
        obtain ⟨c, -, hq⟩ := Finset.mem_biUnion.mp hqSupport
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_univ c, ?_⟩
        simpa [cells] using Finset.mem_map.mpr ⟨q, hq, hqi⟩
    rw [hsupport, Finset.card_map]
    exact Q.card_support

@[simp]
theorem OrdinaryGMOClaimBOutput.cells_pullbackQuotientPartition
    {xs : List A} {seed : Selection xs} {n r m : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (Q : Theorem21SetPartition W.quotientDisplacementSequence r m)
    (c : Fin r) :
    (W.pullbackQuotientPartition Q).cells c =
      (Q.cells c).map W.quotientSourceEmbedding := by
  rfl

theorem OrdinaryGMOClaimBOutput.support_pullbackQuotientPartition
    {xs : List A} {seed : Selection xs} {n r m : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (Q : Theorem21SetPartition W.quotientDisplacementSequence r m) :
    (W.pullbackQuotientPartition Q).support =
      Q.support.map W.quotientSourceEmbedding := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨c, -, hic⟩ := Finset.mem_biUnion.mp hi
    rw [W.cells_pullbackQuotientPartition Q] at hic
    obtain ⟨q, hq, hqi⟩ := Finset.mem_map.mp hic
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, hqi⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨c, Finset.mem_univ c, hq⟩
  · intro hi
    obtain ⟨q, hq, hqi⟩ := Finset.mem_map.mp hi
    obtain ⟨c, -, hqc⟩ := Finset.mem_biUnion.mp hq
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ c, ?_⟩
    rw [W.cells_pullbackQuotientPartition Q]
    exact Finset.mem_map.mpr ⟨q, hqc, hqi⟩

theorem OrdinaryGMOClaimBOutput.support_pullbackQuotientPartition_subset_remaining
    {xs : List A} {seed : Selection xs} {n r m : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (Q : Theorem21SetPartition W.quotientDisplacementSequence r m) :
    (W.pullbackQuotientPartition Q).support ⊆ W.remainingOccurrences := by
  rw [W.support_pullbackQuotientPartition Q]
  intro i hi
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hi
  exact W.quotientSourceOccurrence_mem_remaining q

/-- Properness of `K` makes the quotient genuinely nontrivial. -/
theorem OrdinaryGMOClaimBOutput.nontrivial_quotient_of_ne_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (hproper : W.K ≠ ⊤) :
    Nontrivial (A ⧸ W.K) := by
  have hex : ∃ a : A, a ∉ W.K := by
    by_contra h
    push_neg at h
    apply hproper
    exact top_unique fun a _ ↦ h a
  obtain ⟨a, ha⟩ := hex
  apply nontrivial_iff.mpr
  refine ⟨QuotientAddGroup.mk' W.K a, 0, ?_⟩
  intro hzero
  exact ha ((QuotientAddGroup.eq_zero_iff a).1 hzero)

/-- Since Claim B proves `K ≠ ⊥`, its quotient is a strictly smaller finite
ambient group for the later quotient-induction call. -/
theorem OrdinaryGMOClaimBOutput.natCard_quotient_lt
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Nat.card (A ⧸ W.K) < Nat.card A :=
  natCard_quotient_lt_of_addSubgroup_ne_bot W.K W.nontrivial

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_zeroQuotientFiber
#print axioms GaoLean.OrdinaryGMOClaimBOutput.pullbackQuotientPartition
#print axioms GaoLean.OrdinaryGMOClaimBOutput.natCard_quotient_lt
