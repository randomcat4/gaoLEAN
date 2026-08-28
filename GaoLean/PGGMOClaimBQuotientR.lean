import GaoLean.PGGMOClaimBQuotient

/-!
# The honest `R` ledger in the low quotient-multiplicity branch

`R` contains every nonzero occurrence of the genuine quotient displacement
sequence and exactly `dQ` chosen occurrences from its genuine zero fiber.
Artificial padding zeros are added only after the genuine `R`-subsequence is
formed, and a companion `Option` ledger keeps those artificial positions
separate from all source occurrences.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Literal nonzero positions of the quotient displacement sequence. -/
noncomputable def OrdinaryGMOClaimBOutput.nonzeroQuotientOccurrences
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Selection W.quotientDisplacementSequence := by
  classical
  exact Finset.univ \ W.quotientFiber 0

/-- The paper's `e`: the number of labelled nonzero quotient occurrences. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientRExceptionCount
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) : ℕ :=
  W.nonzeroQuotientOccurrences.card

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_nonzeroQuotientOccurrences_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (q : Occurrence W.quotientDisplacementSequence) :
    q ∈ W.nonzeroQuotientOccurrences ↔
      occurrenceValue W.quotientDisplacementSequence q ≠ 0 := by
  classical
  simp [OrdinaryGMOClaimBOutput.nonzeroQuotientOccurrences]

theorem OrdinaryGMOClaimBOutput.disjoint_nonzeroQuotientOccurrences_zeroFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Disjoint W.nonzeroQuotientOccurrences (W.quotientFiber 0) := by
  classical
  rw [Finset.disjoint_left]
  intro q hnonzero hzero
  exact ((W.mem_nonzeroQuotientOccurrences_iff q).1 hnonzero)
    ((W.mem_quotientFiber_iff 0 q).1 hzero)

theorem OrdinaryGMOClaimBOutput.nonzero_union_zeroFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.nonzeroQuotientOccurrences ∪ W.quotientFiber 0 = Finset.univ := by
  classical
  exact Finset.sdiff_union_of_subset (Finset.subset_univ _)

theorem OrdinaryGMOClaimBOutput.card_nonzero_add_card_zeroFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.quotientRExceptionCount + (W.quotientFiber 0).card =
      W.quotientDisplacementSequence.length := by
  have hcard := Finset.card_union_of_disjoint
    W.disjoint_nonzeroQuotientOccurrences_zeroFiber
  rw [W.nonzero_union_zeroFiber] at hcard
  simpa [OrdinaryGMOClaimBOutput.quotientRExceptionCount] using hcard.symm

/-- Canonically choose exactly `dQ` genuine positions from the zero fiber. -/
noncomputable def OrdinaryGMOClaimBOutput.chosenZeroQuotientOccurrences
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Selection W.quotientDisplacementSequence :=
  Classical.choose (Finset.exists_subset_card_eq hzero)

theorem OrdinaryGMOClaimBOutput.chosenZeroQuotientOccurrences_subset
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    W.chosenZeroQuotientOccurrences hzero ⊆ W.quotientFiber 0 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq hzero)).1

@[simp]
theorem OrdinaryGMOClaimBOutput.card_chosenZeroQuotientOccurrences
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.chosenZeroQuotientOccurrences hzero).card = dQ :=
  (Classical.choose_spec (Finset.exists_subset_card_eq hzero)).2

/-- The genuine quotient selection `R`: all nonzero positions and exactly
`dQ` genuine zero positions. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Selection W.quotientDisplacementSequence :=
  W.nonzeroQuotientOccurrences ∪ W.chosenZeroQuotientOccurrences hzero

theorem OrdinaryGMOClaimBOutput.nonzeroQuotientOccurrences_subset_quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    W.nonzeroQuotientOccurrences ⊆ W.quotientR hzero :=
  Finset.subset_union_left

theorem OrdinaryGMOClaimBOutput.disjoint_nonzero_chosenZero
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Disjoint W.nonzeroQuotientOccurrences
      (W.chosenZeroQuotientOccurrences hzero) :=
  W.disjoint_nonzeroQuotientOccurrences_zeroFiber.mono_right
    (W.chosenZeroQuotientOccurrences_subset hzero)

@[simp]
theorem OrdinaryGMOClaimBOutput.card_quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.quotientR hzero).card = W.quotientRExceptionCount + dQ := by
  unfold OrdinaryGMOClaimBOutput.quotientR
  rw [Finset.card_union_of_disjoint (W.disjoint_nonzero_chosenZero hzero),
    W.card_chosenZeroQuotientOccurrences]
  rfl

/-- The genuine zero positions in `R` are exactly the chosen zero positions. -/
theorem OrdinaryGMOClaimBOutput.quotientR_inter_zeroFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    W.quotientR hzero ∩ W.quotientFiber 0 =
      W.chosenZeroQuotientOccurrences hzero := by
  classical
  ext q
  constructor
  · intro hq
    have hqR := Finset.mem_inter.mp hq
    rcases Finset.mem_union.mp hqR.1 with hnonzero | hchosen
    · exact False.elim ((Finset.disjoint_left.mp
        W.disjoint_nonzeroQuotientOccurrences_zeroFiber) hnonzero hqR.2)
    · exact hchosen
  · intro hq
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_union_right _ hq,
      W.chosenZeroQuotientOccurrences_subset hzero hq⟩

@[simp]
theorem OrdinaryGMOClaimBOutput.card_quotientR_zeroFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.quotientR hzero ∩ W.quotientFiber 0).card = dQ := by
  rw [W.quotientR_inter_zeroFiber hzero,
    W.card_chosenZeroQuotientOccurrences]

/-- Every quotient position omitted from `R` is a genuine zero position. -/
theorem OrdinaryGMOClaimBOutput.compl_quotientR_subset_zeroFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (Finset.univ : Selection W.quotientDisplacementSequence) \
        W.quotientR hzero ⊆ W.quotientFiber 0 := by
  intro q hq
  have hnotR := (Finset.mem_sdiff.mp hq).2
  by_contra hnotZero
  have hnonzero : q ∈ W.nonzeroQuotientOccurrences := by
    classical
    simp [OrdinaryGMOClaimBOutput.nonzeroQuotientOccurrences, hnotZero]
  exact hnotR (W.nonzeroQuotientOccurrences_subset_quotientR hzero hnonzero)

theorem OrdinaryGMOClaimBOutput.occurrenceValue_eq_zero_of_mem_compl_quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (q : Occurrence W.quotientDisplacementSequence)
    (hq : q ∈ (Finset.univ : Selection W.quotientDisplacementSequence) \
      W.quotientR hzero) :
    occurrenceValue W.quotientDisplacementSequence q = 0 :=
  (W.mem_quotientFiber_iff 0 q).1
    (W.compl_quotientR_subset_zeroFiber hzero hq)

/-- Omitting `R` removes precisely the chosen genuine zero positions from the
zero fiber; in particular, no nonzero occurrence is hidden in the complement. -/
theorem OrdinaryGMOClaimBOutput.compl_quotientR_eq_zeroFiber_sdiff_chosenZero
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (Finset.univ : Selection W.quotientDisplacementSequence) \
        W.quotientR hzero =
      W.quotientFiber 0 \ W.chosenZeroQuotientOccurrences hzero := by
  classical
  ext q
  simp [OrdinaryGMOClaimBOutput.quotientR,
    OrdinaryGMOClaimBOutput.nonzeroQuotientOccurrences]

/-- Exact number of genuine zero positions omitted from `R`. -/
theorem OrdinaryGMOClaimBOutput.card_compl_quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    ((Finset.univ : Selection W.quotientDisplacementSequence) \
      W.quotientR hzero).card = (W.quotientFiber 0).card - dQ := by
  rw [W.compl_quotientR_eq_zeroFiber_sdiff_chosenZero hzero,
    Finset.card_sdiff_of_subset (W.chosenZeroQuotientOccurrences_subset hzero),
    W.card_chosenZeroQuotientOccurrences]

/-- Pullback of `R` to genuine original remaining positions. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientRSource
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) : Selection xs :=
  W.pullbackQuotientSelection (W.quotientR hzero)

@[simp]
theorem OrdinaryGMOClaimBOutput.card_quotientRSource
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.quotientRSource hzero).card = W.quotientRExceptionCount + dQ := by
  rw [OrdinaryGMOClaimBOutput.quotientRSource,
    W.card_pullbackQuotientSelection, W.card_quotientR]

theorem OrdinaryGMOClaimBOutput.quotientRSource_subset_remaining
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    W.quotientRSource hzero ⊆ W.remainingOccurrences :=
  W.pullbackQuotientSelection_subset_remaining (W.quotientR hzero)

theorem OrdinaryGMOClaimBOutput.quotientRSource_disjoint_partition_support
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Disjoint (W.quotientRSource hzero) W.partition.support := by
  rw [Finset.disjoint_left]
  intro i hiR hiSupport
  exact (W.mem_remainingOccurrences_iff i).1
    (W.quotientRSource_subset_remaining hzero hiR) hiSupport

/-- Genuine quotient values selected by `R`, in the deterministic order of
the labelled positions in `R`. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientRValues
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) : List (A ⧸ W.K) :=
  (W.quotientR hzero).toList.map
    (occurrenceValue W.quotientDisplacementSequence)

@[simp]
theorem OrdinaryGMOClaimBOutput.length_quotientRValues
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.quotientRValues hzero).length = W.quotientRExceptionCount + dQ := by
  simp [OrdinaryGMOClaimBOutput.quotientRValues, W.card_quotientR hzero]

/-- The padded quotient list used by the later low-multiplicity argument. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRValues
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) : List (A ⧸ W.K) :=
  W.quotientRValues hzero ++
    List.replicate (Nat.card (A ⧸ W.K) - 1) 0

@[simp]
theorem OrdinaryGMOClaimBOutput.length_paddedQuotientRValues
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).length =
      W.quotientRExceptionCount + dQ +
        (Nat.card (A ⧸ W.K) - 1) := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRValues,
    W.length_quotientRValues hzero]

theorem OrdinaryGMOClaimBOutput.take_paddedQuotientRValues
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).take (W.quotientRValues hzero).length =
      W.quotientRValues hzero := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRValues]

theorem OrdinaryGMOClaimBOutput.drop_paddedQuotientRValues
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).drop (W.quotientRValues hzero).length =
      List.replicate (Nat.card (A ⧸ W.K) - 1) 0 := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRValues]

/-- `some q` records a genuine source-backed quotient position; `none`
records an artificial padding zero and therefore has no source occurrence. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRSourceLedger
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    List (Option (Occurrence W.quotientDisplacementSequence)) :=
  (W.quotientR hzero).toList.map some ++
    List.replicate (Nat.card (A ⧸ W.K) - 1) none

/-- Values carried by the separated genuine/artificial ledger. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRLedgerValue
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Option (Occurrence W.quotientDisplacementSequence) → A ⧸ W.K
  | some q => occurrenceValue W.quotientDisplacementSequence q
  | none => 0

theorem OrdinaryGMOClaimBOutput.map_paddedQuotientRSourceLedger
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSourceLedger hzero).map
        W.paddedQuotientRLedgerValue = W.paddedQuotientRValues hzero := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRSourceLedger,
    OrdinaryGMOClaimBOutput.paddedQuotientRLedgerValue,
    OrdinaryGMOClaimBOutput.paddedQuotientRValues,
    OrdinaryGMOClaimBOutput.quotientRValues, List.map_map]

theorem OrdinaryGMOClaimBOutput.take_paddedQuotientRSourceLedger
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSourceLedger hzero).take
        (W.quotientR hzero).card =
      (W.quotientR hzero).toList.map some := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRSourceLedger]

theorem OrdinaryGMOClaimBOutput.drop_paddedQuotientRSourceLedger
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSourceLedger hzero).drop
        (W.quotientR hzero).card =
      List.replicate (Nat.card (A ⧸ W.K) - 1) none := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRSourceLedger]

@[simp]
theorem OrdinaryGMOClaimBOutput.count_none_paddedQuotientRSourceLedger
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSourceLedger hzero).count none =
      Nat.card (A ⧸ W.K) - 1 := by
  rw [OrdinaryGMOClaimBOutput.paddedQuotientRSourceLedger, List.count_append,
    List.count_replicate]
  have hnone :
      List.count none ((W.quotientR hzero).toList.map some) = 0 := by
    apply List.count_eq_zero_of_not_mem
    simp
  rw [hnone]
  simp

@[simp]
theorem OrdinaryGMOClaimBOutput.some_mem_paddedQuotientRSourceLedger_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (q : Occurrence W.quotientDisplacementSequence) :
    some q ∈ W.paddedQuotientRSourceLedger hzero ↔
      q ∈ W.quotientR hzero := by
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRSourceLedger]

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_quotientR
#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_compl_quotientR
#print axioms GaoLean.OrdinaryGMOClaimBOutput.map_paddedQuotientRSourceLedger
