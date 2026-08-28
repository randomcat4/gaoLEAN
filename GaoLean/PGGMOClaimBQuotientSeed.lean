import GaoLean.PGGMOClaimBQuotientR

/-!
# The source-faithful seed for the low quotient-multiplicity branch

The padded quotient list has a genuine prefix indexed by `R` and an
artificial zero suffix.  The seed below is literally the prefix carrier, so
no artificial position can enter it.  Multiplicity is proved by transporting
position counts back to the genuine quotient sequence.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The selected positions are exactly the genuine `R`-value prefix of the
padded quotient list. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRSeed
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Selection (W.paddedQuotientRValues hzero) := by
  classical
  exact Finset.univ.filter fun i ↦
    i.val < (W.quotientRValues hzero).length

/-- The complementary padded positions.  These positions are artificial;
they do not represent quotient or original-source occurrences. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRArtificialSuffix
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Selection (W.paddedQuotientRValues hzero) := by
  classical
  exact Finset.univ \ W.paddedQuotientRSeed hzero

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_paddedQuotientRSeed_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.paddedQuotientRValues hzero)) :
    i ∈ W.paddedQuotientRSeed hzero ↔
      i.val < (W.quotientRValues hzero).length := by
  classical
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRSeed]

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_paddedQuotientRArtificialSuffix_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.paddedQuotientRValues hzero)) :
    i ∈ W.paddedQuotientRArtificialSuffix hzero ↔
      (W.quotientRValues hzero).length ≤ i.val := by
  classical
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRArtificialSuffix, not_lt]

theorem OrdinaryGMOClaimBOutput.disjoint_paddedQuotientRSeed_artificialSuffix
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Disjoint (W.paddedQuotientRSeed hzero)
      (W.paddedQuotientRArtificialSuffix hzero) := by
  classical
  exact Finset.disjoint_sdiff

theorem OrdinaryGMOClaimBOutput.not_mem_paddedQuotientRSeed_of_mem_artificial
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.paddedQuotientRValues hzero))
    (hi : i ∈ W.paddedQuotientRArtificialSuffix hzero) :
    i ∉ W.paddedQuotientRSeed hzero :=
  (Finset.mem_sdiff.mp hi).2

/-- Every complementary padded position carries an artificial zero. -/
theorem OrdinaryGMOClaimBOutput.occurrenceValue_eq_zero_of_mem_artificialSuffix
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.paddedQuotientRValues hzero))
    (hi : i ∈ W.paddedQuotientRArtificialSuffix hzero) :
    occurrenceValue (W.paddedQuotientRValues hzero) i = 0 := by
  have hge : (W.quotientRValues hzero).length ≤ i.val :=
    (W.mem_paddedQuotientRArtificialSuffix_iff hzero i).1 hi
  simp only [OrdinaryGMOClaimBOutput.paddedQuotientRValues,
    occurrenceValue, List.get_eq_getElem]
  rw [List.getElem_append_right hge]
  simp

@[simp]
theorem OrdinaryGMOClaimBOutput.card_paddedQuotientRSeed_eq_quotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSeed hzero).card = (W.quotientR hzero).card := by
  classical
  calc
    (W.paddedQuotientRSeed hzero).card =
        (Finset.univ : Selection (W.quotientRValues hzero)).card := by
      apply Finset.card_bij
        (fun i hi ↦ ⟨i.val,
          (W.mem_paddedQuotientRSeed_iff hzero i).1 hi⟩)
      · intro i hi
        exact Finset.mem_univ _
      · intro i hi j hj hij
        have hval := congrArg
          (fun k : Occurrence (W.quotientRValues hzero) ↦ k.val) hij
        exact Fin.ext hval
      · intro j hj
        have hlen :
            (W.quotientRValues hzero).length ≤
              (W.paddedQuotientRValues hzero).length := by
          simp [OrdinaryGMOClaimBOutput.paddedQuotientRValues]
        let i : Occurrence (W.paddedQuotientRValues hzero) :=
          ⟨j.val, lt_of_lt_of_le j.isLt hlen⟩
        have hi : i ∈ W.paddedQuotientRSeed hzero :=
          (W.mem_paddedQuotientRSeed_iff hzero i).2 (by
            change j.val < (W.quotientRValues hzero).length
            exact j.isLt)
        refine ⟨i, hi, ?_⟩
        apply Fin.ext
        rfl
    _ = (W.quotientRValues hzero).length := by simp
    _ = (W.quotientR hzero).card := by
      simp [OrdinaryGMOClaimBOutput.quotientRValues]

@[simp]
theorem OrdinaryGMOClaimBOutput.card_paddedQuotientRSeed
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSeed hzero).card =
      W.quotientRExceptionCount + dQ := by
  rw [W.card_paddedQuotientRSeed_eq_quotientR hzero,
    W.card_quotientR hzero]

theorem OrdinaryGMOClaimBOutput.dQ_le_card_paddedQuotientRSeed
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    dQ ≤ (W.paddedQuotientRSeed hzero).card := by
  rw [W.card_paddedQuotientRSeed hzero]
  omega

@[simp]
theorem OrdinaryGMOClaimBOutput.card_paddedQuotientRArtificialSuffix
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRArtificialSuffix hzero).card =
      Nat.card (A ⧸ W.K) - 1 := by
  classical
  rw [OrdinaryGMOClaimBOutput.paddedQuotientRArtificialSuffix,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    W.card_paddedQuotientRSeed_eq_quotientR hzero]
  simp [OrdinaryGMOClaimBOutput.paddedQuotientRValues,
    OrdinaryGMOClaimBOutput.quotientRValues]

/-! ## Exact position embeddings for the genuine prefix -/

/-- The canonical embedding of a genuine prefix position into the padded
list. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRSeedEmbedding
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Occurrence (W.quotientRValues hzero) ↪
      Occurrence (W.paddedQuotientRValues hzero) := by
  simpa [OrdinaryGMOClaimBOutput.paddedQuotientRValues] using
    appendLeftOccurrenceEmbedding (W.quotientRValues hzero)
      (List.replicate (Nat.card (A ⧸ W.K) - 1) 0)

theorem OrdinaryGMOClaimBOutput.map_univ_paddedQuotientRSeedEmbedding
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (Finset.univ : Selection (W.quotientRValues hzero)).map
        (W.paddedQuotientRSeedEmbedding hzero) =
      W.paddedQuotientRSeed hzero := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    exact (W.mem_paddedQuotientRSeed_iff hzero _).2 j.isLt
  · intro hi
    have hlt := (W.mem_paddedQuotientRSeed_iff hzero i).1 hi
    let j : Occurrence (W.quotientRValues hzero) := ⟨i.val, hlt⟩
    apply Finset.mem_map.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl

@[simp]
theorem OrdinaryGMOClaimBOutput.occurrenceValue_paddedQuotientRSeedEmbedding
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    occurrenceValue (W.paddedQuotientRValues hzero)
        (W.paddedQuotientRSeedEmbedding hzero i) =
      occurrenceValue (W.quotientRValues hzero) i := by
  change occurrenceValue
      (W.quotientRValues hzero ++
        List.replicate (Nat.card (A ⧸ W.K) - 1) 0)
      (appendLeftOccurrenceEmbedding (W.quotientRValues hzero)
        (List.replicate (Nat.card (A ⧸ W.K) - 1) 0) i) = _
  exact occurrenceValue_appendLeftOccurrenceEmbedding
    (W.quotientRValues hzero)
    (List.replicate (Nat.card (A ⧸ W.K) - 1) 0) i

/-- Recover the genuine quotient-sequence occurrence at the same ordered
`R.toList` position. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientRListSourceOccurrence
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    Occurrence W.quotientDisplacementSequence :=
  (W.quotientR hzero).toList.get
    ⟨i.val, by
      simpa [OrdinaryGMOClaimBOutput.quotientRValues] using i.isLt⟩

theorem OrdinaryGMOClaimBOutput.quotientRListSourceOccurrence_mem
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    W.quotientRListSourceOccurrence hzero i ∈ W.quotientR hzero := by
  change (W.quotientR hzero).toList.get _ ∈ W.quotientR hzero
  exact Finset.mem_toList.mp (List.get_mem _ _)

theorem OrdinaryGMOClaimBOutput.quotientRListSourceOccurrence_injective
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Function.Injective (W.quotientRListSourceOccurrence hzero) := by
  intro i j hij
  have hindex :
      (⟨i.val, by simpa [OrdinaryGMOClaimBOutput.quotientRValues]
          using i.isLt⟩ : Fin (W.quotientR hzero).toList.length) =
        ⟨j.val, by simpa [OrdinaryGMOClaimBOutput.quotientRValues]
          using j.isLt⟩ :=
    (W.quotientR hzero).nodup_toList.injective_get hij
  have hval := congrArg
    (fun k : Fin (W.quotientR hzero).toList.length ↦ k.val) hindex
  exact Fin.ext hval

/-- Ordered `R` positions embed in their exact genuine quotient positions. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientRListSourceEmbedding
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Occurrence (W.quotientRValues hzero) ↪
      Occurrence W.quotientDisplacementSequence where
  toFun := W.quotientRListSourceOccurrence hzero
  inj' := W.quotientRListSourceOccurrence_injective hzero

@[simp]
theorem OrdinaryGMOClaimBOutput.occurrenceValue_quotientRListSourceEmbedding
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    occurrenceValue W.quotientDisplacementSequence
        (W.quotientRListSourceEmbedding hzero i) =
      occurrenceValue (W.quotientRValues hzero) i := by
  change occurrenceValue W.quotientDisplacementSequence
      (W.quotientRListSourceOccurrence hzero i) = _
  simp [OrdinaryGMOClaimBOutput.quotientRListSourceOccurrence,
    OrdinaryGMOClaimBOutput.quotientRValues, occurrenceValue]

/-- The same prefix position embeds all the way back to its literal original
source occurrence. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRSeedOriginalEmbedding
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Occurrence (W.quotientRValues hzero) ↪ Occurrence xs where
  toFun := fun i ↦ W.quotientSourceOccurrence
    (W.quotientRListSourceEmbedding hzero i)
  inj' := W.quotientSourceOccurrence_injective.comp
    (W.quotientRListSourceEmbedding hzero).injective

theorem OrdinaryGMOClaimBOutput.paddedQuotientRSeedOriginalEmbedding_mem_remaining
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    W.paddedQuotientRSeedOriginalEmbedding hzero i ∈
      W.remainingOccurrences :=
  W.quotientSourceOccurrence_mem_remaining
    (W.quotientRListSourceEmbedding hzero i)

theorem OrdinaryGMOClaimBOutput.paddedQuotientRSeedOriginalEmbedding_not_mem_support
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    W.paddedQuotientRSeedOriginalEmbedding hzero i ∉
      W.partition.support :=
  (W.mem_remainingOccurrences_iff _).1
    (W.paddedQuotientRSeedOriginalEmbedding_mem_remaining hzero i)

theorem OrdinaryGMOClaimBOutput.occurrenceValue_paddedSeed_eq_sourceDisplacement
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (i : Occurrence (W.quotientRValues hzero)) :
    occurrenceValue (W.paddedQuotientRValues hzero)
        (W.paddedQuotientRSeedEmbedding hzero i) =
      W.quotientDisplacement
        (W.paddedQuotientRSeedOriginalEmbedding hzero i) := by
  rw [W.occurrenceValue_paddedQuotientRSeedEmbedding hzero i,
    ← W.occurrenceValue_quotientRListSourceEmbedding hzero i,
    W.occurrenceValue_quotientDisplacementSequence]
  rfl

/-! ## Position-count multiplicity transport -/

/-- The genuine seed positions carrying quotient value `z`. -/
noncomputable def OrdinaryGMOClaimBOutput.paddedQuotientRSeedFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) (z : A ⧸ W.K) :
    Selection (W.paddedQuotientRValues hzero) := by
  classical
  exact (W.paddedQuotientRSeed hzero).filter fun i ↦
    occurrenceValue (W.paddedQuotientRValues hzero) i = z

/-- The restriction of the original quotient fiber to the genuine set `R`. -/
noncomputable def OrdinaryGMOClaimBOutput.quotientRRestrictedFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) (z : A ⧸ W.K) :
    Selection W.quotientDisplacementSequence := by
  classical
  exact (W.quotientR hzero).filter fun q ↦
    occurrenceValue W.quotientDisplacementSequence q = z

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_paddedQuotientRSeedFiber_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) (z : A ⧸ W.K)
    (i : Occurrence (W.paddedQuotientRValues hzero)) :
    i ∈ W.paddedQuotientRSeedFiber hzero z ↔
      i ∈ W.paddedQuotientRSeed hzero ∧
        occurrenceValue (W.paddedQuotientRValues hzero) i = z := by
  classical
  rw [OrdinaryGMOClaimBOutput.paddedQuotientRSeedFiber]
  exact Finset.mem_filter

@[simp]
theorem OrdinaryGMOClaimBOutput.mem_quotientRRestrictedFiber_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) (z : A ⧸ W.K)
    (q : Occurrence W.quotientDisplacementSequence) :
    q ∈ W.quotientRRestrictedFiber hzero z ↔
      q ∈ W.quotientR hzero ∧
        occurrenceValue W.quotientDisplacementSequence q = z := by
  classical
  rw [OrdinaryGMOClaimBOutput.quotientRRestrictedFiber]
  exact Finset.mem_filter

/-- Any selection whose members are exactly the genuine seed positions of
value `z` is position-bijective with the restriction of the original
quotient fiber to `R`.  The proof uses labelled occurrences throughout. -/
theorem OrdinaryGMOClaimBOutput.card_selection_eq_quotientRRestrictedFiber_of_mem_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) (z : A ⧸ W.K)
    (S : Selection (W.paddedQuotientRValues hzero))
    (hmem : ∀ i, i ∈ S ↔
      i ∈ W.paddedQuotientRSeed hzero ∧
        occurrenceValue (W.paddedQuotientRValues hzero) i = z) :
    S.card = (W.quotientRRestrictedFiber hzero z).card := by
  classical
  let index : ∀ i, i ∈ S → Occurrence (W.quotientRValues hzero) :=
    fun i hi ↦ ⟨i.val,
      (W.mem_paddedQuotientRSeed_iff hzero i).1 ((hmem i).1 hi).1⟩
  let toQ : ∀ i, i ∈ S → Occurrence W.quotientDisplacementSequence :=
    fun i hi ↦ W.quotientRListSourceEmbedding hzero (index i hi)
  refine Finset.card_bij toQ ?_ ?_ ?_
  · intro i hi
    apply (W.mem_quotientRRestrictedFiber_iff hzero z _).2
    refine ⟨W.quotientRListSourceOccurrence_mem hzero (index i hi), ?_⟩
    have hi' := (hmem i).1 hi
    have hemb : W.paddedQuotientRSeedEmbedding hzero (index i hi) = i := by
      apply Fin.ext
      rfl
    calc
      occurrenceValue W.quotientDisplacementSequence (toQ i hi) =
          occurrenceValue (W.quotientRValues hzero) (index i hi) :=
        W.occurrenceValue_quotientRListSourceEmbedding hzero (index i hi)
      _ = occurrenceValue (W.paddedQuotientRValues hzero)
          (W.paddedQuotientRSeedEmbedding hzero (index i hi)) :=
        (W.occurrenceValue_paddedQuotientRSeedEmbedding hzero
          (index i hi)).symm
      _ = occurrenceValue (W.paddedQuotientRValues hzero) i := by rw [hemb]
      _ = z := hi'.2
  · intro i hi j hj hij
    have hindex : index i hi = index j hj :=
      (W.quotientRListSourceEmbedding hzero).injective hij
    have hval := congrArg
      (fun k : Occurrence (W.quotientRValues hzero) ↦ k.val) hindex
    exact Fin.ext hval
  · intro q hq
    have hq' := (W.mem_quotientRRestrictedFiber_iff hzero z q).1 hq
    have hqList : q ∈ (W.quotientR hzero).toList :=
      Finset.mem_toList.mpr hq'.1
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hqList
    let j' : Occurrence (W.quotientRValues hzero) :=
      ⟨j.val, by
        simpa [OrdinaryGMOClaimBOutput.quotientRValues] using j.isLt⟩
    let i : Occurrence (W.paddedQuotientRValues hzero) :=
      W.paddedQuotientRSeedEmbedding hzero j'
    have hiSeed : i ∈ W.paddedQuotientRSeed hzero := by
      apply (W.mem_paddedQuotientRSeed_iff hzero i).2
      have hval : i.val = j'.val := by
        rfl
      rw [hval]
      exact j'.isLt
    have hsource : W.quotientRListSourceEmbedding hzero j' = q := by
      change (W.quotientR hzero).toList.get _ = q
      have hindex :
          (⟨j'.val, by
            simpa [OrdinaryGMOClaimBOutput.quotientRValues]
              using j'.isLt⟩ : Fin (W.quotientR hzero).toList.length) = j := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact hj
    have hiValue : occurrenceValue (W.paddedQuotientRValues hzero) i = z := by
      calc
        occurrenceValue (W.paddedQuotientRValues hzero) i =
            occurrenceValue (W.quotientRValues hzero) j' :=
          W.occurrenceValue_paddedQuotientRSeedEmbedding hzero j'
        _ = occurrenceValue W.quotientDisplacementSequence
            (W.quotientRListSourceEmbedding hzero j') :=
          (W.occurrenceValue_quotientRListSourceEmbedding hzero j').symm
        _ = z := by rw [hsource]; exact hq'.2
    have hiS : i ∈ S := (hmem i).2 ⟨hiSeed, hiValue⟩
    refine ⟨i, hiS, ?_⟩
    dsimp [toQ, index]
    exact hsource

theorem OrdinaryGMOClaimBOutput.card_paddedQuotientRSeedFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (z : A ⧸ W.K) :
    (W.paddedQuotientRSeedFiber hzero z).card =
      (W.quotientRRestrictedFiber hzero z).card := by
  apply W.card_selection_eq_quotientRRestrictedFiber_of_mem_iff hzero z
  intro i
  exact W.mem_paddedQuotientRSeedFiber_iff hzero z i

@[simp]
theorem OrdinaryGMOClaimBOutput.card_paddedQuotientRSeed_zeroFiber
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRSeedFiber hzero 0).card = dQ := by
  rw [W.card_paddedQuotientRSeedFiber hzero 0]
  have heq :
      W.quotientRRestrictedFiber hzero 0 =
        W.quotientR hzero ∩ W.quotientFiber 0 := by
    classical
    ext q
    simp [OrdinaryGMOClaimBOutput.quotientRRestrictedFiber]
  rw [heq, W.card_quotientR_zeroFiber hzero]

/-- Low multiplicity on genuine quotient fibers gives the exact multiplicity
bound required for the padded seed.  Artificial zeros do not contribute. -/
theorem OrdinaryGMOClaimBOutput.paddedQuotientRSeed_multiplicityAtMost
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hlow : ∀ z : A ⧸ W.K, z ≠ 0 → (W.quotientFiber z).card ≤ dQ) :
    SelectionMultiplicityAtMost (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ := by
  classical
  intro z
  calc
    _ = (W.quotientRRestrictedFiber hzero z).card := by
      apply W.card_selection_eq_quotientRRestrictedFiber_of_mem_iff hzero z
      intro i
      constructor
      · intro hi
        simpa only [Finset.mem_filter] using hi
      · intro hi
        simpa only [Finset.mem_filter] using hi
    _ ≤ dQ := by
      by_cases hz : z = 0
      · subst z
        rw [← W.card_paddedQuotientRSeedFiber hzero 0,
          W.card_paddedQuotientRSeed_zeroFiber hzero]
      · calc
        (W.quotientRRestrictedFiber hzero z).card ≤
          (W.quotientFiber z).card := by
            apply Finset.card_le_card
            intro q hq
            exact (W.mem_quotientFiber_iff z q).2
              ((W.mem_quotientRRestrictedFiber_iff hzero z q).1 hq).2
        _ ≤ dQ := hlow z hz

/-- The honest selected setpartition input on the smaller quotient group.
This constructs only the input data; it makes no claim about the later
Theorem 2.1 output. -/
theorem OrdinaryGMOClaimBOutput.nonempty_gmoTheoremEInput_paddedQuotientR
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hlow : ∀ z : A ⧸ W.K, z ≠ 0 → (W.quotientFiber z).card ≤ dQ) :
    Nonempty (GMOTheoremEInput (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ) :=
  exists_gmoTheoremEInput _ _ _
    (W.paddedQuotientRSeed_multiplicityAtMost hzero hlow)
    (W.dQ_le_card_paddedQuotientRSeed hzero)

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_paddedQuotientRSeed_zeroFiber
#print axioms GaoLean.OrdinaryGMOClaimBOutput.paddedQuotientRSeed_multiplicityAtMost
#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_gmoTheoremEInput_paddedQuotientR
