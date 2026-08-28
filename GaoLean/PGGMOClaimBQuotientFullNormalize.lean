import GaoLean.PGGMOClaimBQuotientSeed

/-!
# Normalizing a full padded quotient spectrum to genuine quotient labels

The padded quotient list consists of the genuine `R`-value prefix followed
by artificial zeros.  A padded exact-cardinality selection may therefore
use labels that have no source occurrence.  This module first separates its
zero and nonzero labels.  Every nonzero label is forced into the genuine
prefix and is transported to its literal `R` occurrence.  All selected zero
labels, whether genuine-prefix or artificial-suffix labels, are injected
into the fixed set of `dQ` genuine chosen zero occurrences.  The two images
are disjoint by value, so cardinality and the exact quotient sum are retained.

No artificial padded occurrence is mapped to an original source occurrence.
Only the resulting normalized genuine quotient selection may subsequently
enter the source ledger.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientFullNormalizeFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- Replace every selected padded zero by a distinct genuine chosen zero
occurrence, while transporting every selected nonzero prefix position to
its literal occurrence in `R`.  The output is entirely contained in the
genuine quotient ledger and preserves both labelled cardinality and sum. -/
theorem OrdinaryGMOClaimBOutput.exists_quotientR_selection_of_padded_selection
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (I : Selection (W.paddedQuotientRValues hzero))
    (hIcard : I.card = dQ) :
    ∃ J : Selection W.quotientDisplacementSequence,
      J ⊆ W.quotientR hzero ∧ J.card = dQ ∧
        (∑ q ∈ J, occurrenceValue W.quotientDisplacementSequence q) =
          ∑ i ∈ I, occurrenceValue (W.paddedQuotientRValues hzero) i := by
  classical
  let Z : Selection (W.paddedQuotientRValues hzero) :=
    I.filter fun i ↦ occurrenceValue (W.paddedQuotientRValues hzero) i = 0
  let N : Selection (W.paddedQuotientRValues hzero) :=
    I.filter fun i ↦ occurrenceValue (W.paddedQuotientRValues hzero) i ≠ 0
  have hNZ : Disjoint N Z := by
    rw [Finset.disjoint_left]
    intro i hiN hiZ
    have hne := (Finset.mem_filter.mp hiN).2
    exact hne (Finset.mem_filter.mp hiZ).2
  have hNUZ : N ∪ Z = I := by
    ext i
    simp only [N, Z, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hi, -⟩ | ⟨hi, -⟩)
      · exact hi
      · exact hi
    · intro hi
      by_cases hz :
          occurrenceValue (W.paddedQuotientRValues hzero) i = 0
      · exact Or.inr ⟨hi, hz⟩
      · exact Or.inl ⟨hi, hz⟩
  let chosen : Selection W.quotientDisplacementSequence :=
    W.chosenZeroQuotientOccurrences hzero
  have hchosenCard : chosen.card = dQ := by
    dsimp [chosen]
    exact W.card_chosenZeroQuotientOccurrences hzero
  have hZCardLe : Z.card ≤ chosen.card := by
    calc
      Z.card ≤ I.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = dQ := hIcard
      _ = chosen.card := hchosenCard.symm
  have hSubtypeCard :
      Fintype.card {i // i ∈ Z} ≤ Fintype.card {q // q ∈ chosen} := by
    simpa using hZCardLe
  obtain ⟨zeroSubEmbedding⟩ :=
    Function.Embedding.nonempty_of_card_le hSubtypeCard
  let zeroToQ : {i // i ∈ Z} ↪
      Occurrence W.quotientDisplacementSequence :=
    zeroSubEmbedding.trans (Function.Embedding.subtype fun q ↦ q ∈ chosen)
  have hzeroToQChosen (i : {i // i ∈ Z}) :
      zeroToQ i ∈ chosen := by
    change (zeroSubEmbedding i).1 ∈ chosen
    exact (zeroSubEmbedding i).2
  have hzeroToQValue (i : {i // i ∈ Z}) :
      occurrenceValue W.quotientDisplacementSequence (zeroToQ i) = 0 := by
    apply (W.mem_quotientFiber_iff 0 (zeroToQ i)).1
    exact W.chosenZeroQuotientOccurrences_subset hzero (hzeroToQChosen i)
  have hNSeed (i : Occurrence (W.paddedQuotientRValues hzero))
      (hi : i ∈ N) : i ∈ W.paddedQuotientRSeed hzero := by
    have hne : occurrenceValue (W.paddedQuotientRValues hzero) i ≠ 0 :=
      (Finset.mem_filter.mp hi).2
    by_contra hnotSeed
    have hiArtificial : i ∈ W.paddedQuotientRArtificialSuffix hzero :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotSeed⟩
    exact hne
      (W.occurrenceValue_eq_zero_of_mem_artificialSuffix hzero i hiArtificial)
  let nonzeroIndex : {i // i ∈ N} →
      Occurrence (W.quotientRValues hzero) := fun i ↦
    ⟨i.1.val, (W.mem_paddedQuotientRSeed_iff hzero i.1).1
      (hNSeed i.1 i.2)⟩
  let nonzeroToQ : {i // i ∈ N} ↪
      Occurrence W.quotientDisplacementSequence :=
    { toFun := fun i ↦
        W.quotientRListSourceEmbedding hzero (nonzeroIndex i)
      inj' := by
        intro i j hij
        have hindex : nonzeroIndex i = nonzeroIndex j :=
          (W.quotientRListSourceEmbedding hzero).injective hij
        apply Subtype.ext
        apply Fin.ext
        exact congrArg
          (fun q : Occurrence (W.quotientRValues hzero) ↦ q.val) hindex }
  have hnonzeroToQR (i : {i // i ∈ N}) :
      nonzeroToQ i ∈ W.quotientR hzero := by
    change W.quotientRListSourceOccurrence hzero (nonzeroIndex i) ∈
      W.quotientR hzero
    exact W.quotientRListSourceOccurrence_mem hzero (nonzeroIndex i)
  have hnonzeroToQValue (i : {i // i ∈ N}) :
      occurrenceValue W.quotientDisplacementSequence (nonzeroToQ i) =
        occurrenceValue (W.paddedQuotientRValues hzero) i.1 := by
    have hemb :
        W.paddedQuotientRSeedEmbedding hzero (nonzeroIndex i) = i.1 := by
      apply Fin.ext
      rfl
    change occurrenceValue W.quotientDisplacementSequence
        (W.quotientRListSourceEmbedding hzero (nonzeroIndex i)) = _
    calc
      occurrenceValue W.quotientDisplacementSequence
          (W.quotientRListSourceEmbedding hzero (nonzeroIndex i)) =
          occurrenceValue (W.quotientRValues hzero) (nonzeroIndex i) :=
        W.occurrenceValue_quotientRListSourceEmbedding hzero (nonzeroIndex i)
      _ = occurrenceValue (W.paddedQuotientRValues hzero)
          (W.paddedQuotientRSeedEmbedding hzero (nonzeroIndex i)) :=
        (W.occurrenceValue_paddedQuotientRSeedEmbedding hzero
          (nonzeroIndex i)).symm
      _ = occurrenceValue (W.paddedQuotientRValues hzero) i.1 := by
        rw [hemb]
  let JN : Selection W.quotientDisplacementSequence :=
    N.attach.map nonzeroToQ
  let JZ : Selection W.quotientDisplacementSequence :=
    Z.attach.map zeroToQ
  have hJNJZ : Disjoint JN JZ := by
    rw [Finset.disjoint_left]
    intro q hqN hqZ
    obtain ⟨i, -, hiq⟩ := Finset.mem_map.mp hqN
    obtain ⟨z, -, hzq⟩ := Finset.mem_map.mp hqZ
    have hiNonzero :
        occurrenceValue (W.paddedQuotientRValues hzero) i.1 ≠ 0 :=
      (Finset.mem_filter.mp i.2).2
    apply hiNonzero
    calc
      occurrenceValue (W.paddedQuotientRValues hzero) i.1 =
          occurrenceValue W.quotientDisplacementSequence (nonzeroToQ i) :=
        (hnonzeroToQValue i).symm
      _ = occurrenceValue W.quotientDisplacementSequence q :=
        congrArg (occurrenceValue W.quotientDisplacementSequence) hiq
      _ = occurrenceValue W.quotientDisplacementSequence (zeroToQ z) :=
        congrArg (occurrenceValue W.quotientDisplacementSequence) hzq.symm
      _ = 0 := hzeroToQValue z
  let J : Selection W.quotientDisplacementSequence := JN ∪ JZ
  have hJSubset : J ⊆ W.quotientR hzero := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqN | hqZ
    · obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hqN
      exact hnonzeroToQR i
    · obtain ⟨z, -, rfl⟩ := Finset.mem_map.mp hqZ
      exact Finset.mem_union_right _ (hzeroToQChosen z)
  have hJNCard : JN.card = N.card := by
    simp [JN]
  have hJZCard : JZ.card = Z.card := by
    simp [JZ]
  have hInputCard : N.card + Z.card = I.card := by
    rw [← Finset.card_union_of_disjoint hNZ, hNUZ]
  have hJCard : J.card = dQ := by
    dsimp [J]
    rw [Finset.card_union_of_disjoint hJNJZ, hJNCard, hJZCard,
      hInputCard, hIcard]
  have hJNsum :
      (∑ q ∈ JN, occurrenceValue W.quotientDisplacementSequence q) =
        ∑ i ∈ N, occurrenceValue (W.paddedQuotientRValues hzero) i := by
    symm
    refine Finset.sum_bij
      (fun i hi ↦ nonzeroToQ ⟨i, hi⟩) ?_ ?_ ?_ ?_
    · intro i hi
      apply Finset.mem_map.mpr
      exact ⟨⟨i, hi⟩, by simp, rfl⟩
    · intro i hi j hj hij
      have hs := nonzeroToQ.injective hij
      exact congrArg Subtype.val hs
    · intro q hq
      obtain ⟨i, -, hiq⟩ := Finset.mem_map.mp hq
      exact ⟨i.1, i.2, hiq⟩
    · intro i hi
      exact (hnonzeroToQValue ⟨i, hi⟩).symm
  have hJZsum :
      (∑ q ∈ JZ, occurrenceValue W.quotientDisplacementSequence q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨z, -, hzq⟩ := Finset.mem_map.mp hq
    rw [← hzq]
    exact hzeroToQValue z
  have hZsum :
      (∑ i ∈ Z, occurrenceValue (W.paddedQuotientRValues hzero) i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hInputSum :
      (∑ i ∈ I, occurrenceValue (W.paddedQuotientRValues hzero) i) =
        (∑ i ∈ N, occurrenceValue (W.paddedQuotientRValues hzero) i) +
          ∑ i ∈ Z, occurrenceValue (W.paddedQuotientRValues hzero) i := by
    calc
      (∑ i ∈ I, occurrenceValue (W.paddedQuotientRValues hzero) i) =
          ∑ i ∈ N ∪ Z,
            occurrenceValue (W.paddedQuotientRValues hzero) i := by
        rw [hNUZ]
      _ = _ := Finset.sum_union hNZ
  refine ⟨J, hJSubset, hJCard, ?_⟩
  dsimp [J]
  calc
    (∑ q ∈ JN ∪ JZ,
        occurrenceValue W.quotientDisplacementSequence q) =
        (∑ q ∈ JN, occurrenceValue W.quotientDisplacementSequence q) +
          ∑ q ∈ JZ, occurrenceValue W.quotientDisplacementSequence q :=
      Finset.sum_union hJNJZ
    _ = (∑ i ∈ N, occurrenceValue (W.paddedQuotientRValues hzero) i) + 0 := by
      rw [hJNsum, hJZsum]
    _ = (∑ i ∈ N, occurrenceValue (W.paddedQuotientRValues hzero) i) +
          ∑ i ∈ Z, occurrenceValue (W.paddedQuotientRValues hzero) i := by
      rw [hZsum]
    _ = ∑ i ∈ I, occurrenceValue (W.paddedQuotientRValues hzero) i :=
      hInputSum.symm

/-- Full exact spectrum on the padded quotient list normalizes to a genuine
exact-cardinality selection in `R` for every quotient target.  Positivity is
retained explicitly because the recursive Claim-B invocation supplies it;
the normalization itself only consumes the exact `dQ` zero reservoir. -/
theorem OrdinaryGMOClaimBOutput.exists_quotientR_selection_of_padded_spectrumFull
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (_hdQpos : 1 ≤ dQ)
    (hfull : OrdinarySpectrumFull (W.paddedQuotientRValues hzero) dQ)
    (y : A ⧸ W.K) :
    ∃ J : Selection W.quotientDisplacementSequence,
      J ⊆ W.quotientR hzero ∧ J.card = dQ ∧
        (∑ q ∈ J, occurrenceValue W.quotientDisplacementSequence q) = y := by
  obtain ⟨I, hIcard, hIsum⟩ := hfull y
  obtain ⟨J, hJSub, hJcard, hJsum⟩ :=
    W.exists_quotientR_selection_of_padded_selection hzero I hIcard
  exact ⟨J, hJSub, hJcard, hJsum.trans hIsum⟩

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.exists_quotientR_selection_of_padded_selection
#print axioms GaoLean.OrdinaryGMOClaimBOutput.exists_quotientR_selection_of_padded_spectrumFull
