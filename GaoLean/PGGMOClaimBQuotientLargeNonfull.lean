import GaoLean.PGGMOClaimBQuotientSeed

/-!
# The non-full large branch on the padded Claim-B quotient

The large alternative on the padded quotient is used here only for its
cardinality inequality.  Artificial padding positions never enter the
source ledger.  The genuine nonzero quotient positions are identified
exactly with original occurrences outside `g + K`.

The explicit hypothesis `1 ≤ dQ` is necessary at this level of generality.
If `dQ` were allowed to be zero, a zero-cell padded partition could satisfy
the large/non-full cardinality hypotheses without providing the two genuine
source occurrences required when the quotient is wider than the source.
In the final recursive application, positivity comes from the canonical
`dQ = pGroupDStar (A ⧸ K)` on a nontrivial odd-primary quotient.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientLargeNonfullFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- A nontrivial finite subgroup has positive canonical `d*`.  This is the
single genuine support label needed in the short-source branch below. -/
theorem one_le_pGroupDStar_of_addSubgroup_ne_bot
    (K : AddSubgroup A) (hK : K ≠ ⊥) :
    1 ≤ pGroupDStar K := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Nontrivial K := (AddSubgroup.nontrivial_iff_ne_bot K).2 hK
  by_contra hnot
  have hdstarZero : pGroupDStar K = 0 := by omega
  have hDOne : ordinaryDavenportValue K = 1 := by
    have hadd := pGroupDStar_add_one K
    omega
  obtain ⟨a, ha⟩ : ∃ a : K, a ≠ 0 := exists_ne 0
  have hzero : HasNonemptyZeroSum ([a] : List K) :=
    (ordinaryDavenportValue_spec K).1 [a] (by simp [hDOne])
  obtain ⟨I, hIne, hIsum⟩ := hzero
  obtain ⟨i, hi⟩ := hIne
  have hIeq : I = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hi, ?_⟩
    intro j _
    simpa using (Fin.eq_zero j).trans (Fin.eq_zero i).symm
  have hiZero : i = (⟨0, by simp⟩ : Occurrence ([a] : List K)) := by
    simpa using Fin.eq_zero i
  subst i
  rw [hIeq] at hIsum
  have haZero : a = 0 := by
    simpa [occurrenceValue] using hIsum
  exact ha haZero

/-- The labelled nonzero quotient positions are exactly the original source
occurrences outside the canonical Claim-B coset.  The reverse implication
uses `support_in_coset`, so no support occurrence is lost when passing to the
remaining-occurrence quotient ledger. -/
theorem OrdinaryGMOClaimBOutput.map_nonzeroQuotientOccurrences
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    W.nonzeroQuotientOccurrences.map W.quotientSourceEmbedding =
      (Finset.univ : Selection xs) \
        occurrencesInAddCoset xs W.K W.g := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcoset
    have hnotAdd :
        occurrenceValue xs (W.quotientSourceOccurrence q) ∉
          addCosetFinset W.K W.g :=
      (W.occurrenceValue_quotient_ne_zero_iff q).1
        ((W.mem_nonzeroQuotientOccurrences_iff q).1 hq)
    apply hnotAdd
    apply (mem_addCosetFinset_iff W.K W.g _).2
    simpa [OrdinaryGMOClaimBOutput.quotientSourceEmbedding] using
      (mem_occurrencesInAddCoset_iff xs W.K W.g _).1 hcoset
  · intro hi
    have hiSdiff := Finset.mem_sdiff.mp hi
    have hiNotAdd : occurrenceValue xs i ∉ addCosetFinset W.K W.g := by
      intro hiAdd
      apply hiSdiff.2
      exact (mem_occurrencesInAddCoset_iff xs W.K W.g i).2
        ((mem_addCosetFinset_iff W.K W.g _).1 hiAdd)
    have hiRemaining : i ∈ W.remainingOccurrences := by
      apply (W.mem_remainingOccurrences_iff i).2
      intro hiSupport
      exact hiNotAdd (W.support_in_coset i hiSupport)
    have hiRange : i ∈
        (Finset.univ : Selection W.quotientDisplacementSequence).map
          W.quotientSourceEmbedding := by
      rw [W.map_univ_quotientSourceEmbedding]
      exact hiRemaining
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hiRange
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, hqi⟩
    apply (W.mem_nonzeroQuotientOccurrences_iff q).2
    apply (W.occurrenceValue_quotient_ne_zero_iff q).2
    change occurrenceValue xs (W.quotientSourceEmbedding q) ∉
      addCosetFinset W.K W.g
    rw [hqi]
    exact hiNotAdd

/-- Exact source interpretation of the paper's exception count `e`. -/
theorem OrdinaryGMOClaimBOutput.card_sourceOutsideCoset_eq_quotientRExceptionCount
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    ((Finset.univ : Selection xs) \
      occurrencesInAddCoset xs W.K W.g).card =
        W.quotientRExceptionCount := by
  have hcard := congrArg Finset.card W.map_nonzeroQuotientOccurrences
  simpa [OrdinaryGMOClaimBOutput.quotientRExceptionCount] using hcard.symm

/-- A proper padded quotient large branch yields the canonical source
concentration at `K` and `g`.  The proof uses no source interpretation of
artificial padding positions. -/
theorem OrdinaryGMOClaimBOutput.nonempty_concentration_of_quotientLarge_nonfull
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card)
    (hdQpos : 1 ≤ dQ)
    (Qpartition : Theorem21SetPartition
      (W.paddedQuotientRValues hzero) dQ
      (W.paddedQuotientRSeed hzero).card)
    (Qlarge : GMOTheorem21LargeAlternative
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ Qpartition)
    (hnotfull : Qpartition.sumset ≠ Finset.univ) :
    Nonempty (OrdinaryGMOConcentration xs) := by
  classical
  let qcard : ℕ := Nat.card (A ⧸ W.K)
  let e : ℕ := W.quotientRExceptionCount
  have hwidth :
      (W.paddedQuotientRSeed hzero).card - dQ + 1 = e + 1 := by
    rw [W.card_paddedQuotientRSeed hzero]
    dsimp [e]
    omega
  have hlarge := Qlarge.card_lower
  rw [hwidth] at hlarge
  have hsumsetLt : Qpartition.sumset.card < qcard := by
    dsimp [qcard]
    simpa using
      (Finset.card_lt_iff_ne_univ Qpartition.sumset).2 hnotfull
  have hminLt : min qcard (e + 1) < qcard :=
    lt_of_le_of_lt hlarge hsumsetLt
  have heLt : e + 1 < qcard := by
    by_contra hnot
    have hqle : qcard ≤ e + 1 := Nat.le_of_not_gt hnot
    rw [min_eq_left hqle] at hminLt
    exact (Nat.lt_irrefl qcard) hminLt
  have heTwo : e + 2 ≤ qcard := by omega
  have hKneTop : W.K ≠ ⊤ := by
    intro htop
    have hqone : qcard = 1 := by
      dsimp [qcard]
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientAddGroup.subsingleton_quotient_top, ⟨0⟩⟩
    omega
  have hKstrict : W.K < ⊤ := lt_top_iff_ne_top.mpr hKneTop
  let C : Selection xs := occurrencesInAddCoset xs W.K W.g
  have hCLe : C.card ≤ xs.length := by
    dsimp [C]
    simpa using Finset.card_le_univ
      (occurrencesInAddCoset xs W.K W.g)
  have houtside :
      ((Finset.univ : Selection xs) \ C).card = e := by
    dsimp [C, e]
    exact W.card_sourceOutsideCoset_eq_quotientRExceptionCount
  have htotal : e + C.card = xs.length := by
    calc
      e + C.card =
          ((Finset.univ : Selection xs) \ C).card + C.card := by
            rw [houtside]
      _ = (xs.length - C.card) + C.card := by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ C)]
            simp
      _ = xs.length := Nat.sub_add_cancel hCLe
  have hdstarPos : 0 < pGroupDStar W.K :=
    one_le_pGroupDStar_of_addSubgroup_ne_bot W.K W.nontrivial
  let c : Fin (pGroupDStar W.K) := ⟨0, hdstarPos⟩
  obtain ⟨isupport, hisupportCell⟩ := W.partition.cells_nonempty c
  have hisupport : isupport ∈ W.partition.support := by
    apply Finset.mem_biUnion.mpr
    exact ⟨c, Finset.mem_univ _, hisupportCell⟩
  have hisupportC : isupport ∈ C := by
    apply (mem_occurrencesInAddCoset_iff xs W.K W.g isupport).2
    exact (mem_addCosetFinset_iff W.K W.g _).1
      (W.support_in_coset isupport hisupport)
  have hzeroFiberPos : 0 < (W.quotientFiber 0).card := by omega
  obtain ⟨qzero, hqzero⟩ := Finset.card_pos.mp hzeroFiberPos
  let izero : Occurrence xs := W.quotientSourceOccurrence qzero
  have hizeroRemaining : izero ∈ W.remainingOccurrences :=
    W.quotientSourceOccurrence_mem_remaining qzero
  have hizeroC : izero ∈ C := by
    apply (mem_occurrencesInAddCoset_iff xs W.K W.g izero).2
    apply (mem_addCosetFinset_iff W.K W.g _).1
    exact (W.occurrenceValue_quotient_eq_zero_iff qzero).1
      ((W.mem_quotientFiber_iff 0 qzero).1 hqzero)
  have hsupportNeZero : isupport ≠ izero := by
    intro heq
    have hizeroNotSupport : izero ∉ W.partition.support :=
      (W.mem_remainingOccurrences_iff izero).1 hizeroRemaining
    exact hizeroNotSupport (heq ▸ hisupport)
  have hCtwo : 2 ≤ C.card := by
    have hpair : ({isupport, izero} : Selection xs) ⊆ C := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hisupportC
      · exact hizeroC
    have hcard := Finset.card_le_card hpair
    simpa [hsupportNeZero] using hcard
  have hcosetCard :
      xs.length - Nat.card (A ⧸ W.K) + 2 ≤ C.card := by
    by_cases hwide : qcard ≤ xs.length
    · dsimp [qcard] at heTwo ⊢
      omega
    · have hshort : xs.length ≤ qcard := Nat.le_of_lt (Nat.lt_of_not_ge hwide)
      have hsubzero : xs.length - Nat.card (A ⧸ W.K) = 0 := by
        apply Nat.sub_eq_zero_of_le
        simpa [qcard] using hshort
      rw [hsubzero]
      exact hCtwo
  exact ⟨{
    K := W.K
    strict := hKstrict
    alpha := W.g
    selected := C
    sourceCoset := by
      intro i hi
      exact (mem_occurrencesInAddCoset_iff xs W.K W.g i).1 hi
    card_lower := hcosetCard
  }⟩

end GaoLean

#print axioms GaoLean.one_le_pGroupDStar_of_addSubgroup_ne_bot
#print axioms GaoLean.OrdinaryGMOClaimBOutput.map_nonzeroQuotientOccurrences
#print axioms GaoLean.OrdinaryGMOClaimBOutput.card_sourceOutsideCoset_eq_quotientRExceptionCount
#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_concentration_of_quotientLarge_nonfull
