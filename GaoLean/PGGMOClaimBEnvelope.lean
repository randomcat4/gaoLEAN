import GaoLean.PGGMOClaimBMaximal

/-!
# Honest terminal envelopes for ordinary GMO Claim B

The plain Claim-B payload remembers the saturated small partition but erases
the original `n`-cell Theorem-E partition from which it was cut.  This module
keeps that data in an honest envelope: the full partition, the actual cell
embedding, and occurrence-level inclusion of every small cell in its original
full cell.

No terminal conclusion is stored in the envelope.  Instead, a general
partial-layer extension theorem proves that a full sumset on the embedded
small cells forces the full `n`-cell sumset to be the ambient group.  Thus a
top Claim-B subgroup yields the large branch of Theorem 2.1 without the false
equalities `pGroupDStar K = n` or `supportCard = seed.card`.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A genuine Claim-B witness together with the full source-faithful
Theorem-E partition from which its cells were selected. -/
structure OrdinaryGMOClaimBEnvelope
    (xs : List A) (seed : Selection xs) (n : ℕ) where
  W : OrdinaryGMOClaimBOutput xs seed n
  Pfull : Theorem21SetPartition xs n seed.card
  e : Fin (pGroupDStar W.K) ↪ Fin n
  cell_subset : ∀ j : Fin (pGroupDStar W.K),
    W.partition.cells j ⊆ Pfull.cells (e j)

/-- The existing labelled construction already carries all data needed for
an envelope.  The small witness itself is the previously proved Claim-B
output; only its original parent partition and embedding are retained beside
it. -/
noncomputable def ordinaryGMOClaimBEnvelope_of_insideCoreEmbeddedPartition
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P : Theorem21SetPartition xs n seed.card)
    (H K : AddSubgroup A) (hK : K ≠ ⊥) (g : A)
    (e : Fin (pGroupDStar K) ↪ Fin n)
    (hne : ∀ j : Fin (pGroupDStar K),
      (P.insideCoreCell H (e j)).Nonempty)
    (choice : P.CellCosetOccurrenceChoice K g)
    (hselected : ∀ (j : Fin (pGroupDStar K)) (i : Occurrence xs),
      i ∈ P.insideCoreCell H (e j) →
        occurrenceValue xs i ∈ addCosetFinset K g)
    (hallUnused : ∀ i : Occurrence xs, i ∉ P.support →
      occurrenceValue xs i ∈ addCosetFinset K g)
    (hsaturation :
      P.insideCoreEmbeddedIteratedSum H e =
        addCosetFinset K ((pGroupDStar K) • g)) :
    OrdinaryGMOClaimBEnvelope xs seed n := by
  classical
  let W := ordinaryGMOClaimBOutput_of_insideCoreEmbeddedPartition
    P H K hK g e hne choice hselected hallUnused hsaturation
  refine {
    W := W
    Pfull := P
    e := e
    cell_subset := ?_
  }
  intro j i hi
  change i ∈ P.insideCoreCell H (e j) at hi
  exact (P.mem_insideCoreCell_iff H (e j) i).1 hi |>.1

/-- The M100 Case-1 hypotheses produce an envelope directly from the same
source-faithful Theorem-E partition and the same verified Claim-B data. -/
theorem GMOTheoremESourceOutput.nonempty_ordinaryGMOClaimBEnvelope_case1
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (hambient : pGroupDStar A ≤ n)
    (hN : 2 ≤ out.partition.commonCosetCount out.H)
    (hnotLarge :
      ¬ GMOTheorem21LargeAlternative xs seed n out.partition) :
    Nonempty (OrdinaryGMOClaimBEnvelope xs seed n) := by
  classical
  have hH : out.H ≠ ⊥ := out.period_ne_bot_of_not_large hnotLarge
  letI : Nontrivial out.H :=
    (AddSubgroup.nontrivial_iff_ne_bot out.H).2 hH
  letI : Nontrivial A :=
    Function.Injective.nontrivial out.H.subtype_injective
  have hnTwo : 2 ≤ n :=
    (two_le_pGroupDStar_of_odd_pGroup p hp hpTwo hA).trans hambient
  obtain ⟨g, hg, j, k, hjk, hthick⟩ :=
    out.exists_commonCore_two_cells_large_slice hnTwo hN hnotLarge
  let K := claimBIntermediateSubgroup out.partition out.H g
  have hK : K ≠ ⊥ := by
    dsimp [K]
    exact claimBIntermediateSubgroup_ne_bot_of_two_le_commonCosetCount
      out.partition out.H g hN
  have hr : pGroupDStar K ≤ n := by
    dsimp [K]
    exact pGroupDStar_claimBIntermediateSubgroup_le_of_ambient_budget
      out.partition out.H g hambient
  obtain ⟨e, hne, hfront, hsaturation⟩ :=
    out.partition.exists_pairFrontEmbedding_exact_saturation
      p hp hpTwo hA out.H hH g hg j k hjk hthick (by
        simpa [K] using hr)
  let choice : out.partition.CellCosetOccurrenceChoice K g := by
    dsimp [K]
    exact out.partition.claimBCellCosetOccurrenceChoice out.H g hg
  have hselected :
      ∀ (q : Fin (pGroupDStar K)) (i : Occurrence xs),
        i ∈ out.partition.insideCoreCell out.H (e q) →
          occurrenceValue xs i ∈ addCosetFinset K g := by
    intro q i hi
    dsimp [K]
    exact out.partition.insideCoreCell_value_mem_claimBCoset
      out.H g hg (e q) i hi
  have hallUnused :
      ∀ i : Occurrence xs, i ∉ out.partition.support →
        occurrenceValue xs i ∈ addCosetFinset K g := by
    intro i hi
    dsimp [K]
    exact out.unused_value_mem_claimBCoset g hg hnotLarge i hi
  refine ⟨ordinaryGMOClaimBEnvelope_of_insideCoreEmbeddedPartition
    out.partition out.H K hK g e ?_ choice hselected hallUnused ?_⟩
  · simpa [K] using hne
  · simpa [K] using hsaturation

/-- Membership in a Theorem-2.1 partition sumset, expressed directly as one
value choice from every indexed cell. -/
theorem Theorem21SetPartition.mem_sumset_iff_exists_value_choice
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m) (y : A) :
    y ∈ P.sumset ↔
      ∃ a : Fin n → A,
        (∀ c, a c ∈ P.valueCell c) ∧ (∑ c, a c) = y := by
  classical
  unfold Theorem21SetPartition.sumset
  rw [mem_fullLayerSumSpectrum_iff_exists_choice]
  let f : Fin n ≃ Fin P.valueCells.length :=
    finCongr P.length_valueCells.symm
  constructor
  · rintro ⟨a, ha, hsum⟩
    refine ⟨fun c ↦ a (f c), ?_, ?_⟩
    · intro c
      have hc := ha (f c)
      simp only [Theorem21SetPartition.valueCells, List.get_ofFn] at hc
      convert hc using 1
      · congr 1
      · rfl
    · exact (f.sum_comp a).trans hsum
  · rintro ⟨a, ha, hsum⟩
    refine ⟨fun i ↦ a (f.symm i), ?_, ?_⟩
    · intro i
      have hi := ha (f.symm i)
      simp only [Theorem21SetPartition.valueCells, List.get_ofFn]
      convert hi using 1
      · congr 1
      · rfl
    · exact (f.symm.sum_comp a).trans hsum

/-- Occurrence-level cell inclusion induces literal inclusion of value cells. -/
theorem Theorem21SetPartition.valueCell_subset_of_cells_subset
    {xs : List A} {r n mr mn : ℕ}
    (Q : Theorem21SetPartition xs r mr)
    (P : Theorem21SetPartition xs n mn)
    (e : Fin r ↪ Fin n)
    (hcell : ∀ j : Fin r, Q.cells j ⊆ P.cells (e j))
    (j : Fin r) :
    Q.valueCell j ⊆ P.valueCell (e j) := by
  classical
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨i, hcell j hi, rfl⟩

/-- A full sumset on distinct embedded cells remains full after enlarging
those cells and adjoining all other nonempty layers of the ambient partition.
This is the missing terminal bridge; it uses only the honest cell embedding
and occurrence inclusion. -/
theorem theorem21SetPartition_sumset_eq_univ_of_embedded_sumset_eq_univ
    {xs : List A} {r n mr mn : ℕ}
    (Q : Theorem21SetPartition xs r mr)
    (P : Theorem21SetPartition xs n mn)
    (e : Fin r ↪ Fin n)
    (hcell : ∀ j : Fin r, Q.cells j ⊆ P.cells (e j))
    (hfull : Q.sumset = Finset.univ) :
    P.sumset = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  let selected := selectedCellIndices e
  let unselected := unselectedCellIndices e
  let b : Fin n → A := fun c ↦
    occurrenceValue xs (Classical.choose (P.cells_nonempty c))
  have hb (c : Fin n) : b c ∈ P.valueCell c := by
    apply Finset.mem_image.mpr
    exact ⟨Classical.choose (P.cells_nonempty c),
      Classical.choose_spec (P.cells_nonempty c), rfl⟩
  let tail : A := ∑ c ∈ unselected, b c
  have hyQ : y - tail ∈ Q.sumset := by
    rw [hfull]
    exact Finset.mem_univ _
  obtain ⟨q, hq, hqsum⟩ :=
    (Q.mem_sumset_iff_exists_value_choice (y - tail)).1 hyQ
  have hselectedExists (c : Fin n) (hc : c ∈ selected) :
      ∃ j : Fin r, e j = c := by
    exact (mem_selectedCellIndices_iff e c).1 hc
  let preimage (c : Fin n) (hc : c ∈ selected) : Fin r :=
    Classical.choose (hselectedExists c hc)
  have hpreimage (c : Fin n) (hc : c ∈ selected) :
      e (preimage c hc) = c :=
    Classical.choose_spec (hselectedExists c hc)
  let a : Fin n → A := fun c ↦
    if hc : c ∈ selected then q (preimage c hc) else b c
  have haSelected (j : Fin r) : a (e j) = q j := by
    have hej : e j ∈ selected :=
      (mem_selectedCellIndices_iff e (e j)).2 ⟨j, rfl⟩
    simp only [a, dif_pos hej]
    congr 1
    apply e.injective
    exact hpreimage (e j) hej
  have ha (c : Fin n) : a c ∈ P.valueCell c := by
    by_cases hc : c ∈ selected
    · simp only [a, dif_pos hc]
      have hqmem := hq (preimage c hc)
      have hv := Q.valueCell_subset_of_cells_subset P e hcell
        (preimage c hc) hqmem
      simpa [hpreimage c hc] using hv
    · simp only [a, dif_neg hc]
      exact hb c
  have hselectedSum :
      (∑ c ∈ selected, a c) = ∑ j, q j := by
    symm
    refine Finset.sum_bij (fun j _ ↦ e j) ?_ ?_ ?_ ?_
    · intro j _
      exact (mem_selectedCellIndices_iff e (e j)).2 ⟨j, rfl⟩
    · intro i _ j _ hij
      exact e.injective hij
    · intro c hc
      obtain ⟨j, hj⟩ := (mem_selectedCellIndices_iff e c).1 hc
      exact ⟨j, Finset.mem_univ j, hj⟩
    · intro j _
      exact (haSelected j).symm
  have hUnselectedNotMem (c : Fin n) (hc : c ∈ unselected) :
      c ∉ selected := by
    exact (Finset.mem_sdiff.mp hc).2
  have hunselectedSum : (∑ c ∈ unselected, a c) = tail := by
    dsimp only [tail]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [a, dif_neg (hUnselectedNotMem c hc)]
  have hdisjoint : Disjoint selected unselected := by
    dsimp only [selected, unselected, unselectedCellIndices]
    exact Finset.disjoint_sdiff
  have hunion : selected ∪ unselected = Finset.univ := by
    dsimp only [selected, unselected, unselectedCellIndices]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  apply (P.mem_sumset_iff_exists_value_choice y).2
  refine ⟨a, ha, ?_⟩
  calc
    (∑ c, a c) = ∑ c ∈ selected ∪ unselected, a c := by rw [hunion]
    _ = (∑ c ∈ selected, a c) + ∑ c ∈ unselected, a c :=
      Finset.sum_union hdisjoint
    _ = (y - tail) + tail := by rw [hselectedSum, hunselectedSum, hqsum]
    _ = y := sub_add_cancel y tail

/-- Choose a cardinal-maximal genuine envelope, retaining its full parent
partition and embedding rather than maximizing only a projected witness. -/
theorem exists_card_maximal_ordinaryGMOClaimBEnvelope
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (hne : Nonempty (OrdinaryGMOClaimBEnvelope xs seed n)) :
    ∃ Emax : OrdinaryGMOClaimBEnvelope xs seed n,
      ∀ E : OrdinaryGMOClaimBEnvelope xs seed n,
        Nat.card E.W.K ≤ Nat.card Emax.W.K := by
  classical
  let cards : Finset ℕ :=
    (Finset.range (Nat.card A + 1)).filter fun c ↦
      ∃ E : OrdinaryGMOClaimBEnvelope xs seed n, Nat.card E.W.K = c
  have hmem (E : OrdinaryGMOClaimBEnvelope xs seed n) :
      Nat.card E.W.K ∈ cards := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ⟨E, rfl⟩⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (natCard_addSubgroup_le_ambient E.W.K)
  obtain ⟨E₀⟩ := hne
  have hcards : cards.Nonempty := ⟨Nat.card E₀.W.K, hmem E₀⟩
  obtain ⟨c, hc, hcmax⟩ :=
    Finset.exists_max_image cards (fun q ↦ q) hcards
  obtain ⟨Emax, hEmax⟩ :
      ∃ E : OrdinaryGMOClaimBEnvelope xs seed n, Nat.card E.W.K = c :=
    (Finset.mem_filter.mp hc).2
  refine ⟨Emax, ?_⟩
  intro E
  have hle : Nat.card E.W.K ≤ c := by
    simpa using hcmax (Nat.card E.W.K) (hmem E)
  exact hle.trans_eq hEmax.symm

/-- A cardinal-maximal envelope cannot be strictly enlarged by the subgroup
of another genuine envelope. -/
theorem OrdinaryGMOClaimBEnvelope.not_subgroup_lt_of_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (Emax : OrdinaryGMOClaimBEnvelope xs seed n)
    (hmax : ∀ E : OrdinaryGMOClaimBEnvelope xs seed n,
      Nat.card E.W.K ≤ Nat.card Emax.W.K)
    (E : OrdinaryGMOClaimBEnvelope xs seed n) :
    ¬ Emax.W.K < E.W.K := by
  intro hlt
  exact (Nat.not_lt_of_ge (hmax E)) (natCard_lt_of_addSubgroup_lt hlt)

/-- A top subgroup saturates the retained full `n`-cell partition. -/
theorem OrdinaryGMOClaimBEnvelope.full_sumset_eq_univ_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (E : OrdinaryGMOClaimBEnvelope xs seed n) (hK : E.W.K = ⊤) :
    E.Pfull.sumset = Finset.univ := by
  apply theorem21SetPartition_sumset_eq_univ_of_embedded_sumset_eq_univ
    E.W.partition E.Pfull E.e E.cell_subset
  exact E.W.sumset_eq_univ_of_K_eq_top hK

/-- The top-envelope endpoint is exactly the large alternative for the
retained source-faithful `n`-cell partition. -/
theorem OrdinaryGMOClaimBEnvelope.largeAlternative_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (E : OrdinaryGMOClaimBEnvelope xs seed n) (hK : E.W.K = ⊤) :
    GMOTheorem21LargeAlternative xs seed n E.Pfull := by
  classical
  refine ⟨?_⟩
  rw [E.full_sumset_eq_univ_of_K_eq_top hK, Finset.card_univ]
  simpa only [Nat.card_eq_fintype_card] using
    min_le_left (Nat.card A) (seed.card - n + 1)

/-- Complete Theorem-2.1 output in the top-envelope branch. -/
noncomputable def OrdinaryGMOClaimBEnvelope.toGMOTheorem21Output_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (E : OrdinaryGMOClaimBEnvelope xs seed n) (hK : E.W.K = ⊤) :
    GMOTheorem21Output xs seed n where
  partition := E.Pfull
  alternative := Or.inl (E.largeAlternative_of_K_eq_top hK)

end GaoLean

#print axioms GaoLean.ordinaryGMOClaimBEnvelope_of_insideCoreEmbeddedPartition
#print axioms GaoLean.GMOTheoremESourceOutput.nonempty_ordinaryGMOClaimBEnvelope_case1
#print axioms GaoLean.theorem21SetPartition_sumset_eq_univ_of_embedded_sumset_eq_univ
#print axioms GaoLean.exists_card_maximal_ordinaryGMOClaimBEnvelope
#print axioms GaoLean.OrdinaryGMOClaimBEnvelope.largeAlternative_of_K_eq_top
#print axioms GaoLean.OrdinaryGMOClaimBEnvelope.toGMOTheorem21Output_of_K_eq_top
