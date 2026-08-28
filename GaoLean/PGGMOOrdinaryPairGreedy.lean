import GaoLean.PGGMOOrdinaryPairSubgroup

/-!
# Greedy full-sumset core for honest labelled pairs

This module proves the finite combinatorial endpoint needed by the top
stabilizer branch of the ordinary pair-subgroup construction.  If all
labelled pairs `{0, v i}` already sum to the ambient finite group, then a
literal carrier of exactly `|Q| - 1` indices still has full subset-sum
spectrum.  The proof first chooses a cardinality-minimal full carrier, shows
that every newly inserted label strictly grows every prefix spectrum, and
then pads the minimal carrier inside `univ`.

No recursive subgroup certificate or extension hypothesis is used here.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {Q : Type u} [AddCommGroup Q] [Fintype Q]
variable {ι : Type v} [Fintype ι]

noncomputable local instance pairGreedyDecidableEq {α : Type*} :
    DecidableEq α := Classical.decEq α
noncomputable local instance pairGreedyPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

/-! ## Elementary labelled subset-sum identities -/

/-- Adding one fresh labelled index is the same as adding its honest pair
`{0, v i}` to the old subset-sum spectrum. -/
theorem pairIndexSubsetSums_insert
    (v : ι → Q) (s : Finset ι) (i : ι) (hi : i ∉ s) :
    pairIndexSubsetSums v (insert i s) =
      ({0, v i} : Finset Q) + pairIndexSubsetSums v s := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hsum⟩ :=
      (mem_pairIndexSubsetSums_iff v (insert i s) x).1 hx
    by_cases hit : i ∈ t
    · have hsub : t.erase i ⊆ s := by
        intro j hj
        have hjt : j ∈ t := (Finset.mem_erase.mp hj).2
        have hjins := ht hjt
        rcases Finset.mem_insert.mp hjins with rfl | hjs
        · exact ((Finset.mem_erase.mp hj).1 rfl).elim
        · exact hjs
      have htail : (∑ j ∈ t.erase i, v j) ∈
          pairIndexSubsetSums v s :=
        (mem_pairIndexSubsetSums_iff v s _).2 ⟨t.erase i, hsub, rfl⟩
      refine Finset.mem_add.mpr
        ⟨v i, by simp, ∑ j ∈ t.erase i, v j, htail, ?_⟩
      rw [← hsum]
      simpa [add_comm] using t.sum_erase_add v hit
    · have hsub : t ⊆ s := by
        intro j hj
        rcases Finset.mem_insert.mp (ht hj) with hji | hjs
        · exact (hit (hji ▸ hj)).elim
        · exact hjs
      have htmem : (∑ j ∈ t, v j) ∈ pairIndexSubsetSums v s :=
        (mem_pairIndexSubsetSums_iff v s _).2 ⟨t, hsub, rfl⟩
      exact Finset.mem_add.mpr
        ⟨0, by simp, ∑ j ∈ t, v j, htmem, by simpa using hsum⟩
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
    obtain ⟨t, ht, rfl⟩ :=
      (mem_pairIndexSubsetSums_iff v s b).1 hb
    have hit : i ∉ t := fun hit ↦ hi (ht hit)
    simp only [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · refine (mem_pairIndexSubsetSums_iff v (insert i s) x).2
        ⟨t, ht.trans (Finset.subset_insert i s), ?_⟩
      simpa using hab
    · have ha' : a = v i := by simpa using ha
      subst a
      refine (mem_pairIndexSubsetSums_iff v (insert i s) x).2
        ⟨insert i t, ?_, ?_⟩
      · exact Finset.insert_subset_insert i ht
      · rw [Finset.sum_insert hit]
        exact hab

/-- Subset sums of two disjoint labelled carriers factor as their pointwise
sum.  This is the bookkeeping step that turns local redundancy into global
redundancy. -/
theorem pairIndexSubsetSums_union_of_disjoint
    (v : ι → Q) {s t : Finset ι} (hst : Disjoint s t) :
    pairIndexSubsetSums v (s ∪ t) =
      pairIndexSubsetSums v s + pairIndexSubsetSums v t := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hsum⟩ :=
      (mem_pairIndexSubsetSums_iff v (s ∪ t) x).1 hx
    let us := u ∩ s
    let ut := u \ s
    have hus : us ⊆ s := Finset.inter_subset_right
    have hut : ut ⊆ t := by
      intro j hj
      have hju : j ∈ u := (Finset.mem_sdiff.mp hj).1
      have hjns : j ∉ s := (Finset.mem_sdiff.mp hj).2
      rcases Finset.mem_union.mp (hu hju) with hjs | hjt
      · exact (hjns hjs).elim
      · exact hjt
    have hdis : Disjoint us ut := by
      rw [Finset.disjoint_left]
      intro j hjus hjut
      exact (Finset.mem_sdiff.mp hjut).2 (Finset.mem_inter.mp hjus).2
    have hpartition : us ∪ ut = u := by
      ext j
      simp only [us, ut, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff]
      constructor
      · rintro (⟨hju, -⟩ | ⟨hju, -⟩) <;> exact hju
      · intro hju
        by_cases hjs : j ∈ s
        · exact Or.inl ⟨hju, hjs⟩
        · exact Or.inr ⟨hju, hjs⟩
    have hsMem : (∑ j ∈ us, v j) ∈ pairIndexSubsetSums v s :=
      (mem_pairIndexSubsetSums_iff v s _).2 ⟨us, hus, rfl⟩
    have htMem : (∑ j ∈ ut, v j) ∈ pairIndexSubsetSums v t :=
      (mem_pairIndexSubsetSums_iff v t _).2 ⟨ut, hut, rfl⟩
    refine Finset.mem_add.mpr
      ⟨∑ j ∈ us, v j, hsMem, ∑ j ∈ ut, v j, htMem, ?_⟩
    rw [← hsum, ← hpartition, Finset.sum_union hdis]
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
    obtain ⟨sa, hsa, hsumA⟩ :=
      (mem_pairIndexSubsetSums_iff v s a).1 ha
    obtain ⟨tb, htb, hsumB⟩ :=
      (mem_pairIndexSubsetSums_iff v t b).1 hb
    have hdis : Disjoint sa tb := by
      rw [Finset.disjoint_left]
      intro j hjsa hjtb
      exact (Finset.disjoint_left.mp hst) (hsa hjsa) (htb hjtb)
    refine (mem_pairIndexSubsetSums_iff v (s ∪ t) x).2
      ⟨sa ∪ tb, Finset.union_subset
        (hsa.trans Finset.subset_union_left)
        (htb.trans Finset.subset_union_right), ?_⟩
    rw [Finset.sum_union hdis, hsumA, hsumB]
    exact hab

/-- If inserting `i` changes no prefix spectrum, then `i` is redundant in
every ambient carrier containing that prefix. -/
theorem pairIndexSubsetSums_erase_eq_of_insert_eq
    (v : ι → Q) {M s : Finset ι} {i : ι}
    (hiM : i ∈ M) (hsM : s ⊆ M.erase i)
    (heq : pairIndexSubsetSums v (insert i s) =
      pairIndexSubsetSums v s) :
    pairIndexSubsetSums v (M.erase i) = pairIndexSubsetSums v M := by
  classical
  let t := M \ insert i s
  have hinsM : insert i s ⊆ M := by
    exact Finset.insert_subset hiM (hsM.trans (Finset.erase_subset i M))
  have hdisInsert : Disjoint (insert i s) t := by
    rw [Finset.disjoint_left]
    intro j hjins hjt
    exact (Finset.mem_sdiff.mp hjt).2 hjins
  have hdisS : Disjoint s t :=
    hdisInsert.mono_left (Finset.subset_insert i s)
  have hMpartition : insert i s ∪ t = M := by
    exact Finset.union_sdiff_of_subset hinsM
  have herasePartition : s ∪ t = M.erase i := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hjs | hjt
      · exact hsM hjs
      · have hjdiff := Finset.mem_sdiff.mp hjt
        exact Finset.mem_erase.mpr
          ⟨fun hji ↦ hjdiff.2 (by subst j; simp), hjdiff.1⟩
    · intro hj
      have hjErase := Finset.mem_erase.mp hj
      by_cases hjs : j ∈ s
      · exact Finset.mem_union_left t hjs
      · apply Finset.mem_union_right s
        exact Finset.mem_sdiff.mpr
          ⟨hjErase.2, by simpa [hjErase.1, hjs]⟩
  calc
    pairIndexSubsetSums v (M.erase i) =
        pairIndexSubsetSums v (s ∪ t) := by rw [herasePartition]
    _ = pairIndexSubsetSums v s + pairIndexSubsetSums v t :=
      pairIndexSubsetSums_union_of_disjoint v hdisS
    _ = pairIndexSubsetSums v (insert i s) +
        pairIndexSubsetSums v t := by rw [heq]
    _ = pairIndexSubsetSums v (insert i s ∪ t) :=
      (pairIndexSubsetSums_union_of_disjoint v hdisInsert).symm
    _ = pairIndexSubsetSums v M := by rw [hMpartition]

/-! ## Minimal full carriers -/

/-- A carrier for which deleting any label changes its spectrum has at most
one fewer labels than spectrum values. -/
theorem card_add_one_le_pairIndexSubsetSums_card_of_erase_minimal
    (v : ι → Q) (M : Finset ι)
    (hminimal : ∀ i ∈ M,
      pairIndexSubsetSums v (M.erase i) ≠ pairIndexSubsetSums v M) :
    M.card + 1 ≤ (pairIndexSubsetSums v M).card := by
  classical
  have aux : ∀ s : Finset ι, s ⊆ M →
      s.card + 1 ≤ (pairIndexSubsetSums v s).card := by
    intro s hsM
    induction s using Finset.induction_on with
    | empty =>
        simp [pairIndexSubsetSums]
    | @insert i s hi ih =>
        have hiM : i ∈ M := hsM (Finset.mem_insert_self i s)
        have hsM' : s ⊆ M.erase i := by
          intro j hjs
          exact Finset.mem_erase.mpr
            ⟨fun hji ↦ hi (hji ▸ hjs), hsM (Finset.mem_insert_of_mem hjs)⟩
        have hne : pairIndexSubsetSums v s ≠
            pairIndexSubsetSums v (insert i s) := by
          intro heq
          exact hminimal i hiM
            (pairIndexSubsetSums_erase_eq_of_insert_eq
              v hiM hsM' heq.symm)
        have hstrict : pairIndexSubsetSums v s ⊂
            pairIndexSubsetSums v (insert i s) := by
          rw [Finset.ssubset_iff_subset_ne]
          exact ⟨pairIndexSubsetSums_mono v (Finset.subset_insert i s), hne⟩
        have hcardStrict := Finset.card_lt_card hstrict
        have ih' := ih (hsM'.trans (Finset.erase_subset i M))
        rw [Finset.card_insert_of_notMem hi]
        omega
  exact aux M Finset.Subset.rfl

/-- A full labelled subset-sum spectrum has a full subcarrier of exact
cardinality `|Q| - 1`, provided that many labels are available. -/
theorem exists_pairIndexSubsetSums_core_card_eq_card_sub_one
    [Nontrivial Q] (v : ι → Q)
    (hlen : Nat.card Q - 1 ≤ Nat.card ι)
    (hfull : pairIndexSubsetSums v (Finset.univ : Finset ι) =
      (Finset.univ : Finset Q)) :
    ∃ core : Finset ι,
      core.card = Nat.card Q - 1 ∧
        pairIndexSubsetSums v core = (Finset.univ : Finset Q) := by
  classical
  let candidates := (Finset.univ : Finset ι).powerset.filter fun s ↦
    pairIndexSubsetSums v s = (Finset.univ : Finset Q)
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hfull⟩
  obtain ⟨M, hMcandidate, hMmin⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hMsub : M ⊆ (Finset.univ : Finset ι) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMcandidate).1
  have hMfull : pairIndexSubsetSums v M = (Finset.univ : Finset Q) :=
    (Finset.mem_filter.mp hMcandidate).2
  have hMeraseMinimal : ∀ i ∈ M,
      pairIndexSubsetSums v (M.erase i) ≠ pairIndexSubsetSums v M := by
    intro i hiM heq
    have heraseFull : pairIndexSubsetSums v (M.erase i) =
        (Finset.univ : Finset Q) := heq.trans hMfull
    have heraseCandidate : M.erase i ∈ candidates :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr
          ((Finset.erase_subset i M).trans hMsub), heraseFull⟩
    have hle := hMmin (M.erase i) heraseCandidate
    have hcardErase := Finset.card_erase_of_mem hiM
    have hMpos : 0 < M.card := Finset.card_pos.mpr ⟨i, hiM⟩
    omega
  have hMcardGrowth :=
    card_add_one_le_pairIndexSubsetSums_card_of_erase_minimal
      v M hMeraseMinimal
  have hMcard : M.card ≤ Nat.card Q - 1 := by
    rw [hMfull, Finset.card_univ, ← Nat.card_eq_fintype_card] at hMcardGrowth
    omega
  have htargetLe : Nat.card Q - 1 ≤ (Finset.univ : Finset ι).card := by
    simpa [Nat.card_eq_fintype_card] using hlen
  obtain ⟨core, hMcore, hcoreUniv, hcoreCard⟩ :=
    Finset.exists_subsuperset_card_eq hMsub hMcard htargetLe
  refine ⟨core, hcoreCard, ?_⟩
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  exact pairIndexSubsetSums_mono v hMcore (by simpa [hMfull])

/-! ## Full-layer and top-stabilizer consumers -/

/-- The full layer sumset of the honest pair setpartition is definitionally
the labelled subset-sum spectrum on all indices. -/
theorem pairIndexFullSumset_eq_pairIndexSubsetSums_univ
    (v : ι → Q) :
    pairIndexFullSumset v =
      pairIndexSubsetSums v (Finset.univ : Finset ι) := by
  classical
  have listLemma : ∀ l : List ι, l.Nodup →
      fullLayerSumSpectrum (l.map fun i ↦ pairIndexLayer v i) =
        pairIndexSubsetSums v l.toFinset := by
    intro l hl
    induction l with
    | nil =>
        simp [pairIndexSubsetSums]
    | cons i l ih =>
        have hlParts := List.nodup_cons.mp hl
        have hi : i ∉ l.toFinset := by simpa using hlParts.1
        rw [List.map_cons, fullLayerSumSpectrum_cons, ih hlParts.2,
          List.toFinset_cons, pairIndexSubsetSums_insert v l.toFinset i hi]
        rfl
  unfold pairIndexFullSumset pairIndexSetpartition pairIndexSetpartitionOn
  simpa using listLemma (Finset.univ : Finset ι).toList
    (Finset.nodup_toList (Finset.univ : Finset ι))

/-- A top stabilizer of the nonempty honest pair full sumset forces that
sumset to be the whole finite group. -/
theorem pairIndexFullSumset_eq_univ_of_stabilizer_eq_top
    (v : ι → Q) (htop : pairIndexStabilizer v = ⊤) :
    pairIndexFullSumset v = (Finset.univ : Finset Q) := by
  classical
  by_contra hne
  have hstrict := stabilizer_lt_top_of_finset_nonempty_ne_univ
    (pairIndexFullSumset v) (pairIndexFullSumset_nonempty v) hne
  exact (ne_of_lt hstrict) htop

/-- The top-stabilizer branch directly supplies the exact `|Q|-1` full
carrier consumed by the ordinary pair-subgroup construction. -/
theorem exists_pairIndexSubsetSums_core_of_stabilizer_eq_top
    [Nontrivial Q] (v : ι → Q)
    (hlen : Nat.card Q - 1 ≤ Nat.card ι)
    (htop : pairIndexStabilizer v = ⊤) :
    ∃ core : Finset ι,
      core.card = Nat.card Q - 1 ∧
        pairIndexSubsetSums v core = (Finset.univ : Finset Q) := by
  apply exists_pairIndexSubsetSums_core_card_eq_card_sub_one v hlen
  rw [← pairIndexFullSumset_eq_pairIndexSubsetSums_univ]
  exact pairIndexFullSumset_eq_univ_of_stabilizer_eq_top v htop

end GaoLean

#print axioms GaoLean.exists_pairIndexSubsetSums_core_card_eq_card_sub_one
#print axioms GaoLean.pairIndexFullSumset_eq_pairIndexSubsetSums_univ
#print axioms GaoLean.pairIndexFullSumset_eq_univ_of_stabilizer_eq_top
#print axioms GaoLean.exists_pairIndexSubsetSums_core_of_stabilizer_eq_top
