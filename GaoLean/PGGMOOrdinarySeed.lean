import GaoLean.PGGMOTheorem21

/-!
# Occurrence-faithful capped seed preparation

This file isolates the finite combinatorics needed before invoking the
ordinary Theorem-E driver.  The cap is imposed on labelled occurrences, not
on the support of the source list.  The canonical capped selection takes the
first `min r multiplicity` occurrences from every value fiber.

The final dichotomy is intentionally modest: if the capped fiber mass is too
small to supply the requested seed, it returns a concrete value whose source
fiber strictly exceeds the cap.  It does not turn that local excess into a
coset-concentration or target conclusion; that is the separate Step-1 branch.
-/

namespace GaoLean

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Total labelled mass remaining after every value fiber is capped at `r`. -/
noncomputable def cappedFiberMass (xs : List A) (r : ℕ) : ℕ := by
  classical
  exact ∑ a : A, min r (occurrenceFiber xs a).card

/-- The first `min r multiplicity` labelled occurrences in one value fiber. -/
noncomputable def cappedOccurrenceFiber
    (xs : List A) (a : A) (r : ℕ) : Selection xs := by
  classical
  let F := occurrenceFiber xs a
  let e : Fin (min r F.card) ↪ Occurrence xs :=
    (Fin.castLEEmb (min_le_right r F.card)).trans
      (F.orderEmbOfFin rfl).toEmbedding
  exact (Finset.univ : Finset (Fin (min r F.card))).map e

theorem cappedOccurrenceFiber_subset_occurrenceFiber
    (xs : List A) (a : A) (r : ℕ) :
    cappedOccurrenceFiber xs a r ⊆ occurrenceFiber xs a := by
  classical
  intro i hi
  simp only [cappedOccurrenceFiber, Finset.mem_map] at hi
  obtain ⟨j, _hj, rfl⟩ := hi
  exact Finset.orderEmbOfFin_mem (occurrenceFiber xs a) rfl _

@[simp]
theorem card_cappedOccurrenceFiber
    (xs : List A) (a : A) (r : ℕ) :
    (cappedOccurrenceFiber xs a r).card =
      min r (occurrenceFiber xs a).card := by
  classical
  simp [cappedOccurrenceFiber]

theorem occurrenceFiber_disjoint_of_ne
    (xs : List A) {a b : A} (hab : a ≠ b) :
    Disjoint (occurrenceFiber xs a) (occurrenceFiber xs b) := by
  classical
  rw [Finset.disjoint_left]
  intro i hia hib
  have ha : occurrenceValue xs i = a := by
    simpa [occurrenceFiber] using hia
  have hb : occurrenceValue xs i = b := by
    simpa [occurrenceFiber] using hib
  exact hab (ha.symm.trans hb)

/-- Union of the canonical capped pieces over all values. -/
noncomputable def cappedOccurrenceSelection
    (xs : List A) (r : ℕ) : Selection xs := by
  classical
  exact (Finset.univ : Finset A).biUnion fun a ↦
    cappedOccurrenceFiber xs a r

@[simp]
theorem card_cappedOccurrenceSelection
    (xs : List A) (r : ℕ) :
    (cappedOccurrenceSelection xs r).card = cappedFiberMass xs r := by
  classical
  have hpair : ((Finset.univ : Finset A) : Set A).PairwiseDisjoint
      (fun a ↦ cappedOccurrenceFiber xs a r) := by
    intro a _ha b _hb hab
    exact (occurrenceFiber_disjoint_of_ne xs hab).mono
      (cappedOccurrenceFiber_subset_occurrenceFiber xs a r)
      (cappedOccurrenceFiber_subset_occurrenceFiber xs b r)
  rw [cappedOccurrenceSelection, Finset.card_biUnion hpair]
  simp [cappedFiberMass]

theorem cappedOccurrenceSelection_multiplicity
    (xs : List A) (r : ℕ) :
    SelectionMultiplicityAtMost xs (cappedOccurrenceSelection xs r) r := by
  classical
  intro a
  have hsub :
      ((cappedOccurrenceSelection xs r).filter fun i ↦
          occurrenceValue xs i = a) ⊆
        cappedOccurrenceFiber xs a r := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    simp only [cappedOccurrenceSelection, Finset.mem_biUnion] at hi'
    obtain ⟨b, _hb, hib⟩ := hi'.1
    have hibFiber :=
      cappedOccurrenceFiber_subset_occurrenceFiber xs b r hib
    have hvalueB : occurrenceValue xs i = b := by
      simpa [occurrenceFiber] using hibFiber
    have hba : b = a := hvalueB.symm.trans hi'.2
    simpa [hba] using hib
  exact (Finset.card_le_card hsub).trans (by
    rw [card_cappedOccurrenceFiber]
    exact min_le_left _ _)

theorem selectionMultiplicityAtMost_mono
    {xs : List A} {I J : Selection xs} {r : ℕ}
    (hIJ : I ⊆ J) (hJ : SelectionMultiplicityAtMost xs J r) :
    SelectionMultiplicityAtMost xs I r := by
  classical
  intro a
  exact (Finset.card_le_card (Finset.filter_mono hIJ)).trans (hJ a)

theorem selection_eq_biUnion_valueFibers
    (xs : List A) (I : Selection xs) :
    (Finset.univ : Finset A).biUnion
        (fun a ↦ I.filter fun i ↦ occurrenceValue xs i = a) = I := by
  classical
  ext i
  simp

theorem selection_card_le_cappedFiberMass
    (xs : List A) (I : Selection xs) (r : ℕ)
    (hcap : SelectionMultiplicityAtMost xs I r) :
    I.card ≤ cappedFiberMass xs r := by
  classical
  have hpair : ((Finset.univ : Finset A) : Set A).PairwiseDisjoint
      (fun a ↦ I.filter fun i ↦ occurrenceValue xs i = a) := by
    intro a _ha b _hb hab
    rw [Finset.disjoint_left]
    intro i hia hib
    have ha := (Finset.mem_filter.mp hia).2
    have hb := (Finset.mem_filter.mp hib).2
    exact hab (ha.symm.trans hb)
  rw [← selection_eq_biUnion_valueFibers xs I,
    Finset.card_biUnion hpair, cappedFiberMass]
  apply Finset.sum_le_sum
  intro a _ha
  apply Nat.le_min
  · exact hcap a
  · apply Finset.card_le_card
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    simpa [occurrenceFiber] using hi'.2

/-- The capped mass criterion is sufficient and necessary for an exact-card
labelled seed with multiplicity at most `r`. -/
theorem exists_selection_card_eq_and_multiplicityAtMost_iff
    (xs : List A) (r m : ℕ) :
    m ≤ cappedFiberMass xs r ↔
      ∃ seed : Selection xs,
        seed ⊆ (Finset.univ : Selection xs) ∧
        seed.card = m ∧ SelectionMultiplicityAtMost xs seed r := by
  classical
  constructor
  · intro hm
    have hm' : m ≤ (cappedOccurrenceSelection xs r).card := by
      simpa using hm
    obtain ⟨seed, hseed, hcard⟩ :=
      Finset.exists_subset_card_eq hm'
    exact ⟨seed, Finset.subset_univ _, hcard,
      selectionMultiplicityAtMost_mono hseed
        (cappedOccurrenceSelection_multiplicity xs r)⟩
  · rintro ⟨seed, _hseed, hcard, hcap⟩
    rw [← hcard]
    exact selection_card_le_cappedFiberMass xs seed r hcap

/-- If the capped mass is too small despite enough total occurrences, a
specific source value has multiplicity strictly above the cap. -/
theorem exists_excess_occurrenceFiber_of_cappedFiberMass_lt
    (xs : List A) (r m : ℕ) (hm : m ≤ xs.length)
    (hsmall : cappedFiberMass xs r < m) :
    ∃ a : A, r < (occurrenceFiber xs a).card := by
  classical
  by_contra hno
  push_neg at hno
  have hunivCap : SelectionMultiplicityAtMost xs
      (Finset.univ : Selection xs) r := by
    intro a
    simpa [occurrenceFiber] using hno a
  have htotal := selection_card_le_cappedFiberMass xs
    (Finset.univ : Selection xs) r hunivCap
  have hlenMass : xs.length ≤ cappedFiberMass xs r := by
    simpa using htotal
  omega

/-- Exact source-level preprocessing dichotomy.  The right branch is only a
local high-multiplicity witness; the later Step-1 argument must consume it. -/
theorem exists_capped_seed_or_excess_occurrenceFiber
    (xs : List A) (r m : ℕ) (hm : m ≤ xs.length) :
    (∃ seed : Selection xs,
        seed ⊆ (Finset.univ : Selection xs) ∧
        seed.card = m ∧ SelectionMultiplicityAtMost xs seed r) ∨
      (cappedFiberMass xs r < m ∧
        ∃ a : A, r < (occurrenceFiber xs a).card) := by
  classical
  by_cases hmass : m ≤ cappedFiberMass xs r
  · exact Or.inl
      ((exists_selection_card_eq_and_multiplicityAtMost_iff xs r m).1 hmass)
  · have hsmall : cappedFiberMass xs r < m := Nat.lt_of_not_ge hmass
    exact Or.inr ⟨hsmall,
      exists_excess_occurrenceFiber_of_cappedFiberMass_lt xs r m hm hsmall⟩

/-- Failure of every exact-card capped seed exposes a concrete overfull
value fiber. -/
theorem exists_excess_occurrenceFiber_of_no_capped_seed
    (xs : List A) (r m : ℕ) (hm : m ≤ xs.length)
    (hfail : ¬ ∃ seed : Selection xs,
      seed ⊆ (Finset.univ : Selection xs) ∧
      seed.card = m ∧ SelectionMultiplicityAtMost xs seed r) :
    ∃ a : A, r < (occurrenceFiber xs a).card := by
  have hsmall : cappedFiberMass xs r < m := by
    have hnot : ¬ m ≤ cappedFiberMass xs r := by
      intro hmass
      exact hfail
        ((exists_selection_card_eq_and_multiplicityAtMost_iff xs r m).1 hmass)
    exact Nat.lt_of_not_ge hnot
  exact exists_excess_occurrenceFiber_of_cappedFiberMass_lt xs r m hm hsmall

end GaoLean

