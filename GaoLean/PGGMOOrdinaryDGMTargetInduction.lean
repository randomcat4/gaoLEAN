import GaoLean.PGGMOOrdinaryDGMSingleton
import GaoLean.PGGMOOrdinaryDGMComplement
import GaoLean.PGGMOOrdinaryTargetBase
import GaoLean.PGGMOProvidersFromDGM

/-!
# Ordinary prescribed-target induction from DGM

This module proves the prescribed-target endpoint for every finite additive
commutative group at the canonical Davenport width.  The source is first
restricted to the literal prefix of length `n + pGroupDStar A`; all later
complement arguments therefore take place in an exact occurrence universe.

The recursive branch quotients by the stabilizer of the complementary
`pGroupDStar A`-spectrum.  A quotient target is pulled back through the
genuine equivalence of list positions.  Its error lies in the stabilizer, and
translation by the *negative* error produces an honest ambient target.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance ordinaryTargetQuotientFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-! ## Exact-prefix transport -/

/-- The literal inclusion of occurrences in a prefix into occurrences of the
full source. -/
def ordinaryTakeOccurrenceEmbedding
    (xs : List A) (N : ℕ) (hN : N ≤ xs.length) :
    Occurrence (xs.take N) ↪ Occurrence xs where
  toFun i :=
    ⟨i.1, lt_of_lt_of_le i.2
      ((List.length_take_le N xs).trans hN)⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg
      (fun z : Occurrence xs ↦ z.1) hij

theorem occurrenceValue_ordinaryTakeOccurrenceEmbedding
    (xs : List A) (N : ℕ) (hN : N ≤ xs.length)
    (i : Occurrence (xs.take N)) :
    occurrenceValue xs (ordinaryTakeOccurrenceEmbedding xs N hN i) =
      occurrenceValue (xs.take N) i := by
  simp [ordinaryTakeOccurrenceEmbedding, occurrenceValue,
    List.get_eq_getElem]

/-- An occurrence-labelled target selected in a literal prefix remains the
same target in the full source. -/
noncomputable def OrdinaryGMOTargetOutput.ofTake
    (xs : List A) (N n : ℕ) (hN : N ≤ xs.length)
    (O : OrdinaryGMOTargetOutput (xs.take N) n) :
    OrdinaryGMOTargetOutput xs n := by
  classical
  let e := ordinaryTakeOccurrenceEmbedding xs N hN
  let selected : Selection xs := O.selected.map e
  refine {
    selected := selected
    card_selected := ?_
    sum_mem_target := ?_
  }
  · simpa [selected] using O.card_selected
  · obtain ⟨a, ha⟩ := O.sum_mem_target
    refine ⟨a, ?_⟩
    calc
      (∑ i ∈ selected, occurrenceValue xs i) =
          ∑ i ∈ O.selected,
            occurrenceValue xs (e i) := by
              simp [selected, Finset.sum_map]
      _ = ∑ i ∈ O.selected,
            occurrenceValue (xs.take N) i := by
              apply Finset.sum_congr rfl
              intro i hi
              exact occurrenceValue_ordinaryTakeOccurrenceEmbedding
                xs N hN i
      _ = n • a := ha

theorem ordinaryGMOTargetOutput_nonempty_of_take
    (xs : List A) (N n : ℕ) (hN : N ≤ xs.length)
    (h : Nonempty (OrdinaryGMOTargetOutput (xs.take N) n)) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  obtain ⟨O⟩ := h
  exact ⟨O.ofTake xs N n hN⟩

/-! ## Singleton capped ledger -/

/-- If no value fiber exceeds the cap, the capped occurrence mass is exactly
the full labelled source length. -/
theorem cappedFiberMass_eq_length_of_forall_fiber_card_le
    (xs : List A) (r : ℕ)
    (hcap : ∀ a : A, (occurrenceFiber xs a).card ≤ r) :
    cappedFiberMass xs r = xs.length := by
  classical
  rw [← rawDgmCappedMultiplicitySum_ordinaryOccurrenceSetpartition]
  unfold rawDgmCappedMultiplicitySum
  simp_rw [rawLayerMultiplicity_ordinaryOccurrenceSetpartition,
    min_eq_right (hcap _)]
  have htotal :=
    sum_rawLayerMultiplicity (ordinaryOccurrenceSetpartition xs)
  simp_rw [rawLayerMultiplicity_ordinaryOccurrenceSetpartition] at htotal
  have hcardSum :
      ((ordinaryOccurrenceSetpartition xs).map Finset.card).sum =
        xs.length := by
    clear hcap htotal
    induction xs with
    | nil => simp [ordinaryOccurrenceSetpartition_nil]
    | cons x xs ih =>
        rw [ordinaryOccurrenceSetpartition_cons]
        simpa [ih, Nat.add_comm]
  exact htotal.trans hcardSum

/-! ## Stabilizer endpoints -/

/-- A nonempty ordinary exact spectrum with top stabilizer is full. -/
theorem ordinarySpectrumFull_of_stabilizer_eq_top
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (htop : ordinarySpectrumStabilizer xs n = ⊤) :
    OrdinarySpectrumFull xs n := by
  by_contra hnot
  have hstrict :=
    ordinarySpectrumStabilizer_strict_of_not_full xs n hn hnot
  exact (ne_of_lt hstrict) htop

/-- Pull a prescribed target back from the quotient by the stabilizer of the
complementary spectrum.  If the pulled-back sum is `s` and its desired
ambient representative is `n • a`, the error
`delta = s - n • a` lies in the stabilizer.  Translating by `-delta`,
not by `delta`, produces the genuine target. -/
theorem ordinaryGMOTargetOutput_nonempty_of_quotient_complementStabilizer
    (xs : List A) (n r : ℕ) (L : AddSubgroup A)
    (hlen : xs.length = n + r)
    (hL : L = ordinarySpectrumStabilizer xs r)
    (hout : Nonempty (OrdinaryGMOTargetOutput
      (xs.map (QuotientAddGroup.mk' L)) n)) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  classical
  let q : A →+ A ⧸ L := QuotientAddGroup.mk' L
  obtain ⟨OQ⟩ := hout
  obtain ⟨betaQ, hbetaQ⟩ := OQ.sum_mem_target
  have hquotientMem :
      n • betaQ ∈ ordinaryExactSpectrum (xs.map q) n := by
    apply (mem_ordinaryExactSpectrum_iff (xs.map q) n _).2
    exact ⟨OQ.selected, OQ.card_selected, hbetaQ⟩
  obtain ⟨I, hIcard, hImap⟩ :=
    exists_pullback_selection_of_mem_ordinaryExactSpectrum_map
      q xs n hquotientMem
  obtain ⟨beta, hbeta⟩ :=
    QuotientAddGroup.mk'_surjective L betaQ
  let s : A := ∑ i ∈ I, occurrenceValue xs i
  let delta : A := s - n • beta
  have hdeltaQuotient : q delta = 0 := by
    dsimp only [delta]
    rw [map_sub, map_nsmul, hbeta, hImap]
    simp
  have hdeltaL : delta ∈ L :=
    (QuotientAddGroup.eq_zero_iff delta).1 hdeltaQuotient
  have hsumMem : s ∈ ordinaryExactSpectrum xs n := by
    apply (mem_ordinaryExactSpectrum_iff xs n s).2
    exact ⟨I, hIcard, rfl⟩
  have hnle : n ≤ xs.length := by omega
  have hSpectrumNonempty :=
    ordinaryExactSpectrum_nonempty xs n hnle
  have hstabilizer :
      ordinarySpectrumStabilizer xs n = L := by
    exact (ordinarySpectrumStabilizer_complement hlen).trans hL.symm
  have hnegDelta :
      -delta ∈ ordinarySpectrumStabilizer xs n := by
    rw [hstabilizer]
    exact L.neg_mem hdeltaL
  have hnegDeltaFin :
      -delta ∈ (ordinaryExactSpectrum xs n).addStab := by
    rw [← Finset.mem_coe,
      Finset.coe_addStab hSpectrumNonempty]
    exact hnegDelta
  have htranslate :=
    (Finset.mem_addStab hSpectrumNonempty).1 hnegDeltaFin
  have hvadd :
      (-delta) +ᵥ s ∈
        (-delta) +ᵥ ordinaryExactSpectrum xs n :=
    Finset.vadd_mem_vadd_finset hsumMem
  rw [htranslate] at hvadd
  have hcancel : -delta + s = n • beta := by
    dsimp only [delta]
    abel
  have htargetMem :
      n • beta ∈ ordinaryExactSpectrum xs n := by
    simpa [vadd_eq_add, hcancel] using hvadd
  obtain ⟨J, hJcard, hJsum⟩ :=
    (mem_ordinaryExactSpectrum_iff xs n (n • beta)).1 htargetMem
  exact ⟨{
    selected := J
    card_selected := hJcard
    sum_mem_target := ⟨beta, hJsum⟩
  }⟩

/-! ## Canonical target statement -/

/-- The ordinary prescribed-target endpoint at canonical Davenport width.
This statement is intentionally valid for every finite additive commutative
group; no p-group hypothesis is required by the DGM recursion. -/
def OrdinaryGMOCanonicalTargetStatement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (n : ℕ),
    Nat.card A ≤ n →
    n + pGroupDStar A ≤ xs.length →
    Nonempty (OrdinaryGMOTargetOutput xs n)

/-- DGM and strict quotient-cardinality induction prove the canonical target
statement for every finite additive commutative group. -/
theorem ordinaryGMOTargetOutput_nonempty_of_canonicalDStar
    (A : Type u) [AddCommGroup A] [Fintype A]
    (xs : List A) (n : ℕ)
    (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  classical
  let dA : ℕ := pGroupDStar A
  let N : ℕ := n + dA
  have hN : N ≤ xs.length := by
    simpa [N, dA] using hlen
  let ys : List A := xs.take N
  have hysLength : ys.length = n + dA := by
    simp [ys, N, List.length_take, Nat.min_eq_left hN]
  have hprefix : Nonempty (OrdinaryGMOTargetOutput ys n) := by
    by_cases hhigh : ∃ a : A, dA < (occurrenceFiber ys a).card
    · obtain ⟨a, ha⟩ := hhigh
      exact ordinaryGMOTargetOutput_nonempty_of_excess_occurrenceFiber
        ys a n (by simpa [dA] using ha) hnA (by
          simpa [dA] using (show n + dA ≤ ys.length by omega))
    · have hcap : ∀ a : A, (occurrenceFiber ys a).card ≤ dA := by
        intro a
        have hnot : ¬dA < (occurrenceFiber ys a).card := by
          intro ha
          exact hhigh ⟨a, ha⟩
        omega
      have hnpos : 0 < n :=
        Nat.lt_of_lt_of_le Nat.card_pos hnA
      have hyspos : 0 < ys.length := by omega
      let i : Occurrence ys := ⟨0, hyspos⟩
      have hiFiber :
          i ∈ occurrenceFiber ys (occurrenceValue ys i) := by
        simp [occurrenceFiber]
      have hdApos : 1 ≤ dA := by
        have hone : 1 ≤
            (occurrenceFiber ys (occurrenceValue ys i)).card :=
          Finset.card_pos.mpr ⟨i, hiFiber⟩
        exact hone.trans (hcap _)
      have hdAle : dA ≤ ys.length := by omega
      have hDGM :=
        dgmSetpartitionBound_ordinaryOccurrenceSetpartition
          (finiteDGMSetpartitionInput_of_doubleInduction A)
          ys dA hdApos hdAle
      unfold OrdinaryOccurrenceDGMSetpartitionBound at hDGM
      unfold DGMSetpartitionBound at hDGM
      dsimp only at hDGM
      rw [layerSubsumSpectrum_ordinaryOccurrenceSetpartition] at hDGM
      let L : AddSubgroup A := ordinarySpectrumStabilizer ys dA
      by_cases hLbot : L = ⊥
      · have hstabBot : AddAction.stabilizer A
            (ordinaryExactSpectrum ys dA : Set A) = ⊥ := by
          simpa [L, ordinarySpectrumStabilizer] using hLbot
        have hstabRaw :=
          stabilizerDgmCappedMultiplicitySum_ordinary_eq_raw_of_stabilizer_eq_bot
            ys dA hdAle hstabBot
        have hmass :=
          cappedFiberMass_eq_length_of_forall_fiber_card_le ys dA hcap
        rw [hstabRaw,
          rawDgmCappedMultiplicitySum_ordinaryOccurrenceSetpartition,
          hmass] at hDGM
        have hTnonempty :=
          ordinaryExactSpectrum_nonempty ys dA hdAle
        have hstabCard :
            (ordinaryExactSpectrum ys dA).addStab.card = 1 := by
          rw [card_addStab_eq_natCard_stabilizer _ hTnonempty,
            hstabBot]
          exact AddSubgroup.card_bot
        rw [hstabCard, Nat.mul_one] at hDGM
        have hTcardLe :
            (ordinaryExactSpectrum ys dA).card ≤ Nat.card A := by
          have hle := Finset.card_le_card
            (Finset.subset_univ (ordinaryExactSpectrum ys dA))
          simpa [Nat.card_eq_fintype_card] using hle
        omega
      · by_cases hLtop : L = ⊤
        · have hfull : OrdinarySpectrumFull ys dA :=
            ordinarySpectrumFull_of_stabilizer_eq_top ys dA hdAle
              (by simpa [L] using hLtop)
          exact ordinaryGMOTargetOutput_nonempty_of_complement_spectrumFull
            hysLength hfull
        · let q : A →+ A ⧸ L := QuotientAddGroup.mk' L
          letI : Fintype (A ⧸ L) := Fintype.ofFinite (A ⧸ L)
          have hdQle : pGroupDStar (A ⧸ L) ≤ dA := by
            have hconv := pGroupDStar_subgroup_quotient_le L
            omega
          have hquotientCardLeA : Nat.card (A ⧸ L) ≤ Nat.card A :=
            Nat.le_of_dvd Nat.card_pos L.card_quotient_dvd_card
          have hquotientCardLeN : Nat.card (A ⧸ L) ≤ n :=
            hquotientCardLeA.trans hnA
          have hquotientLength :
              n + pGroupDStar (A ⧸ L) ≤ (ys.map q).length := by
            simp only [List.length_map]
            omega
          have houtQ :=
            ordinaryGMOTargetOutput_nonempty_of_canonicalDStar
              (A ⧸ L) (ys.map q) n hquotientCardLeN hquotientLength
          exact
            ordinaryGMOTargetOutput_nonempty_of_quotient_complementStabilizer
              ys n dA L hysLength rfl (by simpa [q] using houtQ)
  exact ordinaryGMOTargetOutput_nonempty_of_take xs N n hN (by
    simpa [ys] using hprefix)
termination_by Nat.card A
decreasing_by
  exact natCard_quotient_lt_of_addSubgroup_ne_bot L hLbot

/-- The canonical target statement is discharged rather than accepted as an
input. -/
theorem ordinaryGMOCanonicalTargetStatement
    (A : Type u) [AddCommGroup A] [Fintype A] :
    OrdinaryGMOCanonicalTargetStatement A := by
  intro xs n hnA hlen
  exact ordinaryGMOTargetOutput_nonempty_of_canonicalDStar
    A xs n hnA hlen

/-- Source-shaped odd-prime p-group wrapper needed by the thirteen-page
specialization.  The proof deliberately forgets the additional p-group data:
the target endpoint above is valid for every finite commutative group. -/
def OrdinaryGMOPGroupTargetStatement
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (p : ℕ), Fact p.Prime → p ≠ 2 →
    IsPGroup p (Multiplicative A) →
    OrdinaryGMOCanonicalTargetStatement A

theorem ordinaryGMOPGroupTargetStatement
    (A : Type u) [AddCommGroup A] [Fintype A] :
    OrdinaryGMOPGroupTargetStatement A := by
  intro _p _hp _hpTwo _hA
  exact ordinaryGMOCanonicalTargetStatement A

end GaoLean

#print axioms GaoLean.OrdinaryGMOTargetOutput.ofTake
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_take
#print axioms GaoLean.cappedFiberMass_eq_length_of_forall_fiber_card_le
#print axioms GaoLean.ordinarySpectrumFull_of_stabilizer_eq_top
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_quotient_complementStabilizer
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_canonicalDStar
#print axioms GaoLean.ordinaryGMOCanonicalTargetStatement
#print axioms GaoLean.ordinaryGMOPGroupTargetStatement
