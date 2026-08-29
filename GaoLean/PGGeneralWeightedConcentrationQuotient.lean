import GaoLean.PGGeneralWeightedQuotient

/-!
# Lifting general weighted concentration through a quotient

This is the source-occurrence-faithful structural lift needed in the
nontrivial-stabilizer branch of general weighted GMO.  The lifted subgroup is
the full preimage of the quotient subgroup, while the two quotient coset
centers are lifted independently.  One global `beta` remains shared by every
retained occurrence and every weight in `W`.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

theorem weightedGMOConcentration_of_quotient
    (W : Set ℤ) (xs : List A) (L : AddSubgroup A)
    [Fintype (A ⧸ L)]
    (hQ : WeightedGMOConcentration W
      (xs.map (QuotientAddGroup.mk' L))) :
    Nonempty (WeightedGMOConcentration W xs) := by
  classical
  let q : A →+ A ⧸ L := QuotientAddGroup.mk' L
  let e : Occurrence xs ≃
      Occurrence (xs.map (QuotientAddGroup.mk' L)) :=
    ConcreteGDihedral.mapOccurrenceEquiv (QuotientAddGroup.mk' L) xs
  let K : AddSubgroup A := hQ.K.comap q
  let alpha : A := quotientAddSection L hQ.alpha
  let beta : A := quotientAddSection L hQ.beta
  let selected : Selection xs := hQ.selected.map e.symm.toEmbedding
  have hmapK : K.map q = hQ.K := by
    simpa [K, q] using
      AddSubgroup.map_comap_eq_self_of_surjective
        (QuotientAddGroup.mk'_surjective L) hQ.K
  have hLK : L ≤ K := by
    intro x hx
    change q x ∈ hQ.K
    have hqx : q x = 0 := (QuotientAddGroup.eq_zero_iff x).2 hx
    rw [hqx]
    exact hQ.K.zero_mem
  have hcardQuot :
      Nat.card ((A ⧸ L) ⧸ hQ.K) = Nat.card (A ⧸ K) := by
    have hcard := Nat.card_congr
      (QuotientAddGroup.quotientQuotientEquivQuotient L K hLK).toEquiv
    rw [hmapK] at hcard
    exact hcard
  have hstrictK : K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply (ne_of_lt hQ.strict)
    apply top_unique
    intro z _hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
    have hxK : x ∈ K := by
      rw [htop]
      trivial
    exact hxK
  have hselected_mem
      {i : Occurrence xs} (hi : i ∈ selected) : e i ∈ hQ.selected := by
    obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
    have hje : j = e i := e.symm_apply_eq.mp hji
    simpa [hje] using hj
  have hqalpha : q alpha = hQ.alpha := by
    simpa [q, alpha] using quotientAddSection_mk L hQ.alpha
  have hqbeta : q beta = hQ.beta := by
    simpa [q, beta] using quotientAddSection_mk L hQ.beta
  refine ⟨{
    K := K
    strict := hstrictK
    alpha := alpha
    beta := beta
    selected := selected
    sourceCoset := ?_
    weightCoset := ?_
    card_lower := ?_
  }⟩
  · intro i hi
    have hei := hselected_mem hi
    have hmem := hQ.sourceCoset (e i) hei
    have hvalue :
        occurrenceValue (xs.map (QuotientAddGroup.mk' L)) (e i) =
          q (occurrenceValue xs i) := by
      simpa [e, q] using
        ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
          (QuotientAddGroup.mk' L) xs i
    change q (occurrenceValue xs i - alpha) ∈ hQ.K
    rw [map_sub, hqalpha]
    rw [hvalue] at hmem
    exact hmem
  · intro i hi w hw
    have hei := hselected_mem hi
    have hmem := hQ.weightCoset (e i) hei w hw
    have hvalue :
        occurrenceValue (xs.map (QuotientAddGroup.mk' L)) (e i) =
          q (occurrenceValue xs i) := by
      simpa [e, q] using
        ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
          (QuotientAddGroup.mk' L) xs i
    change q (w • occurrenceValue xs i - beta) ∈ hQ.K
    rw [map_sub, map_zsmul, hqbeta]
    rw [hvalue] at hmem
    exact hmem
  · change xs.length - Nat.card (A ⧸ K) + 2 ≤ selected.card
    have hlenmap :
        (xs.map (QuotientAddGroup.mk' L)).length = xs.length := by simp
    have hselcard : selected.card = hQ.selected.card := by
      simpa [selected]
    calc
      xs.length - Nat.card (A ⧸ K) + 2 =
          (xs.map (QuotientAddGroup.mk' L)).length -
            Nat.card ((A ⧸ L) ⧸ hQ.K) + 2 := by
              rw [hlenmap, hcardQuot]
      _ ≤ hQ.selected.card := hQ.card_lower
      _ = selected.card := hselcard.symm

/-- Complete structural lifting from the exact source alternative on the
stabilizer quotient.  Quotient fullness lifts by stabilizer invariance;
quotient concentration lifts by full preimage of its subgroup. -/
theorem weightedGMOStructuralConclusion_of_stabilizerQuotient
    {W : Set ℤ} (hW : W.Nonempty)
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (L : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (hL : L = weightedSpectrumStabilizer W xs n)
    (hQ : weightedExactSpectrum W
        (xs.map (QuotientAddGroup.mk' L)) n = Finset.univ ∨
      Nonempty (WeightedGMOConcentration W
        (xs.map (QuotientAddGroup.mk' L)))) :
    weightedExactSpectrum W xs n = Finset.univ ∨
      Nonempty (WeightedGMOConcentration W xs) := by
  rcases hQ with hfull | hcon
  · exact Or.inl
      (weightedExactSpectrum_eq_univ_of_stabilizerQuotient_full
        hW xs n hn L hL hfull)
  · obtain ⟨hcon⟩ := hcon
    exact Or.inr (weightedGMOConcentration_of_quotient W xs L hcon)

end GaoLean

#print axioms GaoLean.weightedGMOConcentration_of_quotient
#print axioms GaoLean.weightedGMOStructuralConclusion_of_stabilizerQuotient
