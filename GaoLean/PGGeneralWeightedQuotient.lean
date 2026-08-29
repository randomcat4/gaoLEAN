import GaoLean.PGGeneralWeightedDGMBridge

/-!
# Homomorphic and stabilizer-quotient transport for general weights

All statements keep the integer weight set unchanged.  Only source values
and weighted sums are mapped, so the results apply equally to finite and
infinite `W : Set ℤ`.
-/

namespace GaoLean

open scoped Pointwise

universe u v

variable {A : Type u} {B : Type v}
  [AddCommGroup A] [Fintype A]
  [AddCommGroup B] [Fintype B]

/-- A weighted value block commutes with every additive homomorphism. -/
theorem image_weightedValueBlock_addMonoidHom
    [DecidableEq B]
    (W : Set ℤ) (f : A →+ B) (x : A) :
    (weightedValueBlock W x).image f = weightedValueBlock W (f x) := by
  classical
  ext y
  simp only [Finset.mem_image, mem_weightedValueBlock_iff]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w • x, ⟨w, hw, rfl⟩, by simp⟩

/-- Mapping every literal weighted occurrence layer is the literal weighted
occurrence setpartition of the mapped source list. -/
theorem map_weightedOccurrenceSetpartition_addMonoidHom
    [DecidableEq B]
    (W : Set ℤ) (f : A →+ B) (xs : List A) :
    (weightedOccurrenceSetpartition W xs).map (fun C ↦ C.image f) =
      weightedOccurrenceSetpartition W (xs.map f) := by
  classical
  induction xs with
  | nil => simp [weightedOccurrenceSetpartition]
  | cons x xs ih =>
      simp [weightedOccurrenceSetpartition,
        image_weightedValueBlock_addMonoidHom]

/-- Exact occurrence-labelled weighted spectra commute with additive
homomorphisms. -/
theorem image_weightedExactSpectrum_addMonoidHom
    [DecidableEq B]
    (W : Set ℤ) (f : A →+ B) (xs : List A) (n : ℕ) :
    (weightedExactSpectrum W xs n).image f =
      weightedExactSpectrum W (xs.map f) n := by
  classical
  rw [weightedExactSpectrum_eq_layerSubsumSpectrum,
    weightedExactSpectrum_eq_layerSubsumSpectrum,
    image_layerSubsumSpectrum,
    map_weightedOccurrenceSetpartition_addMonoidHom]

/-- Quotient specialization of exact weighted-spectrum transport. -/
theorem image_weightedExactSpectrum_quotient
    (W : Set ℤ) (xs : List A) (n : ℕ) (K : AddSubgroup A)
    [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] :
    (weightedExactSpectrum W xs n).image (QuotientAddGroup.mk' K) =
      weightedExactSpectrum W (xs.map (QuotientAddGroup.mk' K)) n :=
  image_weightedExactSpectrum_addMonoidHom
    W (QuotientAddGroup.mk' K) xs n

/-- The stabilizer of the exact general weighted spectrum. -/
noncomputable def weightedSpectrumStabilizer
    (W : Set ℤ) (xs : List A) (n : ℕ) : AddSubgroup A :=
  AddAction.stabilizer A (weightedExactSpectrum W xs n : Set A)

/-- A nonempty non-full exact weighted spectrum has a proper stabilizer. -/
theorem weightedSpectrumStabilizer_strict_of_not_full
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : n ≤ xs.length)
    (hnot : weightedExactSpectrum W xs n ≠ Finset.univ) :
    weightedSpectrumStabilizer W xs n < ⊤ := by
  simpa [weightedSpectrumStabilizer] using
    stabilizer_lt_top_of_finset_nonempty_ne_univ
      (weightedExactSpectrum W xs n)
      (weightedExactSpectrum_nonempty hW xs n hn)
      hnot

/-- The full-stabilizer branch is the full ambient spectrum. -/
theorem weightedExactSpectrum_eq_univ_of_stabilizer_eq_top
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : n ≤ xs.length)
    (htop : weightedSpectrumStabilizer W xs n = ⊤) :
    weightedExactSpectrum W xs n = Finset.univ := by
  by_contra hnot
  exact (ne_of_lt
    (weightedSpectrumStabilizer_strict_of_not_full hW xs n hn hnot)) htop

/-- If the exact weighted spectrum is full after quotienting by its ambient
stabilizer, then stabilizer invariance lifts fullness back to the ambient
group. -/
theorem weightedExactSpectrum_eq_univ_of_stabilizerQuotient_full
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : n ≤ xs.length) (L : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (hL : L = weightedSpectrumStabilizer W xs n)
    (hquot : weightedExactSpectrum W
      (xs.map (QuotientAddGroup.mk' L)) n = Finset.univ) :
    weightedExactSpectrum W xs n = Finset.univ := by
  classical
  let S := weightedExactSpectrum W xs n
  have hS : S.Nonempty := by
    simpa [S] using weightedExactSpectrum_nonempty hW xs n hn
  have hLstab : L ≤ AddAction.stabilizer A (S : Set A) := by
    simpa [S, hL, weightedSpectrumStabilizer]
  rw [Finset.eq_univ_iff_forall]
  intro y
  have hqy : QuotientAddGroup.mk' L y ∈
      S.image (QuotientAddGroup.mk' L) := by
    rw [show S.image (QuotientAddGroup.mk' L) =
        weightedExactSpectrum W
          (xs.map (QuotientAddGroup.mk' L)) n by
      simpa [S] using image_weightedExactSpectrum_quotient W xs n L,
      hquot]
    simp
  obtain ⟨x, hx, hqxy⟩ := Finset.mem_image.mp hqy
  have hyxL : y - x ∈ L := by
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    exact hqxy.symm
  have hyxStab : y - x ∈ AddAction.stabilizer A (S : Set A) :=
    hLstab hyxL
  have hyxFin : y - x ∈ S.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hS]
    exact hyxStab
  have htranslate := (Finset.mem_addStab hS).mp hyxFin
  have hy : (y - x) +ᵥ x ∈ (y - x) +ᵥ S :=
    Finset.vadd_mem_vadd_finset hx
  rw [htranslate] at hy
  simpa only [S, vadd_eq_add, sub_add_cancel] using hy

/-- After quotienting the weighted occurrence layers by the stabilizer of
their exact layer spectrum, the quotient layer spectrum is aperiodic. -/
theorem addStab_quotient_weightedOccurrenceSpectrum_eq_singleton
    [DecidableEq A]
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : n ≤ xs.length) :
    let P := weightedOccurrenceSetpartition W xs
    let T := layerSubsumSpectrum P n
    let H := AddAction.stabilizer A (T : Set A)
    let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
    (layerSubsumSpectrum (P.map fun C ↦ C.image q) n).addStab = {0} := by
  classical
  exact addStab_layerSubsumSpectrum_stabilizerQuotient_eq_singleton
    (weightedOccurrenceSetpartition W xs)
    (weightedOccurrenceSetpartition_isNonempty hW xs)
    n (by simpa using hn)

end GaoLean

#print axioms GaoLean.image_weightedValueBlock_addMonoidHom
#print axioms GaoLean.map_weightedOccurrenceSetpartition_addMonoidHom
#print axioms GaoLean.image_weightedExactSpectrum_addMonoidHom
#print axioms GaoLean.image_weightedExactSpectrum_quotient
#print axioms GaoLean.weightedSpectrumStabilizer_strict_of_not_full
#print axioms GaoLean.weightedExactSpectrum_eq_univ_of_stabilizer_eq_top
#print axioms GaoLean.weightedExactSpectrum_eq_univ_of_stabilizerQuotient_full
#print axioms GaoLean.addStab_quotient_weightedOccurrenceSpectrum_eq_singleton
