import GaoLean.PGGeneralWeightedQuotient

/-!
# Lifting the general weighted target from a stabilizer quotient

If the exact weighted spectrum in the quotient meets `n • (A/L)`, then the
ambient spectrum meets `n • A` whenever `L` is its stabilizer.  The proof
uses exact spectrum transport and stabilizer translation; it makes no
assumption on the shape or cardinality of the weight set.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

theorem weightedGMOExistenceConclusion_of_stabilizerQuotient
    {W : Set ℤ} (hW : W.Nonempty)
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (L : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (hL : L = weightedSpectrumStabilizer W xs n)
    (hQ : WeightedGMOExistenceConclusion W
      (xs.map (QuotientAddGroup.mk' L)) n) :
    WeightedGMOExistenceConclusion W xs n := by
  classical
  obtain ⟨q0, hq0⟩ := hQ
  have hqmem : n • q0 ∈ weightedExactSpectrum W
      (xs.map (QuotientAddGroup.mk' L)) n :=
    (mem_weightedExactSpectrum_iff W _ n _).2 hq0
  rw [← image_weightedExactSpectrum_quotient W xs n L] at hqmem
  obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp hqmem
  let z : A := quotientAddSection L q0
  have hqz : QuotientAddGroup.mk' L z = q0 := by
    simpa [z] using quotientAddSection_mk L q0
  have hdiffL : n • z - y ∈ L := by
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    calc
      QuotientAddGroup.mk' L (n • z) =
          n • QuotientAddGroup.mk' L z := by rw [map_nsmul]
      _ = n • q0 := by rw [hqz]
      _ = QuotientAddGroup.mk' L y := hyq.symm
  let S := weightedExactSpectrum W xs n
  have hSnonempty : S.Nonempty := by
    simpa [S] using weightedExactSpectrum_nonempty hW xs n hn
  have hdiffStab : n • z - y ∈ AddAction.stabilizer A (S : Set A) := by
    simpa [S, hL, weightedSpectrumStabilizer] using hdiffL
  have hdiffFin : n • z - y ∈ S.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hSnonempty]
    exact hdiffStab
  have htranslate := (Finset.mem_addStab hSnonempty).mp hdiffFin
  have htarget : n • z ∈ S := by
    have hv : (n • z - y) +ᵥ y ∈ (n • z - y) +ᵥ S :=
      Finset.vadd_mem_vadd_finset (by simpa [S] using hy)
    rw [htranslate] at hv
    simpa [vadd_eq_add] using hv
  exact ⟨z, (mem_weightedExactSpectrum_iff W xs n (n • z)).1
    (by simpa [S] using htarget)⟩

end GaoLean

#print axioms GaoLean.weightedGMOExistenceConclusion_of_stabilizerQuotient
