import GaoLean.PGGMOPGroupStructuralTrichotomy
import GaoLean.PGGMOClaimBQuotientFullLift
import GaoLean.PGGMOClaimBQuotientLargeNonfull
import GaoLean.PGGMOClaimBQuotientConcentration

/-!
# Pulling the honest padded-quotient trichotomy back to the source

This module consumes the three outcomes of the structural quotient theorem
without adding the large-branch width inequality.  A genuinely full quotient
spectrum is lifted by the normalized quotient ledger.  A large partition is
split according to whether the quotient spectrum is actually full; only its
nonfull case is converted to source concentration.  Quotient concentration is
pulled back through the proved third-isomorphism ledger.

No artificial padded occurrence is interpreted as an occurrence of the
original source in this consumer.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- If a replacement partition has full sumset, its occurrence-labelled
exact spectrum is full. -/
theorem Theorem21SetPartition.ordinarySpectrumFull_of_sumset_eq_univ
    {xs : List A} {r m : ℕ} (P : Theorem21SetPartition xs r m)
    (hfull : P.sumset = Finset.univ) :
    OrdinarySpectrumFull xs r := by
  rw [ordinarySpectrumFull_iff_exactSpectrum_eq_univ]
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  apply P.sumset_subset_ordinaryExactSpectrum
  rw [hfull]
  exact Finset.mem_univ y

/-- The honest padded quotient trichotomy lifts to the exact full-spectrum or
source-concentration alternative.  Properness makes the quotient nontrivial,
which supplies positivity of its canonical `d*`. -/
theorem OrdinaryGMOClaimBOutput.full_or_concentration_of_quotientTrichotomy
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hproper : W.K < ⊤)
    (hzero : pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card)
    (hlen : pGroupDStar W.K + pGroupDStar (A ⧸ W.K) ≤ n)
    (htri : OrdinaryGMOStructuralTrichotomy
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) (pGroupDStar (A ⧸ W.K))) :
    OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  letI : Fintype (A ⧸ W.K) := Fintype.ofFinite (A ⧸ W.K)
  letI : Nontrivial (A ⧸ W.K) :=
    W.nontrivial_quotient_of_ne_top (ne_of_lt hproper)
  have hdQpos : 1 ≤ pGroupDStar (A ⧸ W.K) := by
    have hgt := one_lt_ordinaryDavenportValue (B := A ⧸ W.K)
    have hrecover := pGroupDStar_add_one (A ⧸ W.K)
    omega
  rcases htri with hfull | hlarge | hconcentration
  · exact Or.inl
      (W.ordinarySpectrumFull_of_paddedQuotientR
        hzero hdQpos hfull hlen)
  · obtain ⟨Qpartition, Qlarge⟩ := hlarge
    by_cases hquotientFull :
        OrdinarySpectrumFull (W.paddedQuotientRValues hzero)
          (pGroupDStar (A ⧸ W.K))
    · exact Or.inl
        (W.ordinarySpectrumFull_of_paddedQuotientR
          hzero hdQpos hquotientFull hlen)
    · have hsumsetNotFull : Qpartition.sumset ≠ Finset.univ := by
        intro hsumset
        exact hquotientFull
          (Qpartition.ordinarySpectrumFull_of_sumset_eq_univ hsumset)
      exact Or.inr
        (W.nonempty_concentration_of_quotientLarge_nonfull
          hzero hdQpos Qpartition Qlarge hsumsetNotFull)
  · obtain ⟨CQ⟩ := hconcentration
    exact Or.inr
      (W.nonempty_quotientConcentrationPullback hzero hdQpos CQ)

end GaoLean

#print axioms GaoLean.Theorem21SetPartition.ordinarySpectrumFull_of_sumset_eq_univ
#print axioms GaoLean.OrdinaryGMOClaimBOutput.full_or_concentration_of_quotientTrichotomy
