import GaoLean.PGGMOClaimBFixedCarrierDriver

/-!
# Widening an occurrence-faithful fixed carrier

A fixed-carrier full spectrum remains valid after adding genuine source
occurrences to its carrier.  This module chooses exactly enough occurrences
from the literal complement of the old carrier, preserving both the exact
carrier cardinality and every old exact-spectrum witness.

When the widened carrier has cardinality `target + r`, the existing literal
carrier-complement theorem converts its full exact-`r` spectrum into a full
exact-`target` spectrum.  The final wrappers apply this bookkeeping to the
full branch of the honest Claim-B driver while retaining concentration
unchanged.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Enlarge a fixed occurrence carrier from cardinality `s` to any
`m ∈ [s, xs.length]`.  Every old exact-`r` witness is retained literally. -/
theorem OrdinaryFixedCarrierSpectrumFull.nonempty_widen
    {xs : List A} {s r m : ℕ}
    (F : OrdinaryFixedCarrierSpectrumFull xs s r)
    (hsm : s ≤ m) (hmSource : m ≤ xs.length) :
    Nonempty (OrdinaryFixedCarrierSpectrumFull xs m r) := by
  classical
  let available : Selection xs := Finset.univ \ F.carrier
  have havailableCard : available.card = xs.length - s := by
    dsimp only [available]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ F.carrier),
      F.card_carrier]
    simp
  have hfillLe : m - s ≤ available.card := by
    rw [havailableCard]
    omega
  obtain ⟨extra, hextraSub, hextraCard⟩ :=
    Finset.exists_subset_card_eq (s := available) hfillLe
  have hdisjoint : Disjoint F.carrier extra := by
    rw [Finset.disjoint_left]
    intro i hiCarrier hiExtra
    have hiAvailable := hextraSub hiExtra
    have hiNotCarrier : i ∉ F.carrier := by
      exact (Finset.mem_sdiff.mp (by
        simpa only [available] using hiAvailable)).2
    exact hiNotCarrier hiCarrier
  refine ⟨{
    carrier := F.carrier ∪ extra
    card_carrier := ?_
    spectrumFull := ?_
  }⟩
  · rw [Finset.card_union_of_disjoint hdisjoint,
      F.card_carrier, hextraCard]
    omega
  · intro y
    obtain ⟨I, hIsub, hIcard, hIsum⟩ := F.spectrumFull y
    exact ⟨I, hIsub.trans Finset.subset_union_left, hIcard, hIsum⟩

/-- Widen the common carrier to the complementary cardinality
`target + r`, then take the literal carrier complement. -/
theorem OrdinaryFixedCarrierSpectrumFull.ordinarySpectrumFull_complement_after_widen
    {xs : List A} {s r target : ℕ}
    (F : OrdinaryFixedCarrierSpectrumFull xs s r)
    (hs : s ≤ target + r) (hsource : target + r ≤ xs.length) :
    OrdinarySpectrumFull xs target := by
  obtain ⟨Fwide⟩ := F.nonempty_widen hs hsource
  exact Fwide.ordinarySpectrumFull_complement rfl

/-- Canonical `d*(A)` specialization of carrier widening followed by
complementation. -/
theorem OrdinaryFixedCarrierSpectrumFull.ordinarySpectrumFull_complement_after_widen_dStar
    {xs : List A} {s target : ℕ}
    (F : OrdinaryFixedCarrierSpectrumFull xs s (pGroupDStar A))
    (hs : s ≤ target + pGroupDStar A)
    (hsource : target + pGroupDStar A ≤ xs.length) :
    OrdinarySpectrumFull xs target :=
  F.ordinarySpectrumFull_complement_after_widen hs hsource

/-- Run the existing Claim-B fixed-carrier driver at an exact weight `r`.
Its full branch widens the retained carrier to `target + r` and complements;
its concentration branch is retained unchanged. -/
theorem OrdinaryGMOClaimBOutput.ordinarySpectrumFull_or_concentration_of_carrier_widen
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {seed : Selection xs} {r target : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed r)
    (hambient : pGroupDStar A ≤ r)
    (hseed : seed.card ≤ target + r)
    (hsource : target + r ≤ xs.length) :
    OrdinarySpectrumFull xs target ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  rcases W.nonempty_fixedCarrierSpectrumFull_or_concentration
      p hp hpTwo hA hambient with hfixed | hconcentration
  · obtain ⟨F⟩ := hfixed
    exact Or.inl
      (F.ordinarySpectrumFull_complement_after_widen hseed hsource)
  · exact Or.inr hconcentration

/-- At the canonical recursive weight `r = d*(A)`, only the source-capacity
ledger `seed.card ≤ target + d*(A) ≤ xs.length` is needed. -/
theorem OrdinaryGMOClaimBOutput.ordinarySpectrumFull_or_concentration_of_carrier_widen_dStar
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {seed : Selection xs} {target : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed (pGroupDStar A))
    (hseed : seed.card ≤ target + pGroupDStar A)
    (hsource : target + pGroupDStar A ≤ xs.length) :
    OrdinarySpectrumFull xs target ∨
      Nonempty (OrdinaryGMOConcentration xs) :=
  W.ordinarySpectrumFull_or_concentration_of_carrier_widen
    p hp hpTwo hA le_rfl hseed hsource

#print axioms GaoLean.OrdinaryFixedCarrierSpectrumFull.nonempty_widen
#print axioms GaoLean.OrdinaryFixedCarrierSpectrumFull.ordinarySpectrumFull_complement_after_widen
#print axioms GaoLean.OrdinaryFixedCarrierSpectrumFull.ordinarySpectrumFull_complement_after_widen_dStar
#print axioms GaoLean.OrdinaryGMOClaimBOutput.ordinarySpectrumFull_or_concentration_of_carrier_widen
#print axioms GaoLean.OrdinaryGMOClaimBOutput.ordinarySpectrumFull_or_concentration_of_carrier_widen_dStar

end GaoLean
