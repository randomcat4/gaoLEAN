import GaoLean.PGGMOClaimBQuotientFullLift
import GaoLean.PGGMOClaimBQuotientLargeNonfull

/-!
# Honest recursive data for the padded Claim-B quotient

This module packages only the conditions that follow from the genuine
quotient ledger.  The proper parent branch is explicit: it makes the quotient
nontrivial and hence makes its canonical `d*` positive.

The large-alternative width inequality is deliberately absent.  After the
exact seed-cardinality rewrite it is `|A/K| ≤ e + 1`, which is independent
of the source-length identities below.  The recursive driver must therefore
split full, large-nonfull, and periodic/concentration outcomes rather than
silently assuming that inequality.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance quotientRecursiveInputFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- Exact decomposition of the padded source length into its genuine seed
and the artificial zero suffix. -/
theorem OrdinaryGMOClaimBOutput.length_paddedQuotientRValues_eq_seed_add
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).length =
      (W.paddedQuotientRSeed hzero).card +
        (Nat.card (A ⧸ W.K) - 1) := by
  rw [W.length_paddedQuotientRValues hzero,
    W.card_paddedQuotientRSeed hzero]

/-- Equivalently, removing the genuine seed leaves exactly `|A/K|-1`
artificial positions. -/
theorem OrdinaryGMOClaimBOutput.length_paddedQuotientRValues_sub_seed
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).length -
        (W.paddedQuotientRSeed hzero).card =
      Nat.card (A ⧸ W.K) - 1 := by
  rw [W.length_paddedQuotientRValues_eq_seed_add hzero]
  omega

/-- The exact rewrite exposing why the large-branch width is not a
consequence of padding: it asks for `|A/K| ≤ e+1`, not for a source-length
bound. -/
theorem OrdinaryGMOClaimBOutput.paddedQuotientR_largeWidth_iff
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card) :
    Nat.card (A ⧸ W.K) ≤
        (W.paddedQuotientRSeed hzero).card -
            pGroupDStar (A ⧸ W.K) + 1 ↔
      Nat.card (A ⧸ W.K) ≤ W.quotientRExceptionCount + 1 := by
  rw [W.card_paddedQuotientRSeed hzero]
  omega

/-- All genuinely inherited data needed before directly recursing on the
padded quotient source. -/
structure OrdinaryGMOClaimBQuotientRecursiveInput
    (p : ℕ) {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) : Prop where
  prime : p.Prime
  oddPrime : p ≠ 2
  quotientPGroup : IsPGroup p (Multiplicative (A ⧸ W.K))
  quotientCardLt : Nat.card (A ⧸ W.K) < Nat.card A
  dQPos : 1 ≤ pGroupDStar (A ⧸ W.K)
  zeroCapacity :
    pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card
  seedCardLower :
    pGroupDStar (A ⧸ W.K) ≤
      (W.paddedQuotientRSeed zeroCapacity).card
  seedMultiplicity :
    SelectionMultiplicityAtMost
      (W.paddedQuotientRValues zeroCapacity)
      (W.paddedQuotientRSeed zeroCapacity)
      (pGroupDStar (A ⧸ W.K))
  theoremEInput : Nonempty
    (GMOTheoremEInput
      (W.paddedQuotientRValues zeroCapacity)
      (W.paddedQuotientRSeed zeroCapacity)
      (pGroupDStar (A ⧸ W.K)))
  sourceWide :
    Nat.card (A ⧸ W.K) ≤
      (W.paddedQuotientRValues zeroCapacity).length
  recursiveSourceLength :
    pGroupDStar (A ⧸ W.K) + Nat.card (A ⧸ W.K) - 1 ≤
      (W.paddedQuotientRValues zeroCapacity).length
  liftBudget :
    pGroupDStar W.K + pGroupDStar (A ⧸ W.K) ≤ n

/-- The proper Claim-B branch and the low quotient-multiplicity ledger
construct every field of the honest recursive package. -/
theorem OrdinaryGMOClaimBOutput.nonempty_quotientRecursiveInput
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hproper : W.K < ⊤)
    (hambient : pGroupDStar A ≤ n)
    (hzero : pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card)
    (hlow : ∀ z : A ⧸ W.K, z ≠ 0 →
      (W.quotientFiber z).card ≤ pGroupDStar (A ⧸ W.K)) :
    Nonempty (OrdinaryGMOClaimBQuotientRecursiveInput p W) := by
  let dQ : ℕ := pGroupDStar (A ⧸ W.K)
  letI : Nontrivial (A ⧸ W.K) :=
    W.nontrivial_quotient_of_ne_top (ne_of_lt hproper)
  have hdQPos : 1 ≤ dQ := by
    dsimp [dQ]
    have hgt := one_lt_ordinaryDavenportValue (B := A ⧸ W.K)
    have hrecover := pGroupDStar_add_one (A ⧸ W.K)
    omega
  have hseedLower : dQ ≤ (W.paddedQuotientRSeed hzero).card :=
    W.dQ_le_card_paddedQuotientRSeed hzero
  have hmultiplicity : SelectionMultiplicityAtMost
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) dQ :=
    W.paddedQuotientRSeed_multiplicityAtMost hzero hlow
  have hinput : Nonempty
      (GMOTheoremEInput
        (W.paddedQuotientRValues hzero)
        (W.paddedQuotientRSeed hzero) dQ) :=
    W.nonempty_gmoTheoremEInput_paddedQuotientR hzero hlow
  have hqPos : 0 < Nat.card (A ⧸ W.K) := Nat.card_pos
  have hsourceWide : Nat.card (A ⧸ W.K) ≤
      (W.paddedQuotientRValues hzero).length := by
    rw [W.length_paddedQuotientRValues hzero]
    omega
  have hrecursiveLength :
      dQ + Nat.card (A ⧸ W.K) - 1 ≤
        (W.paddedQuotientRValues hzero).length := by
    rw [W.length_paddedQuotientRValues hzero]
    omega
  have hliftBudget : pGroupDStar W.K + dQ ≤ n := by
    have hconv := pGroupDStar_subgroup_quotient_le W.K
    dsimp [dQ]
    exact hconv.trans hambient
  refine ⟨{
    prime := hp
    oddPrime := hpTwo
    quotientPGroup := isPGroup_multiplicative_quotient p hA W.K
    quotientCardLt := W.natCard_quotient_lt
    dQPos := hdQPos
    zeroCapacity := hzero
    seedCardLower := ?_
    seedMultiplicity := ?_
    theoremEInput := ?_
    sourceWide := ?_
    recursiveSourceLength := ?_
    liftBudget := ?_
  }⟩
  · simpa [dQ] using hseedLower
  · simpa [dQ] using hmultiplicity
  · simpa [dQ] using hinput
  · exact hsourceWide
  · simpa [dQ] using hrecursiveLength
  · simpa [dQ] using hliftBudget

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.length_paddedQuotientRValues_eq_seed_add
#print axioms GaoLean.OrdinaryGMOClaimBOutput.paddedQuotientR_largeWidth_iff
#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_quotientRecursiveInput
