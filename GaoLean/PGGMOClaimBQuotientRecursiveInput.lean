import GaoLean.PGGMOClaimBQuotientFullLift
import GaoLean.PGGMOClaimBQuotientLargeNonfull

/-!
# Honest recursive data for the padded Claim-B quotient

This module packages only the conditions that follow from the genuine
quotient ledger.  The proper parent branch is explicit: it is exactly what
makes the quotient nontrivial and hence makes the padded source strictly
longer than its genuine seed.

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
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).length =
      (W.paddedQuotientRSeed hzero).card +
        (Nat.card (A ⧸ W.K) - 1) := by
  rw [W.length_paddedQuotientRValues hzero,
    W.card_paddedQuotientRSeed hzero]

/-- Equivalently, removing the genuine seed leaves exactly `|A/K|-1`
artificial positions. -/
theorem OrdinaryGMOClaimBOutput.length_paddedQuotientRValues_sub_seed
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    (W.paddedQuotientRValues hzero).length -
        (W.paddedQuotientRSeed hzero).card =
      Nat.card (A ⧸ W.K) - 1 := by
  rw [W.length_paddedQuotientRValues_eq_seed_add hzero]
  omega

/-- The exact rewrite exposing why the large-branch width is not a
consequence of padding: it asks for `|A/K| ≤ e+1`, not for a source-length
bound. -/
theorem OrdinaryGMOClaimBOutput.paddedQuotientR_largeWidth_iff
    {xs : List A} {seed : Selection xs} {n dQ : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hzero : dQ ≤ (W.quotientFiber 0).card) :
    Nat.card (A ⧸ W.K) ≤
        (W.paddedQuotientRSeed hzero).card - dQ + 1 ↔
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
  dQPos : 1 ≤ pGroupDStar W.K
  zeroCapacity :
    pGroupDStar W.K ≤ (W.quotientFiber 0).card
  seedCardLower :
    pGroupDStar W.K ≤
      (W.paddedQuotientRSeed zeroCapacity).card
  seedMultiplicity :
    SelectionMultiplicityAtMost
      (W.paddedQuotientRValues zeroCapacity)
      (W.paddedQuotientRSeed zeroCapacity)
      (pGroupDStar W.K)
  theoremEInput : Nonempty
    (GMOTheoremEInput
      (W.paddedQuotientRValues zeroCapacity)
      (W.paddedQuotientRSeed zeroCapacity)
      (pGroupDStar W.K))
  sourceWide :
    Nat.card (A ⧸ W.K) ≤
      (W.paddedQuotientRValues zeroCapacity).length
  recursiveSourceLength :
    pGroupDStar W.K + Nat.card (A ⧸ W.K) - 1 ≤
      (W.paddedQuotientRValues zeroCapacity).length
  seedStrictSource :
    (W.paddedQuotientRSeed zeroCapacity).card <
      (W.paddedQuotientRValues zeroCapacity).length

/-- The proper Claim-B branch and the low quotient-multiplicity ledger
construct every field of the honest recursive package. -/
theorem OrdinaryGMOClaimBOutput.nonempty_quotientRecursiveInput
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hproper : W.K < ⊤)
    (hzero : pGroupDStar W.K ≤ (W.quotientFiber 0).card)
    (hlow : ∀ z : A ⧸ W.K, z ≠ 0 →
      (W.quotientFiber z).card ≤ pGroupDStar W.K) :
    Nonempty (OrdinaryGMOClaimBQuotientRecursiveInput p W) := by
  let dQ : ℕ := pGroupDStar W.K
  have hdQPos : 1 ≤ dQ := by
    dsimp [dQ]
    exact one_le_pGroupDStar_of_addSubgroup_ne_bot W.K W.nontrivial
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
  have hqTwo : 2 ≤ Nat.card (A ⧸ W.K) :=
    two_le_natCard_quotient_of_lt_top W.K hproper
  have hsourceWide : Nat.card (A ⧸ W.K) ≤
      (W.paddedQuotientRValues hzero).length := by
    rw [W.length_paddedQuotientRValues hzero]
    omega
  have hrecursiveLength :
      dQ + Nat.card (A ⧸ W.K) - 1 ≤
        (W.paddedQuotientRValues hzero).length := by
    rw [W.length_paddedQuotientRValues hzero]
    omega
  have hseedStrict : (W.paddedQuotientRSeed hzero).card <
      (W.paddedQuotientRValues hzero).length := by
    rw [W.length_paddedQuotientRValues_eq_seed_add hzero]
    omega
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
    seedStrictSource := ?_
  }⟩
  · simpa [dQ] using hseedLower
  · simpa [dQ] using hmultiplicity
  · simpa [dQ] using hinput
  · exact hsourceWide
  · simpa [dQ] using hrecursiveLength
  · exact hseedStrict

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.length_paddedQuotientRValues_eq_seed_add
#print axioms GaoLean.OrdinaryGMOClaimBOutput.paddedQuotientR_largeWidth_iff
#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_quotientRecursiveInput
