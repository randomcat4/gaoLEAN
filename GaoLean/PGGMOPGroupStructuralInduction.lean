import GaoLean.PGGMOPGroupStructuralTrichotomy
import GaoLean.PGGMOClaimBProperKDispatch
import GaoLean.PGGMOClaimBQuotientTrichotomyLift
import GaoLean.PGGMOClaimBTopSpectrum

/-!
# Well-founded p-group structural induction driver

This module carries out the well-founded recursion for the frozen odd-prime
p-group structural theorem.  The recursive measure is the ambient
cardinality.  In a proper Claim-B branch, the quotient by the genuine
nontrivial subgroup has strictly smaller cardinality.

The recursive target is only `OrdinaryGMOStructuralTrichotomy`: full exact
spectrum, a genuine large-alternative partition, or ordinary source
concentration.  It is not the complete periodic branch of GMO Theorem 2.1.

The proper branch uses the verified plain-witness high-multiplicity
contradiction, the canonical quotient length `dQ = pGroupDStar (A ⧸ W.K)`,
and the honest quotient-trichotomy lift.  No external induction boundary is
used.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The precise goal of the well-founded recursive driver.  Positivity is
needed to run the source-faithful Theorem E.  The canonical Davenport budget
is stable under the quotient recursion, unlike the stronger ambient-cardinal
budget used by earlier nonrecursive Claim-B wrappers. -/
def OrdinaryGMOPGroupStructuralInductionGoal
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ (xs : List A) (seed : Selection xs) (n : ℕ)
      (I : GMOTheoremEInput xs seed n),
      0 < n →
      pGroupDStar A ≤ n →
      Nat.card A ≤ xs.length →
      OrdinaryGMOStructuralTrichotomy xs seed n

/-- The unconditional source-faithful Theorem E supplies the output consumed
by one recursion step. -/
theorem nonempty_gmoTheoremESourceOutput_for_structuralInduction
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (I : GMOTheoremEInput xs seed n) (hn : 0 < n) :
    Nonempty (GMOTheoremESourceOutput I) :=
  gmoTheoremESourceStatement xs seed n I hn

/-- An already obtained genuine large alternative is the middle branch of
the structural trichotomy, with its real partition retained. -/
theorem ordinaryGMOStructuralTrichotomy_of_large
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P : Theorem21SetPartition xs n seed.card)
    (hlarge : GMOTheorem21LargeAlternative xs seed n P) :
    OrdinaryGMOStructuralTrichotomy xs seed n :=
  Or.inr (Or.inl ⟨P, hlarge⟩)

/-- The `N ≤ 1` part of a recursion step is completely closed by the honest
terminal trichotomy. -/
theorem GMOTheoremESourceOutput.structuralTrichotomy_of_count_le_one
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hsourceWide : Nat.card A ≤ xs.length)
    (hN : out.partition.commonCosetCount out.H ≤ 1) :
    OrdinaryGMOStructuralTrichotomy xs seed n :=
  out.structuralTrichotomy_of_terminal hsourceWide hN

/-- Canonical subgroup--quotient budget for the recursive Claim-B branch. -/
theorem OrdinaryGMOClaimBOutput.canonicalQuotient_budget
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hdA : pGroupDStar A ≤ n) :
    pGroupDStar W.K + pGroupDStar (A ⧸ W.K) ≤ n :=
  (pGroupDStar_subgroup_quotient_le W.K).trans hdA

/-- The canonical quotient budget fits inside the genuine zero fiber.  This
uses the retained Claim-B occurrence ledger and no source-padding label. -/
theorem OrdinaryGMOClaimBOutput.canonicalQuotient_zeroCapacity
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hdA : pGroupDStar A ≤ n) :
    pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card := by
  have hbudget := W.canonicalQuotient_budget hdA
  have hzero := W.zeroQuotientFiber_lower
  omega

/-- A top plain Claim-B witness closes the full branch using only the
canonical ambient Davenport budget. -/
theorem OrdinaryGMOClaimBOutput.structuralTrichotomy_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hdA : pGroupDStar A ≤ n)
    (hKtop : W.K = ⊤) :
    OrdinaryGMOStructuralTrichotomy xs seed n := by
  have hrn : pGroupDStar W.K ≤ n := by
    exact (Nat.le_add_right (pGroupDStar W.K)
      (pGroupDStar (A ⧸ W.K))).trans (W.canonicalQuotient_budget hdA)
  exact Or.inl (W.ordinarySpectrumFull_of_K_eq_top hrn hKtop)

/-- The exact well-founded descent used by the quotient call. -/
theorem OrdinaryGMOClaimBOutput.structuralInduction_quotientCard_lt
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    Nat.card (A ⧸ W.K) < Nat.card A :=
  W.natCard_quotient_lt

/-- Genuine well-founded structural recursion for finite odd-prime
`p`-groups.  The recursive call is made only on the quotient by the
nontrivial proper subgroup of a cardinal-maximal plain Claim-B witness. -/
theorem ordinaryGMOPGroupStructuralTrichotomy
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (I : GMOTheoremEInput xs seed n)
    (hn : 0 < n)
    (hambient : pGroupDStar A ≤ n)
    (hsourceWide : Nat.card A ≤ xs.length) :
    OrdinaryGMOStructuralTrichotomy xs seed n := by
  obtain ⟨out⟩ :=
    nonempty_gmoTheoremESourceOutput_for_structuralInduction I hn
  by_cases hterminal : out.partition.commonCosetCount out.H ≤ 1
  · exact out.structuralTrichotomy_of_count_le_one hsourceWide hterminal
  have hN : 2 ≤ out.partition.commonCosetCount out.H := by omega
  by_cases hlarge :
      GMOTheorem21LargeAlternative xs seed n out.partition
  · exact ordinaryGMOStructuralTrichotomy_of_large out.partition hlarge
  obtain ⟨Wmax, hmax⟩ :=
    exists_card_maximal_ordinaryGMOClaimBOutput
      (out.nonempty_ordinaryGMOClaimBOutput_case1
        p hp hpTwo hA hambient hN hlarge)
  by_cases hKtop : Wmax.K = ⊤
  · exact Wmax.structuralTrichotomy_of_K_eq_top hambient hKtop
  have hproper : Wmax.K < ⊤ := lt_top_iff_ne_top.mpr hKtop
  obtain ⟨R⟩ :=
    Wmax.nonempty_quotientRecursiveInput_of_card_maximal
      p hp hpTwo hA hmax hproper hambient
  obtain ⟨IQ⟩ := R.theoremEInput
  letI : Fintype (A ⧸ Wmax.K) := Fintype.ofFinite (A ⧸ Wmax.K)
  have hquotientTrichotomy : OrdinaryGMOStructuralTrichotomy
      (Wmax.paddedQuotientRValues R.zeroCapacity)
      (Wmax.paddedQuotientRSeed R.zeroCapacity)
      (pGroupDStar (A ⧸ Wmax.K)) :=
    ordinaryGMOPGroupStructuralTrichotomy
      (A ⧸ Wmax.K) p hp hpTwo R.quotientPGroup
      (Wmax.paddedQuotientRValues R.zeroCapacity)
      (Wmax.paddedQuotientRSeed R.zeroCapacity)
      (pGroupDStar (A ⧸ Wmax.K)) IQ R.dQPos le_rfl R.sourceWide
  have hparent :=
    Wmax.full_or_concentration_of_quotientTrichotomy
      hproper R.zeroCapacity R.liftBudget hquotientTrichotomy
  rcases hparent with hfull | hconcentration
  · exact Or.inl hfull
  · exact Or.inr (Or.inr hconcentration)
termination_by Nat.card A
decreasing_by
  exact R.quotientCardLt

/-- The recursive construction closes the proposition-valued goal exactly,
without accepting the goal itself as an input. -/
theorem ordinaryGMOPGroupStructuralInductionGoal
    (A : Type u) [AddCommGroup A] [Fintype A] :
    OrdinaryGMOPGroupStructuralInductionGoal A := by
  intro p hp hpTwo hA xs seed n I hn hambient hsourceWide
  exact ordinaryGMOPGroupStructuralTrichotomy
    A p hp hpTwo hA xs seed n I hn hambient hsourceWide

#print axioms GaoLean.nonempty_gmoTheoremESourceOutput_for_structuralInduction
#print axioms GaoLean.ordinaryGMOStructuralTrichotomy_of_large
#print axioms GaoLean.GMOTheoremESourceOutput.structuralTrichotomy_of_count_le_one
#print axioms GaoLean.OrdinaryGMOClaimBOutput.canonicalQuotient_budget
#print axioms GaoLean.OrdinaryGMOClaimBOutput.canonicalQuotient_zeroCapacity
#print axioms GaoLean.OrdinaryGMOClaimBOutput.structuralTrichotomy_of_K_eq_top
#print axioms GaoLean.OrdinaryGMOClaimBOutput.structuralInduction_quotientCard_lt
#print axioms GaoLean.ordinaryGMOPGroupStructuralTrichotomy
#print axioms GaoLean.ordinaryGMOPGroupStructuralInductionGoal

end GaoLean
