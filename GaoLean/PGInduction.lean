import GaoLean.PGBase

/-!
# Strict simultaneous induction for PG-O3

The paper proves the fixed-source controller and the arbitrary-sequence
controller simultaneously, with recursive calls only at strict subgroups.
For a finite ambient group, strict subgroup inclusion is well founded.  This
file checks that scheduler and specializes it to the concrete quotient guard.

The two one-level step predicates below are proof obligations, not imported
theorems.  In particular, this module does not supply the GMO branch arguments
needed to inhabit them.
-/

namespace GaoLean

section FiniteSubgroupInduction

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Strict containment of finite additive subgroups strictly lowers their
cardinality.  This is a simpler well-founded rank than the paper's
`log_p |K|`, and requires no additional p-group arithmetic. -/
theorem natCard_lt_of_addSubgroup_lt {H K : AddSubgroup A} (hHK : H < K) :
    Nat.card H < Nat.card K := by
  change (H : Set A).ncard < (K : Set A).ncard
  exact Set.ncard_lt_ncard hHK

/-- Strong induction over the strict-subgroup relation of a finite ambient
additive group. -/
theorem addSubgroup_strongInduction
    (P : AddSubgroup A → Prop)
    (step : ∀ K, (∀ H, H < K → P H) → P K) :
    ∀ K, P K := by
  intro K
  have hwf : WellFounded (fun H K : AddSubgroup A => H < K) :=
    Finite.wellFounded_of_trans_of_irrefl _
  exact hwf.induction K (fun K ih => step K (fun H hHK => ih H hHK))

end FiniteSubgroupInduction

section ConcreteControllerInduction

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The two conclusions which must be established together at subgroup `K`:
one fixed-source `RC` conclusion and all auxiliary-sequence `ZR` conclusions. -/
def ConcreteControllerAt
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (K : AddSubgroup A) : Prop :=
  RCStatement S Q b K ∧
    ∀ X : List (ConcreteGDihedral.Group A), ConcreteZRStatement X Q D a b K

/-- One-level fixed-source obligation.  It may use both controller families,
but only at strict subgroups. -/
def ConcreteRCStrictStep
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ) : Prop :=
  ∀ K : AddSubgroup A, K < ⊤ →
    (∀ H : AddSubgroup A, H < K → RCStatement S Q b H) →
    (∀ (H : AddSubgroup A), H < K →
      ∀ X : List (ConcreteGDihedral.Group A),
        ConcreteZRStatement X Q D a b H) →
    RCStatement S Q b K

/-- One-level arbitrary-sequence obligation.  As in the paper, it may use
either smaller controller family, but never a same-level recursive call. -/
def ConcreteZRStrictStep
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ) : Prop :=
  ∀ (K : AddSubgroup A) (X : List (ConcreteGDihedral.Group A)), K < ⊤ →
    (∀ H : AddSubgroup A, H < K → RCStatement S Q b H) →
    (∀ (H : AddSubgroup A), H < K →
      ∀ Y : List (ConcreteGDihedral.Group A),
        ConcreteZRStatement Y Q D a b H) →
    ConcreteZRStatement X Q D a b K

/-- The fixed-source local step restricted to nonzero proper subgroups.  The
zero subgroup is handled separately by `PGBase.lean`. -/
def ConcreteRCPositiveStep
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ) : Prop :=
  ∀ K : AddSubgroup A, ⊥ < K → K < ⊤ →
    (∀ H : AddSubgroup A, H < K → RCStatement S Q b H) →
    (∀ (H : AddSubgroup A), H < K →
      ∀ X : List (ConcreteGDihedral.Group A),
        ConcreteZRStatement X Q D a b H) →
    RCStatement S Q b K

/-- The arbitrary-sequence local step restricted to nonzero proper
subgroups. -/
def ConcreteZRPositiveStep
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ) : Prop :=
  ∀ (K : AddSubgroup A) (X : List (ConcreteGDihedral.Group A)),
    ⊥ < K → K < ⊤ →
    (∀ H : AddSubgroup A, H < K → RCStatement S Q b H) →
    (∀ (H : AddSubgroup A), H < K →
      ∀ Y : List (ConcreteGDihedral.Group A),
        ConcreteZRStatement Y Q D a b H) →
    ConcreteZRStatement X Q D a b K

/-- Both zero-layer bases, with their fixed-`S` versus arbitrary-`X`
quantifiers kept distinct, follow from the explicit GJM-style bound. -/
theorem concreteControllerAt_bot_of_smallDavenport
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (hQ : Q = Nat.card A) (hDb : D ≤ b - Q + 2)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (ConcreteGDihedral.Group A) D) :
    ConcreteControllerAt S Q D a b ⊥ := by
  constructor
  · exact ConcreteGDihedral.rcStatement_bot_of_smallDavenport
      S Q D b hlen hQ hDb hsmall
  · intro X
    exact ConcreteGDihedral.concreteZRStatement_bot_of_smallDavenport
      X Q D a b hQ hDb hsmall

/-- Mechanical scheduler for Section 5.4.  Once the two local branch
obligations are proved, finite strict-subgroup induction yields exactly the
paper's fixed-`S`/arbitrary-`X` controller skeleton with the concrete guard. -/
theorem concretePGO3ControllerSkeleton_of_strictSteps
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hRC : ConcreteRCStrictStep S Q D a b)
    (hZR : ConcreteZRStrictStep S Q D a b) :
    PGO3ControllerSkeleton ConcreteGDihedral.QuotientNoReflection
      S Q D a b := by
  let P : AddSubgroup A → Prop := fun K =>
    K < ⊤ → ConcreteControllerAt S Q D a b K
  have hall : ∀ K, P K :=
    addSubgroup_strongInduction P (fun K ih hKtop => by
      have hsmallRC : ∀ H : AddSubgroup A, H < K → RCStatement S Q b H := by
        intro H hHK
        exact (ih H hHK (hHK.trans hKtop)).1
      have hsmallZR : ∀ (H : AddSubgroup A), H < K →
          ∀ X : List (ConcreteGDihedral.Group A),
            ConcreteZRStatement X Q D a b H := by
        intro H hHK X
        exact (ih H hHK (hHK.trans hKtop)).2 X
      exact ⟨hRC K hKtop hsmallRC hsmallZR,
        fun X => hZR K X hKtop hsmallRC hsmallZR⟩)
  constructor
  · intro K hKtop
    exact (hall K hKtop).1
  · intro X K hKtop
    exact (hall K hKtop).2 X

/-- End-to-end induction scheduler with the two zero bases already closed.
Only the nonzero proper-subgroup branch proofs remain as explicit inputs. -/
theorem concretePGO3ControllerSkeleton_of_positiveSteps
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (hQ : Q = Nat.card A) (hDb : D ≤ b - Q + 2)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (ConcreteGDihedral.Group A) D)
    (hRCpos : ConcreteRCPositiveStep S Q D a b)
    (hZRpos : ConcreteZRPositiveStep S Q D a b) :
    PGO3ControllerSkeleton ConcreteGDihedral.QuotientNoReflection
      S Q D a b := by
  have hbase : ConcreteControllerAt S Q D a b ⊥ :=
    concreteControllerAt_bot_of_smallDavenport S Q D a b
      hlen hQ hDb hsmall
  apply concretePGO3ControllerSkeleton_of_strictSteps S Q D a b
  · intro K hKtop hsmallRC hsmallZR
    by_cases hK : K = ⊥
    · simpa [hK] using hbase.1
    · exact hRCpos K (bot_lt_iff_ne_bot.mpr hK) hKtop hsmallRC hsmallZR
  · intro K X hKtop hsmallRC hsmallZR
    by_cases hK : K = ⊥
    · simpa [hK] using hbase.2 X
    · exact hZRpos K X (bot_lt_iff_ne_bot.mpr hK) hKtop hsmallRC hsmallZR

end ConcreteControllerInduction

end GaoLean

#print axioms GaoLean.natCard_lt_of_addSubgroup_lt
#print axioms GaoLean.addSubgroup_strongInduction
#print axioms GaoLean.concreteControllerAt_bot_of_smallDavenport
#print axioms GaoLean.concretePGO3ControllerSkeleton_of_strictSteps
#print axioms GaoLean.concretePGO3ControllerSkeleton_of_positiveSteps
