import GaoLean.PGReflectionChannel
import GaoLean.PGRotationExtraction
import GaoLean.PGReflectionExtraction

/-!
# Source-shaped PG-O3 controller closure

This module connects the source-faithful channel preparations to the already
checked zero bases and simultaneous strict-subgroup induction.  The remaining
inputs are exactly preparation theorems for the rotation-only channel and the
reflection-containing fixed-source channel, plus the isolated GJM-style small
Davenport bound.  No positive controller conclusion is assumed directly.
-/

namespace GaoLean

open ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Middle-range arithmetic supplies the zero-base inequality used by the
controller scheduler. -/
theorem middle_controller_base_bound {Q D a b : ℕ}
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (htotal : a + b = 2 * Q + D) :
    D ≤ b - Q + 2 := by
  omega

/-- Full PG-O3 controller skeleton from the two source-shaped preparation
families.  The rotation preparation is quantified over arbitrary auxiliary
`X` and is reused for the fixed source `S` when its quotient guard holds.  The
reflection preparation is fixed-source, exactly matching `RC_S`. -/
theorem concretePGO3ControllerSkeleton_of_channelPreparations
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (href : (reflectionOccurrences S).card = a)
    (hrot : (rotationOccurrences S).card = b)
    (hQ : Q = Nat.card A) (hAodd : Odd (Nat.card A))
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (htotal : a + b = 2 * Q + D)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (ConcreteGDihedral.Group A) D)
    (hrotationPrepare : ∀ (K : AddSubgroup A)
      (X : List (ConcreteGDihedral.Group A)),
      ⊥ < K → K < ⊤ →
      X.length = 2 * Q + D →
      (reflectionOccurrences X).card = a →
      (rotationOccurrences X).card = b →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
      QuotientNoReflection X K →
      RotationChannelPreparation X Q K)
    (hreflectionPrepare : ∀ K : AddSubgroup A,
      ⊥ < K → K < ⊤ →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn S K).card →
      ¬QuotientNoReflection S K →
      ReflectionChannelPreparation S Q K) :
    PGO3ControllerSkeleton QuotientNoReflection S Q D a b := by
  have hDb : D ≤ b - Q + 2 :=
    middle_controller_base_bound hDQ haD htotal
  have hRCpos : ConcreteRCPositiveStep S Q D a b :=
    concreteRCPositiveStep_of_channelPreparations
      S Q D a b hlen href hrot hQ hAodd
      (fun K hKpos hKtop hcapacity hguard =>
        hrotationPrepare K S hKpos hKtop hlen href hrot
          hcapacity hguard)
      hreflectionPrepare
  have hZRpos : ConcreteZRPositiveStep S Q D a b :=
    concreteZRPositiveStep_of_rotationChannelPreparations
      S Q D a b hrotationPrepare hQ
  exact concretePGO3ControllerSkeleton_of_positiveSteps
    S Q D a b hlen hQ hDb hsmall hRCpos hZRpos

/-- Controller closure with the rotation-channel preparation expanded into
its actual internal extraction plus the two remaining external inputs:
the quotient small-Davenport bound and the ordinary GMO provider.  The
reflection-channel preparation remains explicit and fixed-source. -/
theorem concretePGO3ControllerSkeleton_of_rotationGMOProviders
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (href : (reflectionOccurrences S).card = a)
    (hrot : (rotationOccurrences S).card = b)
    (hQ : Q = Nat.card A) (hAodd : Odd (Nat.card A))
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (htotal : a + b = 2 * Q + D)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (ConcreteGDihedral.Group A) D)
    (Dquot : AddSubgroup A → ℕ)
    (hsmallQuotient : ∀ K : AddSubgroup A,
      QuotientSmallDavenportProductOneFreeAtMost K (Dquot K))
    (hDquotLe : ∀ K : AddSubgroup A, Dquot K ≤ D)
    (hrotationGMO : ∀ (K : AddSubgroup A)
      (X : List (ConcreteGDihedral.Group A)),
      ⊥ < K → K < ⊤ →
      X.length = 2 * Q + D →
      (reflectionOccurrences X).card = a →
      (rotationOccurrences X).card = b →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
      QuotientNoReflection X K →
      RotationChannelGMOProvider X Q D a b K)
    (hreflectionPrepare : ∀ K : AddSubgroup A,
      ⊥ < K → K < ⊤ →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn S K).card →
      ¬QuotientNoReflection S K →
      ReflectionChannelPreparation S Q K) :
    PGO3ControllerSkeleton QuotientNoReflection S Q D a b := by
  apply concretePGO3ControllerSkeleton_of_channelPreparations
    S Q D a b hlen href hrot hQ hAodd hDQ haD htotal hsmall
  · intro K X hKpos hKtop hlenX hrefX hrotX hcapacity hguard
    exact rotationChannelPreparation_of_extraction
      X Q D a b (Dquot K) K htotal hrefX hrotX
      (hsmallQuotient K) (hDquotLe K) hQ hcapacity hguard
      (hrotationGMO K X hKpos hKtop hlenX hrefX hrotX
        hcapacity hguard)
  · exact hreflectionPrepare

/-- Both positive quotient channels expanded to their maximum-extraction
boundaries.  The only channel-specific assumptions left are the two explicit
GMO providers and the quotient small-Davenport provider. -/
theorem concretePGO3ControllerSkeleton_of_channelGMOProviders
    (S : List (ConcreteGDihedral.Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (href : (reflectionOccurrences S).card = a)
    (hrot : (rotationOccurrences S).card = b)
    (hQ : Q = Nat.card A) (hAodd : Odd (Nat.card A))
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (htotal : a + b = 2 * Q + D)
    (hsmall : SmallDavenportProductOneFreeAtMost
      (ConcreteGDihedral.Group A) D)
    (Dquot : AddSubgroup A → ℕ)
    (hsmallQuotient : ∀ K : AddSubgroup A,
      QuotientSmallDavenportProductOneFreeAtMost K (Dquot K))
    (hDquotLe : ∀ K : AddSubgroup A, Dquot K ≤ D)
    (hrotationGMO : ∀ (K : AddSubgroup A)
      (X : List (ConcreteGDihedral.Group A)),
      ⊥ < K → K < ⊤ →
      X.length = 2 * Q + D →
      (reflectionOccurrences X).card = a →
      (rotationOccurrences X).card = b →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
      QuotientNoReflection X K →
      RotationChannelGMOProvider X Q D a b K)
    (hreflectionGMO : ∀ K : AddSubgroup A,
      ⊥ < K → K < ⊤ →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn S K).card →
      ¬QuotientNoReflection S K →
      ReflectionChannelGMOProvider S Q D a b K) :
    PGO3ControllerSkeleton QuotientNoReflection S Q D a b := by
  apply concretePGO3ControllerSkeleton_of_rotationGMOProviders
    S Q D a b hlen href hrot hQ hAodd hDQ haD htotal hsmall
    Dquot hsmallQuotient hDquotLe hrotationGMO
  intro K hKpos hKtop hcapacity hchannel
  exact reflectionChannelPreparation_of_extraction
    S Q D a b (Dquot K) K href hrot htotal hDQ haD hQ hcapacity
    (hsmallQuotient K) (hDquotLe K) hchannel
    (hreflectionGMO K hKpos hKtop hcapacity hchannel)

end GaoLean

#print axioms GaoLean.middle_controller_base_bound
#print axioms GaoLean.concretePGO3ControllerSkeleton_of_channelPreparations
#print axioms GaoLean.concretePGO3ControllerSkeleton_of_rotationGMOProviders
#print axioms GaoLean.concretePGO3ControllerSkeleton_of_channelGMOProviders
