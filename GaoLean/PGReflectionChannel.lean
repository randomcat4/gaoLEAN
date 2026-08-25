import GaoLean.PGRotationChannel
import GaoLean.PGMiddleNonfull

/-!
# Reflection-containing quotient channel

This module formalizes the two post-preparation outcomes of A-R6 Section 5.2's
reflection-containing channel.  A full signed-spectrum outcome is represented
by the exact balanced-sign occurrence certificate consumed by the previously
checked literal ordering.  A non-full outcome retains the weighted-coset
conditions, proves that every concentrated coordinate lies in a strict
`H < K`, composes the exact capacity inequality, and invokes `RC_S(H)` on the
unchanged fixed source sequence.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact post-signed-GMO certificate for the full reflection channel.  It is
strictly before the product-one conclusion: the explicit balanced assignment
still has to be checked by the literal-ordering theorem. -/
structure ReflectionChannelFullOutput
    (s : List (Group A)) (Q : ℕ) where
  selected : Selection s
  card_selected : selected.card = 2 * Q
  assignment : BalancedSignedAssignment (selectedMultiset s selected)

theorem ReflectionChannelFullOutput.hasProductOneSubsequence
    {s : List (Group A)} {Q : ℕ}
    (h : ReflectionChannelFullOutput s Q) :
    HasProductOneSubsequenceOfCard s (2 * Q) :=
  hasProductOneSubsequenceOfCard_of_balancedSignedAssignment
    s h.selected (2 * Q) h.card_selected h.assignment

/-- Source-faithful post-GMO split for the reflection-containing channel.
The non-full lower bound is measured against the actual `K`-rotation reservoir
of cardinality `M`, and the weighted coset data is kept in difference form. -/
def ReflectionChannelAlternative
    (s : List (Group A)) (Q : ℕ) (C : Selection s)
    (K : AddSubgroup A) (M : ℕ) : Prop :=
  Nonempty (ReflectionChannelFullOutput s Q) ∨
  (∃ (H : AddSubgroup A), H < K ∧
    ∃ X : Selection s,
      X ⊆ C ∧
      M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ X.card ∧
      ∀ i ∈ X, ∃ β : A,
        coordinate (occurrenceValue s i) - β ∈ H ∧
        -coordinate (occurrenceValue s i) - β ∈ H)

/-- Prepared fixed-source data for the reflection-containing channel. -/
structure ReflectionChannelPreparedData
    (s : List (Group A)) (Q : ℕ) (K : AddSubgroup A) where
  M : ℕ
  C : Selection s
  C_eq : C = rotationOccurrencesIn s K
  Ccard : C.card = M
  allC : ∀ i ∈ C, IsRotation (occurrenceValue s i)
  alternative : ReflectionChannelAlternative s Q C K M

/-- The full branch closes by balanced literal ordering.  The non-full branch
derives actual `H`-membership occurrence-by-occurrence, composes (5.10)-(5.11),
and calls the strict smaller fixed-source controller. -/
theorem ReflectionChannelPreparedData.hasProductOneSubsequence
    {s : List (Group A)} {Q b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreparedData s Q K)
    (hKtop : K < ⊤)
    (hsmallRC : ∀ H : AddSubgroup A, H < K → RCStatement s Q b H)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hAodd : Odd (Nat.card A)) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  rcases h.alternative with hfull | hnonfull
  · rcases hfull with ⟨hout⟩
    exact hout.hasProductOneSubsequence
  · rcases hnonfull with
      ⟨H, hHK, X, hXsub, hXcard, hXcoset⟩
    letI : Fintype (A ⧸ H) := Fintype.ofFinite (A ⧸ H)
    have hoddNat : Odd (Nat.card (A ⧸ H)) :=
      odd_natCard_quotient_of_odd_natCard H hAodd
    have hodd : Odd (Fintype.card (A ⧸ H)) := by
      simpa using hoddNat
    have hXsubset : X ⊆ rotationOccurrencesIn s H := by
      intro i hi
      obtain ⟨β, hpos, hneg⟩ := hXcoset i hi
      have hmem : coordinate (occurrenceValue s i) ∈ H :=
        mem_of_pos_neg_mem_same_coset_of_quotient_card_odd
          H hodd hpos hneg
      simp only [rotationOccurrencesIn, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨h.allC i (hXsub hi), hmem⟩
    have hM : b - Nat.card (A ⧸ K) + 2 ≤ h.M := by
      rw [← h.Ccard, h.C_eq]
      exact hcapacity
    have hXcapacity : b - Nat.card (A ⧸ H) + 2 ≤ X.card :=
      residual_capacity_composition_of_strict
        H K hHK hKtop b h.M X.card hM hXcard
    have hHcapacity : b - Nat.card (A ⧸ H) + 2 ≤
        (rotationOccurrencesIn s H).card :=
      hXcapacity.trans (Finset.card_le_card hXsubset)
    exact hsmallRC H hHK hHcapacity

/-- Exact missing preparation obligation for the fixed-source reflection
channel. -/
def ReflectionChannelPreparation
    (s : List (Group A)) (Q : ℕ) (K : AddSubgroup A) : Prop :=
  Nonempty (ReflectionChannelPreparedData s Q K)

/-- Build the actual positive fixed-source `RC` step by splitting on the
quotient no-reflection guard.  The guard branch uses the source-faithful
rotation channel and recurses only through smaller `ZR`; the other branch uses
the reflection channel and recurses only through smaller fixed-source `RC`. -/
theorem concreteRCPositiveStep_of_channelPreparations
    (S : List (Group A)) (Q D a b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (href : (reflectionOccurrences S).card = a)
    (hrot : (rotationOccurrences S).card = b)
    (hQ : Q = Nat.card A) (hAodd : Odd (Nat.card A))
    (hrotationPrepare : ∀ K : AddSubgroup A,
      ⊥ < K → K < ⊤ →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn S K).card →
      QuotientNoReflection S K →
      RotationChannelPreparation S Q K)
    (hreflectionPrepare : ∀ K : AddSubgroup A,
      ⊥ < K → K < ⊤ →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn S K).card →
      ¬QuotientNoReflection S K →
      ReflectionChannelPreparation S Q K) :
    ConcreteRCPositiveStep S Q D a b := by
  intro K hKpos hKtop hsmallRC hsmallZR
  intro hcapacity
  by_cases hguard : QuotientNoReflection S K
  · rcases hrotationPrepare K hKpos hKtop hcapacity hguard with
      ⟨hdata⟩
    rcases hdata.hasAllRotationProductOneSubsequence hKtop hsmallZR
        hlen href hrot hcapacity hguard hQ with
      ⟨I, hIcard, hIprod, _⟩
    exact ⟨I, hIcard, hIprod⟩
  · rcases hreflectionPrepare K hKpos hKtop hcapacity hguard with
      ⟨hdata⟩
    exact hdata.hasProductOneSubsequence hKtop hsmallRC hcapacity hAodd

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelFullOutput.hasProductOneSubsequence
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelPreparedData.hasProductOneSubsequence
#print axioms GaoLean.ConcreteGDihedral.concreteRCPositiveStep_of_channelPreparations
