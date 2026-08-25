import GaoLean.PGGMO

/-!
# Source-faithful rotation-only quotient channel

The rotation-only channel in A-R6 Section 5.2 uses two disjoint labelled
reservoirs: `C`, the rotations whose coordinates lie in `K`, and `Bprime`, the
outside-`K` rotations extracted into quotient zero-sum blocks.  The full GMO
branch removes `D0 ⊆ C` and keeps `(C \ D0) ∪ Bprime`; the non-full branch
concentrates occurrences only from `C`.

Keeping these reservoirs separate is essential: using their union as the GMO
input would demand the stronger, unsupported non-full count
`|C| + |Bprime| - |K/H| + 2`.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact post-GMO alternative consumed by the source rotation-only channel.

In the full branch, `D0` is the exact-`d` subselection of the `K`-rotation
reservoir and its coordinate sum includes the defect carried by `Bprime`.  In
the non-full branch, the concentration lower bound uses `M=|C|`, exactly as in
the published GMO application.  This is an explicit proposition parameter,
not a proof of GMO. -/
def RotationChannelAlternative
    (s : List (Group A)) (C Bprime : Selection s)
    (K : AddSubgroup A) (M d : ℕ) : Prop :=
  (∃ D0 : Selection s,
      D0 ⊆ C ∧ D0.card = d ∧
        coordinateSum s D0 = coordinateSum s C + coordinateSum s Bprime) ∨
  (∃ (H : AddSubgroup A), H < K ∧
    ∃ α : A, α ∈ K ∧
      ∃ X : Selection s,
        X ⊆ C ∧
        (∀ i ∈ X, coordinate (occurrenceValue s i) - α ∈ H) ∧
        M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ X.card)

/-- Complete mechanical consumer of the source-faithful rotation-channel
alternative.  The full branch forms the actual occurrence union
`(C \ D0) ∪ Bprime`; the non-full branch performs strict capacity descent,
recursive `ZR`, translation, and pullback. -/
theorem hasAllRotationProductOneSubsequence_of_rotationChannelAlternative
    (s : List (Group A)) (Q D a b M d : ℕ)
    (K : AddSubgroup A) (hKtop : K < ⊤)
    (C Bprime : Selection s)
    (hCcard : C.card = M)
    (hCBdisjoint : Disjoint C Bprime)
    (hallC : ∀ i ∈ C, IsRotation (occurrenceValue s i))
    (hallBprime : ∀ i ∈ Bprime, IsRotation (occurrenceValue s i))
    (hsize : M - d + Bprime.card = 2 * Q)
    (hAlt : RotationChannelAlternative s C Bprime K M d)
    (hsmallZR : ∀ (H : AddSubgroup A), H < K →
      ∀ Y : List (Group A), ConcreteZRStatement Y Q D a b H)
    (hlen : s.length = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hM : b - Nat.card (A ⧸ K) + 2 ≤ M)
    (hguard : QuotientNoReflection s K)
    (hQ : Q = Nat.card A) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  rcases hAlt with hfull | hnonfull
  · rcases hfull with ⟨D0, hD0sub, hD0card, hD0sum⟩
    let I : Selection s := (C \ D0) ∪ Bprime
    have hdiffB : Disjoint (C \ D0) Bprime :=
      hCBdisjoint.mono_left Finset.sdiff_subset
    have hIcard : I.card = 2 * Q := by
      dsimp only [I]
      rw [Finset.card_union_of_disjoint hdiffB,
        Finset.card_sdiff_of_subset hD0sub, hCcard, hD0card, hsize]
    have hallI : ∀ i ∈ I, IsRotation (occurrenceValue s i) := by
      intro i hi
      rcases Finset.mem_union.mp hi with hiDiff | hiB
      · exact hallC i (Finset.mem_sdiff.mp hiDiff).1
      · exact hallBprime i hiB
    have hIsum : coordinateSum s I = 0 := by
      dsimp only [I]
      rw [coordinateSum_union s (C \ D0) Bprime hdiffB,
        coordinateSum_sdiff s C D0 hD0sub, hD0sum]
      abel
    exact hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
      s I (2 * Q) hIcard hallI hIsum
  · rcases hnonfull with
      ⟨H, hHK, α, hα, X, hXsub, hXcoset, hXcard⟩
    have hX : ∀ i ∈ X,
        IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) - α ∈ H := by
      intro i hi
      exact ⟨hallC i (hXsub hi), hXcoset i hi⟩
    exact hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR
      α s Q D a b M H K hHK hKtop X hX hM hXcard
      (hsmallZR H hHK (translatedSequence α s))
      hlen href hrot hα hguard hQ

/-- Source-shaped prepared data for the rotation-only channel.  The equality
`C = rotationOccurrencesIn s K` makes the controller capacity hypothesis feed
the actual GMO reservoir, while `BprimeOutside` records the source split even
though the final algebra only needs disjointness and rotation typing. -/
structure RotationChannelPreparedData
    (s : List (Group A)) (Q : ℕ) (K : AddSubgroup A) where
  M : ℕ
  d : ℕ
  C : Selection s
  Bprime : Selection s
  C_eq : C = rotationOccurrencesIn s K
  Ccard : C.card = M
  CBdisjoint : Disjoint C Bprime
  allC : ∀ i ∈ C, IsRotation (occurrenceValue s i)
  allBprime : ∀ i ∈ Bprime, IsRotation (occurrenceValue s i)
  BprimeOutside : ∀ i ∈ Bprime,
    coordinate (occurrenceValue s i) ∉ K
  exactSize : M - d + Bprime.card = 2 * Q
  alternative : RotationChannelAlternative s C Bprime K M d

/-- A prepared rotation-channel datum consumes exactly the current `ZR`
hypotheses and strict smaller-`ZR` family. -/
theorem RotationChannelPreparedData.hasAllRotationProductOneSubsequence
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : RotationChannelPreparedData s Q K)
    (hKtop : K < ⊤)
    (hsmallZR : ∀ (H : AddSubgroup A), H < K →
      ∀ Y : List (Group A), ConcreteZRStatement Y Q D a b H)
    (hlen : s.length = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hguard : QuotientNoReflection s K)
    (hQ : Q = Nat.card A) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  have hM : b - Nat.card (A ⧸ K) + 2 ≤ h.M := by
    rw [← h.Ccard, h.C_eq]
    exact hcapacity
  exact hasAllRotationProductOneSubsequence_of_rotationChannelAlternative
    s Q D a b h.M h.d K hKtop h.C h.Bprime h.Ccard h.CBdisjoint
      h.allC h.allBprime h.exactSize h.alternative hsmallZR
      hlen href hrot hM hguard hQ

/-- Exact missing preparation obligation for a positive `ZR` step.  It asks
for the quotient block extraction and the source-faithful GMO output, not for
the desired product-one conclusion. -/
def RotationChannelPreparation
    (s : List (Group A)) (Q : ℕ) (K : AddSubgroup A) : Prop :=
  Nonempty (RotationChannelPreparedData s Q K)

/-- Construct the actual positive-subgroup `ZR` step from source-shaped
rotation-channel preparations.  The fixed-source smaller-`RC` family is
intentionally unused, matching the paper: this channel recurses only through
strict smaller `ZR`. -/
theorem concreteZRPositiveStep_of_rotationChannelPreparations
    (S : List (Group A)) (Q D a b : ℕ)
    (hprepare : ∀ (K : AddSubgroup A) (X : List (Group A)),
      ⊥ < K → K < ⊤ →
      X.length = 2 * Q + D →
      (reflectionOccurrences X).card = a →
      (rotationOccurrences X).card = b →
      b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
      QuotientNoReflection X K →
      RotationChannelPreparation X Q K)
    (hQ : Q = Nat.card A) :
    ConcreteZRPositiveStep S Q D a b := by
  intro K X hKpos hKtop _hsmallRC hsmallZR
  change X.length = 2 * Q + D →
    (reflectionOccurrences X).card = a →
    (rotationOccurrences X).card = b →
    b - Nat.card (A ⧸ K) + 2 ≤ (rotationOccurrencesIn X K).card →
    QuotientNoReflection X K →
    HasAllRotationProductOneSubsequenceOfCard X (2 * Q)
  intro hlen href hrot hcapacity hguard
  rcases hprepare K X hKpos hKtop hlen href hrot hcapacity hguard with
    ⟨hdata⟩
  exact hdata.hasAllRotationProductOneSubsequence hKtop hsmallZR
    hlen href hrot hcapacity hguard hQ

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_rotationChannelAlternative
#print axioms GaoLean.ConcreteGDihedral.RotationChannelPreparedData.hasAllRotationProductOneSubsequence
#print axioms GaoLean.ConcreteGDihedral.concreteZRPositiveStep_of_rotationChannelPreparations
