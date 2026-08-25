import GaoLean.PGSpectrum

/-!
# Explicit GMO rotation-spectrum interface

This file provides an abstract single-reservoir ordinary-spectrum consumer.
`OrdinarySpectrumAlternative` is a proposition parameter, not an axiom and not
a proof of GMO.  It is useful when the same reservoir supports both branches,
but it is not by itself the exact A-R6 Section 5.2 encoding when the full branch
also retains a disjoint outside-`K` block `Bprime`; the source-faithful split is
implemented in `PGRotationChannel.lean`.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Abstract occurrence-labelled full/non-full output for a single reservoir
inside a fixed subgroup `K`.

The full branch supplies the prescribed-size coordinate-sum selection.  The
non-full branch supplies a strict `H<K`, a translation center in `K`, and a
large labelled subset of the affine coset `α+H`. -/
def OrdinarySpectrumAlternative
    (s : List (Group A)) (R : Selection s)
    (K : AddSubgroup A) (M d : ℕ) : Prop :=
  (∃ D : Selection s,
      D ⊆ R ∧ D.card = d ∧ coordinateSum s D = coordinateSum s R) ∨
  (∃ (H : AddSubgroup A), H < K ∧
    ∃ α : A, α ∈ K ∧
      ∃ C : Selection s,
        C ⊆ R ∧
        (∀ i ∈ C, coordinate (occurrenceValue s i) - α ∈ H) ∧
        M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ C.card)

/-- Complete internal consumer of the ordinary GMO alternative.  Every
occurrence, guard, cardinality, recursive-call, and pullback obligation after
the external alternative is mechanically discharged. -/
theorem hasAllRotationProductOneSubsequence_of_ordinarySpectrumAlternative
    (s : List (Group A)) (Q D a b M d : ℕ)
    (K : AddSubgroup A) (hKtop : K < ⊤)
    (R : Selection s)
    (hRcard : R.card = M)
    (hallR : ∀ i ∈ R, IsRotation (occurrenceValue s i))
    (hsize : M - d = 2 * Q)
    (hAlt : OrdinarySpectrumAlternative s R K M d)
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
  · rcases hfull with ⟨Dsel, hDsub, hDcard, hDsum⟩
    exact hasAllRotationProductOneSubsequence_of_fullSpectrumComplement
      s R Dsel Q M d hDsub hRcard hDcard hsize hallR hDsum
  · rcases hnonfull with
      ⟨H, hHK, α, hα, C, hCsub, hCcoset, hCcard⟩
    have hC : ∀ i ∈ C,
        IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) - α ∈ H := by
      intro i hi
      exact ⟨hallR i (hCsub hi), hCcoset i hi⟩
    exact hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR
      α s Q D a b M H K hHK hKtop C hC hM hCcard
      (hsmallZR H hHK (translatedSequence α s))
      hlen href hrot hα hguard hQ

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_ordinarySpectrumAlternative
