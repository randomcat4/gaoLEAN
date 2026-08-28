import GaoLean.PGGaoOrdinaryComplete
import GaoLean.PGHomocyclic
import GaoLean.PGDavenportBridge
import GaoLean.PGLowerBound

/-!
# Unconditional manuscript consequences

This module exposes the two numerical displays of Corollary 6.1 without the
historical remaining-input parameter, and records an occurrence-labelled
lower witness for the introductory `C₃²` example.  The latter uses the
standard two-coordinate Olson witness: two labelled copies of each coordinate
generator, followed by one reflection and seventeen identities.
-/

namespace GaoLean

/-! ## Unconditional Corollary 6.1 -/

namespace ConcreteGDihedral

/-- Unconditional homocyclic display from Corollary 6.1, with exactly the
prime, oddness and nontriviality quantifiers of the conditional version. -/
theorem pgGao_homocyclic_display
    (p k r : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    [Nontrivial (HomocyclicKernel p k r)] :
    letI : NeZero p := ⟨hp.ne_zero⟩
    IsExactProductOneThreshold
      (Group (HomocyclicKernel p k r))
      (2 * p ^ (k * r) + r * (p ^ k - 1) + 1)
      (2 * p ^ (k * r)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact pgGao_homocyclic_display_of_structuralRemainingInputs
    (pgGaoStructuralRemainingInputs_of_ordinaryRemainingInputs
      pgGaoOrdinaryRemainingInputs)
    p k r hp hpTwo

/-- Unconditional elementary-abelian display, the `k=1` line of
Corollary 6.1. -/
theorem pgGao_elementaryAbelian_display
    (p r : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    [Nontrivial (HomocyclicKernel p 1 r)] :
    letI : NeZero p := ⟨hp.ne_zero⟩
    IsExactProductOneThreshold
      (Group (HomocyclicKernel p 1 r))
      (2 * p ^ r + r * (p - 1) + 1)
      (2 * p ^ r) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact pgGao_elementaryAbelian_display_of_structuralRemainingInputs
    (pgGaoStructuralRemainingInputs_of_ordinaryRemainingInputs
      pgGaoOrdinaryRemainingInputs)
    p r hp hpTwo

/-! ## The introductory `C₃²` lower witness -/

/-- The two-coordinate Olson witness in `C₃²`.  Its canonical occurrence
labels are `Σ i : Fin 2, Fin 2`, so it contains two distinguished copies of
each coordinate generator even though its internal enumeration order is not
part of the statement. -/
noncomputable def c3SquaredDavenportWitness :
    List (HomocyclicKernel 3 1 2) :=
  invariantProductDavenportWitness 3 (fun _ : Fin 2 ↦ 1)
    (AddEquiv.refl _)

/-- The witness has the four additive terms used in the manuscript example. -/
theorem length_c3SquaredDavenportWitness :
    c3SquaredDavenportWitness.length = 4 := by
  simpa [c3SquaredDavenportWitness] using
    length_invariantProductDavenportWitness 3 (fun _ : Fin 2 ↦ 1)
      (AddEquiv.refl (HomocyclicKernel 3 1 2))

/-- The four-term witness is occurrence-labelled zero-sum-free. -/
theorem c3SquaredDavenportWitness_zeroSumFree :
    ¬HasNonemptyZeroSum c3SquaredDavenportWitness := by
  exact invariantProductDavenportWitness_zeroSumFree 3 Nat.prime_three
    (fun _ : Fin 2 ↦ 1) (AddEquiv.refl _)

/-- Canonical labels identify the witness with two copies in each of its two
coordinates. -/
noncomputable def c3SquaredDavenportWitnessOccurrenceEquiv :
    Occurrence c3SquaredDavenportWitness ≃ Σ _i : Fin 2, Fin 2 :=
  invariantProductWitnessOccurrenceEquiv 3 (fun _ : Fin 2 ↦ 1)
    (AddEquiv.refl _)

/-- Under the preceding label equivalence, every occurrence has exactly its
coordinate generator value; the copy label affects only occurrence identity. -/
theorem occurrenceValue_c3SquaredDavenportWitness
    (j : Occurrence c3SquaredDavenportWitness) :
    occurrenceValue c3SquaredDavenportWitness j =
      invariantProductGenerator 3 (fun _ : Fin 2 ↦ 1)
        (AddEquiv.refl (HomocyclicKernel 3 1 2))
        ((invariantProductWitnessOccurrenceEquiv 3
          (fun _ : Fin 2 ↦ 1)
          (AddEquiv.refl (HomocyclicKernel 3 1 2)) j).1) := by
  exact
    occurrenceValue_invariantProductDavenportWitness 3
      (fun _ : Fin 2 ↦ 1) (AddEquiv.refl (HomocyclicKernel 3 1 2)) j

/-- Append the distinguished reflection to obtain the five-term
product-one-free word from the introductory lower bound. -/
noncomputable def c3SquaredProductOneFreeWord :
    List (Group (HomocyclicKernel 3 1 2)) :=
  davenportLiftWord c3SquaredDavenportWitness

theorem length_c3SquaredProductOneFreeWord :
    c3SquaredProductOneFreeWord.length = 5 := by
  simp [c3SquaredProductOneFreeWord, davenportLiftWord,
    length_c3SquaredDavenportWitness]

theorem c3SquaredProductOneFreeWord_isProductOneFree :
    IsProductOneFreeSelection c3SquaredProductOneFreeWord Finset.univ := by
  exact isProductOneFreeSelection_davenportLiftWord
    c3SquaredDavenportWitness c3SquaredDavenportWitness_zeroSumFree

/-- The literal 22-term lower source: five product-one-free terms followed by
seventeen identities. -/
noncomputable def c3SquaredPaddedLowerWord :
    List (Group (HomocyclicKernel 3 1 2)) :=
  c3SquaredProductOneFreeWord ++ List.replicate 17 1

theorem length_c3SquaredPaddedLowerWord :
    c3SquaredPaddedLowerWord.length = 22 := by
  simp [c3SquaredPaddedLowerWord, length_c3SquaredProductOneFreeWord]

/-- The padded 22-term source has no product-one block of the required
18 occurrences. -/
theorem c3SquaredPaddedLowerWord_no_eighteenBlock :
    ¬HasProductOneSubsequenceOfCard c3SquaredPaddedLowerWord 18 := by
  exact noProductOneBlock_of_identityPadding
    c3SquaredProductOneFreeWord 18 17
      c3SquaredProductOneFreeWord_isProductOneFree (by omega)

/-- The complete numerical threshold displayed for `C₃²`: every source of
length 23 has an 18-term product-one block, while counterexamples exist at
every smaller length. -/
theorem pgGao_c3Squared_threshold :
    IsExactProductOneThreshold
      (Group (HomocyclicKernel 3 1 2)) 23 18 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Nontrivial (HomocyclicKernel 3 1 2) := inferInstance
  simpa using pgGao_elementaryAbelian_display 3 2 Nat.prime_three (by omega)

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ConcreteGDihedral.pgGao_homocyclic_display
#print axioms GaoLean.ConcreteGDihedral.pgGao_elementaryAbelian_display
#print axioms GaoLean.ConcreteGDihedral.c3SquaredDavenportWitness_zeroSumFree
#print axioms GaoLean.ConcreteGDihedral.c3SquaredProductOneFreeWord_isProductOneFree
#print axioms GaoLean.ConcreteGDihedral.c3SquaredPaddedLowerWord_no_eighteenBlock
#print axioms GaoLean.ConcreteGDihedral.pgGao_c3Squared_threshold
