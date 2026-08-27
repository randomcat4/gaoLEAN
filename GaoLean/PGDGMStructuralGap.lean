import GaoLean.PGPlusMinusSetpartition

/-!
# A single-layer obstruction to an over-strong DGM structural interface

For one signed layer, quotient-layer membership says only that at least one of
`x` and `-x` lies in the chosen quotient coset.  The example below shows that
this does not imply that both signed values lie in that same coset: modulo the
trivial subgroup of `ZMod 5`, the layer `{1, -1} = {1, 4}` contains `1` but is
not contained in the singleton coset `{1}`.

This certificate refutes only the proposed direct implication from single-layer
DGM membership to the two-sign common-coset condition.  It is not a
counterexample to the DGM theorem, GMO Corollary 1.3, or any full/concentrated
alternative, all of which use additional global and structural information.
-/

namespace GaoLean

/-- A member of a signed layer need not contain the entire signed layer in its
singleton coset.  Here `plusMinusValueBlock x` is literally `{x, -x}`. -/
theorem zmod5_signedLayer_member_not_subset_singleton :
    ∃ x q : ZMod 5,
      q ∈ plusMinusValueBlock x ∧
        ¬plusMinusValueBlock x ⊆ ({q} : Finset (ZMod 5)) := by
  refine ⟨1, 1, ?_, ?_⟩
  · simp [plusMinusValueBlock]
  · intro hsubset
    have hminus : -(1 : ZMod 5) ∈ plusMinusValueBlock (1 : ZMod 5) := by
      simp [plusMinusValueBlock]
    have heq : -(1 : ZMod 5) = 1 := by
      simpa using hsubset hminus
    exact (by decide : -(1 : ZMod 5) ≠ 1) heq

end GaoLean

#print axioms GaoLean.zmod5_signedLayer_member_not_subset_singleton
