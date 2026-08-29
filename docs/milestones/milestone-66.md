# Milestone 66 — strict DGM endpoint and three-line integration check

Date: 2026-08-27

Status: **LEAN-CONDITIONAL**.  This checkpoint is not the unconditional
formalization of the 13-page PR #7 manuscript.

## New formalized content

- The weighted two-exceptional-coset Xi estimate is now aggregated across
  refinement fibres without duplicating the coarse contribution.
- The four non-strict source bounds corresponding to equations (4) and (5)
  are combined into the correct additive upper bound.
- The final strict coset-cover contradiction is proved from that upper bound,
  using positivity of the fine subgroup instead of the previously over-strong
  strict arithmetic interface.
- The signed Corollary 1.2/1.3 provider package and the corrected Theorem E
  cardinal bound remain compatible with the new DGM file.

## Verification

- `GaoLean/PGDGMCore.lean` direct Lean check: pass.
- Joint build of `GaoLean.PGDGMCore`, `GaoLean.PGGMOTheorem21`, and
  `GaoLean.PGGMOTheorem11`: **8707/8707 pass**.
- Axiom output remains limited to `propext`, `Classical.choice`, and
  `Quot.sound`.
- Integrated source hashes:
  - DGM: `ded21313e43c07cd7df93e01645bb4a5967ab355be259a2a4c03ac4b71620819`
  - ordinary GMO: `38bc1f9625087430ad033f899e68a81da57c6eff1e48f316074b0b054cb476db`
  - signed GMO: `f110e76710410547ae7215ec4c130a8a88ff3bf04b23b9e211694911f55d73f4`

## Honest remaining boundary

General DGM is not yet closed.  The remaining proof must still derive the
exceptional hypotheses from infeasibility of the transformed labelled
pattern, reconstruct Claim 1 and the strict equations (2)--(3), respect the
epsilon-2 nonempty gate, perform the divisibility rounding in equation (5),
and finish equation (6)/averaging before constructing the aperiodic core.

Ordinary GMO still needs the full maximal-replacement contradiction and the
remaining Lemmas 2--5 consequences needed to eliminate the ambient and
subgroup ordinary providers.  The five providers in `GAOARFinal` therefore
remain in place at this checkpoint.
