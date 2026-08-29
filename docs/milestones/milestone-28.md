# Milestone 28: ordinary Davenport lower-witness bridge

Status: `LEAN_PARTIALLY_CHECKED` overall; the lower-bound bridge is
`LEAN_CHECKED`.

## Scope

`GaoLean/PGDavenportBridge.lean` removes the last independent lower-witness
parameter from the source-level conditional PG-GAO theorem.

From `IsOrdinaryDavenportConstant A D`, Lean first proves `D>0` and obtains an
occurrence-labelled zero-sum-free additive word `w` of length `D-1`. It embeds
`w` as rotations and appends one reflection. Any product-one selection from
this lifted word has an even number of reflections; because the source has at
most one reflection, the selection is all-rotation. Prefix and `List.map`
occurrence equivalences then pull the selected rotations back to a nonempty
zero-sum selection of `w`, a contradiction.

Thus `smallDavenportWitness_of_isOrdinaryDavenportConstant` mechanically
constructs the exact length-`D` group witness used by identity padding.
`pgGaoV1_of_externalUpperInputs_and_isOrdinaryDavenportConstant` now consumes
the frozen ordinary Davenport premise directly.

## Build and audit

- Intermediate single-file checks exited 1 while exposing and repairing the
  multiset/filter cardinality, dependent `Fin` transport, and append-source
  type boundaries. No statement was weakened.
- Final `lake env lean GaoLean\\PGDavenportBridge.lean`: exit 0, with no linter
  warnings in the new module.
- `lake build GaoLean.PGDavenportBridge GaoLean.PGSourceAssembly`: exit 0,
  8688 target jobs.
- Full `lake build`: exit 0, `Build completed successfully (8699 jobs)`.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Declaration scan for `sorry`, `admit`, declaration-level `axiom`, and
  `unsafe`: no matches, normalized exit 0.

## Remaining boundary

The lower construction now follows solely from the frozen ordinary Davenport
premise. The remaining conditional inputs are upper-side: `D≤|A|`, oddness of
`|A|`, ambient/quotient small-Davenport bounds, low/high/middle source outputs,
and ordinary/signed GMO providers. No unconditional `PGGaoV1Statement` proof
is claimed.
