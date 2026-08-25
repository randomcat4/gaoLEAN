# Milestone 32: ordinary GMO low-reflection bridge

Status: `LEAN_PARTIALLY_CHECKED` overall; the transport in this milestone is
`LEAN_CHECKED`, while the ordinary GMO provider is `LEAN_CONDITIONAL`.

## Result

`GaoLean/PGOrdinaryGMOBridge.lean` freezes a source-shaped ordinary
prescribed-length GMO interface on additive sequences and proves its complete
transport to the low-reflection generalized-dihedral branch. The rotation
coordinates form an occurrence list; its positions embed injectively into the
original source. An exact selected additive block therefore becomes an exact
source selection of rotations with the same coordinate sum.

`PGGaoExternalUpperInputs` now carries
`OrdinaryGMOPrescribedLengthProvider A D` and no longer carries an arbitrary
low-regime `LowReflectionTargetOutput` for every source.

## Fidelity boundary

- Natural-language anchor: `A-R6/proof.md:205--216`.
- The GMO target is retained as `k • z`; it is not assumed to be zero.
- Repeated coordinate values remain distinct because selection and transport
  are on `Fin` occurrences.
- The cited ordinary GMO theorem is not proved here and no axiom is added.
- High-reflection weighted GMO, middle spectrum/GMO, and ambient/quotient
  small-Davenport provider existence remain external.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- New-module build: exit 0, 8670 jobs.
- Full build: exit 0, 8702 jobs.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`,
  `Quot.sound`.
- Forbidden declaration scan: no matches, normalized exit 0.
- Scoped whitespace check: exit 0.

## Exact next blocker

Formalize the published ordinary GMO theorem itself against
`OrdinaryGMOPrescribedLengthProvider`, or perform the analogous
occurrence-faithful signed-pair transport for the high-reflection branch.
