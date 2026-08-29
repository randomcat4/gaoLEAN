# Milestone 27: source-level PG-GAO upper assembly

Status: `LEAN_PARTIALLY_CHECKED` overall; this internal composition slice is
`LEAN_CHECKED`.

## Scope

`GaoLean/PGSourceAssembly.lean` refines the coarse `PGGaoUpperInputs`
boundary. For each concrete source it retains only the exact external outputs
that the natural-language proof still needs:

- the ambient and quotient small-Davenport bounds;
- low- and high-reflection prescribed-length outputs in their actual regimes;
- the middle full/non-full spectrum alternative;
- ordinary-GMO providers for every auxiliary `ZR` source and signed-GMO
  providers for the fixed `RC_S` source.

`pgGaoUpperInputs_of_externalUpperInputs` constructs the middle controller
through the checked quotient extraction, channel preparation, branch
consumers, zero bases, and simultaneous strict-subgroup induction. It does not
assume a controller field. The conditional theorem
`pgGaoV1_of_externalUpperInputs_and_smallDavenportWitness` then composes this
upper package with the checked occurrence-sensitive lower construction.

## Build and audit

- Initial single-file build: exit 0 with one linter warning that exposed an
  unused presentation parameter; the parameter was removed.
- Rechecked single file: exit 0 with no linter warning in the new module.
- Full `lake build`: exit 0, `Build completed successfully (8698 jobs)`.
- The first unified-audit launch did not execute because the permission review
  timed out. The permitted retry ran and exited 0.
- New declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Declaration scan for `sorry`, `admit`, declaration-level `axiom`, and
  `unsafe`: no matches, normalized exit 0.

## Remaining boundary

The new source package is still a proposition parameter. Formal production of
its fields from Troi--Zannier/GJM/Olson and ordinary/signed GMO is not yet in
Mathlib or this project. No unconditional `PGGaoV1` proof is claimed.
