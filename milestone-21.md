# Milestone P5b2o: reflection-containing channel

Date: 2026-08-24 (America/New_York).

Status: both post-preparation consumers and the positive fixed-source `RC`
step construction are `LEAN_CHECKED`; preparation remains
`LEAN_CONDITIONAL`. PG-GAO-v1 is `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:413-480`, equations (5.6)-(5.11).

## Compiled closure

- `ReflectionChannelFullOutput` closes an exact `2Q` balanced occurrence
  certificate using the checked literal-ordering theorem.
- The non-full branch of `ReflectionChannelAlternative` derives each
  concentrated coordinate lies in strict `H<K`, composes the exact capacity,
  and invokes smaller fixed-source `RC_S(H)` without carrying `U` or `z`.
- `concreteRCPositiveStep_of_channelPreparations` splits on the actual quotient
  guard, calling the rotation channel only in the no-reflection branch and the
  reflection channel otherwise.

## Mechanical audit

- `lake build GaoLean.PGReflectionChannel`: exit 0 (`8678` target jobs).
- Final `lake build`: exit 0, `Build completed successfully (8693 jobs)`.
- Unified axiom audit: exit 0; new theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` raw exit 1).

## Exact remaining boundary

The current full certificate deliberately hides the construction of quotient
block `U`, defect `z`, and the signed GMO output. The labelled greedy
extraction and the theorem producing `ReflectionChannelPreparation` from GMO
remain unformalized.
