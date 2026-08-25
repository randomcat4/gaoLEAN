# Milestone P5b2a: translated-list recursive ZR wiring

Date: 2026-08-24 (America/New_York).

Status: `LEAN_CHECKED` for the internal occurrence transport, quotient guard,
count/capacity bridge, strict-subgroup `ZR` invocation, and exact pullback.
PG-O3 and PG-GAO-v1 remain `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:546-549`: translate every rotation of `Y` by `-alpha`, keep
  reflections fixed, and preserve length and the counts `a,b`.
- `A-R6/proof.md:551-555`: the translated list modulo `H` retains the
  no-reflection quotient guard by projection to `A/K` and deletion of kernel
  identities.
- `A-R6/proof.md:556-566`: call `ZR_A(Y^alpha,H)`, obtain exactly `2Q`
  rotations, and pull the same labelled occurrences back using
  `Q • alpha = 0`.

## Compiled closure

- `translatedSequence` is the actual mapped auxiliary list, and
  `translatedOccurrenceEquiv` is its canonical position equivalence.
- `map_selectedMultiset_pullbackTranslatedSelection` proves exact multiset
  preservation under occurrence pullback, including repeated equal values.
- `quotientNoReflection_translatedSequence_anti` upgrades the former
  unchanged-label guard theorem to the actual translated list.
- `card_rotationOccurrences_translatedSequence` and
  `card_reflectionOccurrences_translatedSequence` prove exact count
  invariance.
- `card_le_rotationOccurrencesIn_translatedSequence` sends any labelled
  source set in the affine coset `alpha+H` into the translated `H`-capacity.
- `hasAllRotationProductOneSubsequence_of_concreteZR_translatedSequence`
  performs the recursive `ConcreteZRStatement` call and exact pullback. It
  derives the guard, length, counts, and `Q • alpha=0`; only the numerical
  translated-capacity premise remains branch-specific.

## Mechanical audit

- First augmented single-file check: exit 1, due only to explicit coercion
  normalization for `Equiv.toEmbedding` and nested `Multiset.map`.
- Repaired `lake env lean GaoLean\PGTranslation.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8677 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `sorry`/`admit`/new `axiom`/`unsafe` scan: no matches (`rg` exit 1).

## Exact remaining boundary

The source must still supply the GMO full/non-full spectrum alternative, a
labelled concentrated set with its lower bound, and the arithmetic
composition (5.10)-(5.11). The full-spectrum closure and the reflection
channel are also not assembled. No external theorem has been replaced by an
axiom, and no Gao equality is claimed.
