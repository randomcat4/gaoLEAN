# Milestone P5b1: zero bases, strict induction, and translation pullback

Date: 2026-08-24 (America/New_York).

Status: `LEAN_CHECKED` for unconditional internal combinatorics and the
strict-induction scheduler; `LEAN_CONDITIONAL` for both zero bases on the
explicit GJM-style small-Davenport bound.  PG-O3 remains `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:568-601`: greedily remove product-one blocks, bound the
  product-one-free remainder, pad by unused identity occurrences, and in the
  `ZR` base use the quotient guard to force the core rotation-only.
- `A-R6/proof.md:603-615`: prove fixed-source `RC` and arbitrary-`X` `ZR`
  simultaneously; every recursive call uses `H<K`.
- `A-R6/proof.md:545-566`: translate rotation coordinates, recurse at `H<K`,
  and pull an exact `2Q` all-rotation block back using `Q • alpha = 0`.

## Compiled closure

- `PGBase.lean` chooses a maximum occurrence-labelled product-one core and
  proves its complement product-one-free.  An explicit
  `SmallDavenportProductOneFreeAtMost G D` interface bounds that complement.
- Identity rotations are exactly `rotationOccurrencesIn s bottom`; they and
  nonidentity labels partition the source.  Disjoint product-one selections
  concatenate, and identity padding reaches exact cardinality `2Q`.
- At the zero quotient, the no-reflection guard forces every product-one core
  drawn from nonidentity labels to be all-rotation.  Hence both `RC_S(0)` and
  every `ZR_A(X,0)` follow from the small-Davenport interface plus
  `Q=|A|`, `D <= b-Q+2`, and the source length equation.
- `PGInduction.lean` proves `H<K` strictly lowers finite subgroup cardinality,
  checks well-founded simultaneous induction, and packages the two zero bases.
  Only nonzero proper-subgroup RC/ZR step obligations remain.
- `PGTranslation.lean` proves inverse translation on rotations and pulls a
  product-one witness back on the exact same selection when its size is `2Q`
  and `Q • alpha=0`.

## Exact remaining boundary

GJM must instantiate the small-Davenport interface.  GMO prescribed-length
and structural alternatives must supply the two nonzero positive-step branch
proofs, including capacity inequalities and the full/non-full spectrum split.
The list-level reindexing noted here is closed in `milestone-07.md`; this file
continues to record the earlier P5b1 boundary.
