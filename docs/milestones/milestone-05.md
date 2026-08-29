# Milestone P5a: faithful quotient guard and strict-subgroup transport

Date: 2026-08-24 (America/New_York).

Status: `LEAN_CHECKED` for this internal controller interface.  PG-O3 and
PG-GAO-v1 remain `NOT_FORMALIZED`.

## Frozen source statements

- `A-R6/proof.md:332-344` defines `ZR_A(X,K)` using the quotient occurrence
  sequence containing every reflection and every rotation outside `K`, and
  forbids a reflection-containing product-one occurrence subsequence.
- `A-R6/proof.md:545-554` translates rotation occurrences by `-alpha`, descends
  to `H<K`, projects a hypothetical block to `A/K`, deletes rotations from
  `K/H` that become identities, and retains the reflection.

## Compiled closure

- `PGQuotient.lean` constructs `G(A) -> G(A/K)` and `G(A/H) -> G(A/K)`, proves
  their factorization, and characterizes precisely which elements become the
  identity.
- `PGGuard.lean` defines the guard on original occurrence labels, proves its
  carrier is exactly “reflection or rotation outside K”, and proves equivalent
  list-facing and generic occurrence-function formulations.
- A product-one block modulo `H` maps to one modulo `K`; labels whose images
  are identities are filtered out, while a reflection label provably survives.
- Translating rotation values by `-alpha` for `alpha in K` is invisible modulo
  `K`, preserves rotation/reflection type, and combines with `H <= K` to yield
  the exact recursive guard transfer on the original list's occurrence type.

No value set is used for selection, so repeated equal entries remain distinct.

## Verification boundary

The strict simultaneous induction, subgroup-measure decrease, capacity count,
GMO non-full-spectrum output, recursive invocation, and `2|A|` pullback are not
assembled here.  External GMO/Troi-Zannier/Olson/GJM results remain absent.
This milestone introduces no theorem parameter or axiom.
