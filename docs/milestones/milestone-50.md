# Milestone M50: Davenport subgroup--quotient convolution

Status: Lemma 5.2 is `LEAN_CHECKED`; the full 13-page manuscript remains
`CRITICAL_GAPS / LEAN_CONDITIONAL`.

`GaoLean/PGDavenportConvolution.lean` reconstructs the paper's internal
Davenport concatenation argument without taking the desired inequality as an
input.  It proves exact-threshold monotonicity, supplies a canonical exact
ordinary Davenport value for each finite additive group, and implements the
prefix/suffix split using occurrence labels so repeated values are never
collapsed.

For an additive subgroup `K <= A`, the construction lifts a zero-sum-free word
of length `D(A/K)-1` through a fixed quotient section and appends a zero-sum-
free word of length `D(K)-1`.  Any hypothetical ambient zero sum would either
give a nonempty quotient zero sum in the prefix or, after the prefix is forced
empty, a nonempty zero sum in the suffix.  Hence the concatenated word is
zero-sum-free and minimality yields

`D(K) + D(A/K) <= D(A) + 1`.

`GAOARFinal` now constructs subgroup and quotient constants canonically and
derives this inequality internally.  No frozen quantifier or target was
weakened.  Proposition 3.1, Olson, GJM, and GMO remain explicit unclosed
boundaries.

Server verification used Lean 4.32.0 / Mathlib v4.32.0.  The target module
completed 8688 jobs and the full repository plus unified axiom audit completed
8737 jobs, all with exit code 0.  The three new audited declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, project
axiom, `sorry`, `admit`, `unsafe`, or `native_decide` was found.
