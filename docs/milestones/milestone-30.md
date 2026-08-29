# Milestone 30: exact frozen-statement residual boundary

Status: `LEAN_PARTIALLY_CHECKED`; the conditional top-level composition is
`LEAN_CHECKED`.

`PGGaoRemainingInputs` is the exact remaining interface for
`PGGaoV1Statement`. It quantifies the frozen odd-prime p-group and ordinary
Davenport hypotheses, but asks only for:

- `D ≤ Nat.card A`;
- `PGGaoExternalUpperInputs A D`.

`pgGaoV1Statement_of_remainingInputs` composes all checked lower, parity,
controller, extraction, regime, and threshold modules into the fully
quantified frozen statement. It does not prove `PGGaoRemainingInputs`.

- First single-file check: exit 1 on a universe mismatch between the residual
  interface and the frozen statement; the universe parameter was made exact.
- Recheck: exit 0.
- Full build: exit 0, 8700 jobs.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden declaration scan: no matches, normalized exit 0.

This is not an unconditional proof of PG-GAO-v1. It is a mechanically checked
statement that the two displayed residual obligations are sufficient.
