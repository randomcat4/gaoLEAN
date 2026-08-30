# GAO-AR final Lean run

## Frozen target

For every odd prime `q` and every `r >= 2`, prove

`E((C_q^r) semidirect_{-1} C_2) = 2 q^r + r(q-1) + 1`,

where the exact product-one block has occurrence-cardinality `2 q^r`.

The executable Lean statement is `GaoLean.GAOARV1Statement` in
`GaoLean/GAOARStatements.lean`.

## Source

The frozen source is the final GAO-AR manuscript in the sibling `gao0823`
repository.  That repository is read-only for this run.  All new formal work
is made in `gaoLEAN`.

## Completion criterion

The run is complete only when the exact frozen statement is either:

1. proved by a Lean term whose remaining dependencies are explicitly named
   published-theorem provider parameters; or
2. refuted by a checked counterexample to the same statement.

Compiling a definition, proving a conditional surrogate, or proving only one
branch does not count as completion.
