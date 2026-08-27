# Milestone M63: DGM stabilizer chain and occurrence-faithful Lemma 1 exchange

Status: `LEAN_CHECKED` for the new proof infrastructure.  The 13-page PR #7
theorem remains `LEAN_CONDITIONAL`; M63 does not claim the generalized DGM
theorem, ordinary Theorem E/2.1, or signed Theorem 1.1.

- `PGDGMCore` now defines the literal `H12` stabilizer and its finite
  `D1/D2` saturations.  It proves `D1,D2` remain inside `D12`, identifies the
  bundled `H12` with the finite `addStab`, and closes the source stabilizer
  chain `H12 <= H1,H2 < H` under the exact escape hypotheses.  Quotient
  patterns now also carry a checked quotient sum and the pattern spectrum is
  proved to lie in the corresponding single quotient fibre.  The remaining
  DGM core is the `Xi` difference count and equations (1)--(5), followed by
  the final minimal-counterexample contradiction.
- `PGGMOTheorem21` now formalizes the first occurrence-labelled exchange in
  dissertation Lemma 1.  A doubled exception yields distinct source and
  target cells and a legal moved occurrence; all cells stay nonempty and
  pairwise disjoint, value injectivity is preserved, and the complete
  labelled support is equal before and after the move.  Removing the doubled
  representative leaves the source quotient image unchanged, while adding
  the missing quotient class increases the target quotient-image cardinality
  by exactly one.  The remaining Lemma 1 work is to transport these changes
  through every Definition 1 extremal stage and derive the maximality
  contradiction; Lemmas 2--5 and Theorem E/2.4/2.5 then remain.
- `PGGMOTheorem11` is intentionally held at the already checked M62 version
  in this integration checkpoint.  Its active worktree is not copied until a
  new direct-build-stable SHA is reported.  Signed Step 1 and the odd-order
  Step 6 counting closure remain open.

The three proof modules build together in 8707 tasks.  The forbidden
declaration scan is clean, and printed dependencies of completed declarations
contain only `propext`, `Classical.choice`, and `Quot.sound`.  A complete
project build is recorded in `build-log.md` before publication.
