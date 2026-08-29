# Milestone M62: crossed DGM sets, full Definition 1 chain, and signed quotient lifting

Status: `LEAN_CHECKED` for the new proof infrastructure.  The 13-page PR #7
theorem remains `LEAN_CONDITIONAL`; M62 does not claim the generalized DGM
theorem, Theorem E, Theorem 2.1, or signed Theorem 1.1.

M62 advances all three remaining source proofs and records one necessary
source-fidelity correction openly.

- `PGDGMCore` now defines the source crossed coset slices, proof-relevant
  two-step pattern extensions, the crossed pair base and `D12`.  It proves
  that `D12` is nonempty and is contained in the exact pattern spectrum.  The
  next DGM obligations are the `H12` saturation, the `D1/D2` subsets and
  stabilizer chain, followed by the final four-inequality contradiction.
- `PGGMOTheorem21` now contains the complete finite recursive skeleton of
  dissertation Definition 1: `Lambda_r/F_r/Upsilon_r/G_r/H_{k_(r+1)}` is
  represented by indexed extremal states and transitions, and a genuine new
  extremal state exists at every finite depth.  The partition is not held
  fixed across the recursion.  The remaining work is the doubled-exception
  exchange and factor-form Lemmas 1--5, which must turn this chain into the
  exact Theorem E output.
- The former Lean encoding of Theorem E's coefficient was found false at
  `N=0`: `(N - 1) * n + e + 1` performs natural-number truncation before the
  multiplication.  It has been corrected to the source-faithful
  `(N * n + e + 1) - n`.  A kernel-checked regression records that for
  `N=0, n=2, e=2` the correct coefficient is `1`, while the old expression is
  `3`.  All dependent terminal and trivial-period lemmas were reproved.
- `PGGMOTheorem11` proves the odd-order singleton characterization
  `{x,-x}={x} iff x=0` and the full Step 5 pullback of a quotient whole-block
  concentration certificate.  The subgroup is the comap, the center is
  lifted by a quotient section, occurrence labels are transported by an
  equivalence, and the exception bound is preserved through the third
  isomorphism theorem.  Signed Corollary 1.2 remains separate: replacing its
  plus-minus Davenport threshold by the ordinary Davenport threshold would
  silently strengthen the manuscript hypothesis and is explicitly rejected.

The three modules build together in 8707 tasks.  The full `GaoLean` target
builds in 8753 tasks.  Forbidden declaration scans are clean; printed
dependencies of completed declarations contain only `propext`,
`Classical.choice`, and `Quot.sound`.
