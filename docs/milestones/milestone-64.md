# Milestone M64: DGM Xi cover, Definition 1 monotonicity, and odd signed induction

Status: `LEAN_CHECKED` for the new proof infrastructure.  The frozen 13-page
PR #7 theorem remains `LEAN_CONDITIONAL`; M64 does not claim General DGM,
ordinary Theorem E/2.1, or signed Theorem 1.1.

- `PGDGMCore` now contains literal finite subgroup and coset carriers, exact
  coset cardinality, single/pair slice saturations, the missing sets `X'` and
  `Y'`, their distinct-coset disjointness, and the two coset-cover cardinal
  inequalities.  It also proves the tail capped-multiplicity monotonicity and
  a nontruncated two-leading-layer Xi gain identity.  Once the source's
  strict bounds (4),(5) are available, `dgmFinalCosetCoverContradiction`
  closes the final cover contradiction mechanically.
- The generalized pattern endpoint is now connected completely to the frozen
  `GeneralDGMSetpartitionTheorem`: top quotient patterns, exact-choice
  realization, top capped multiplicity, and finite/bundled stabilizer cards
  are all checked.  For the minimal-counterexample step, intersection--union
  now gives unconditional lexicographic inner-measure descent and proves
  `Xi_K(A') <= Xi_K(A)`.  Thus the remaining General DGM mathematics is
  concentrated in the weighted Xi claim and the strict (1)--(5) derivation.
- A source-fidelity audit rejected and removed an invalid shortcut: the four
  displayed non-strict natural-number inequalities alone admit equality
  assignments and do not imply the needed strict bound.  The formal proof
  must retain the strict information from (3)/the nonconvergent case, or the
  corresponding divisibility-rounding fact, while deriving (4),(5) from
  (1),(2) and the Xi claim.  No false `omega` lemma is kept.
- `PGGMOTheorem21` proves that the doubled-exception move changes total
  quotient incidence by exactly `+1`, and that an F-maximal transition
  forbids such a candidate.  A recursive `MonotoneReplacement` certificate
  now carries admissibility through the entire Definition 1 chain.  The
  remaining concrete Lemma 1 bridge is equation (3.1): derive every required
  tail and quotient-image inclusion from the actual remove/insert move and
  `H_k <= H_{k_i}`, then obtain the final (3.2) contradiction.
- The concrete tail machinery now handles arbitrary prefix/suffix splits:
  deleting a doubled representative from the distinguished cell preserves a
  periodic reduced tail, and the moved tail contains the old tail.  The
  natural-number closing calculation of Lemma 2 is also checked with its
  positivity and `n-rho >= 2` hypotheses explicit.
- `PGGMOTheorem11` now closes the odd structural Corollary 1.3 Steps 4 and 5
  by strong induction over `Nat.card` across arbitrary subgroup and quotient
  types.  Proper-quotient paired concentration is pulled back with all
  occurrence labels and the exact exception count.  The trivial-stabilizer
  branch is reduced to and then proves the elementary
  `OddSignedCappedMultiplicityEstimate`: zero occurrences contribute once,
  nonzero odd-order `{x,-x}` cells contribute twice, truncation is handled by
  finite-sum lemmas, and DGM's singleton-stabilizer capped sum equals raw
  signed-layer incidence.  The remaining signed obligation is Corollary 1.2
  Step 1's iterated signed zero sums plus zero padding, followed by provider
  assembly.

The three modules build together in 8707 tasks and the complete project in
8753 tasks, all with exit code 0.  The forbidden-declaration and whitespace
scans are clean.  Completed declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.
