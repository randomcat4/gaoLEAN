# Verification rounds

## Round 1 — 2026-08-26

- Audited the final manuscript theorem and its proof DAG.
- Froze `GAOARV1Statement` without an upper-bound claim.
- Checked the represented group cardinality.
- Server build: `GaoLean.GAOARStatements`, 8660 jobs, successful.
- No paper-specific axiom or placeholder introduced.

## Round 2 — 2026-08-26

- Proved every below-threshold counterexample from an explicit Olson
  ordinary-Davenport equality input.
- Server build: `GaoLean.GAOARLowerBound`, 8689 jobs, successful.
- Axiom print contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Froze the occurrence-labelled `{+1,-1}` specialization of GMO Corollary
  1.3, retaining both coset conditions and the exact concentration count.

## Round 3 — 2026-08-26

- Closed the rank-two low-reflection branch `a ≤ 1` from the explicit
  ordinary-GMO provider.
- Proved the manuscript-internal bound `D_±(F_q²) ≤ q`: binary subset-sum
  collision for `q ≥ 5`, and linear dependence over `F₃` for `q = 3`.
- Closed the rank-two high-reflection branch `a ≥ 2q` from the explicit
  weighted-GMO provider, with the internal plus-minus bound no longer an
  assumption.
- Server build: `GaoLean.GAOARRankTwo`, 8687 jobs, successful.
- Axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
  the middle range remains explicitly open.

## Round 4 — 2026-08-26

- Transported the exact structural GMO alternative from the labelled
  rotation-coordinate sequence back to original source occurrences.
- In the full-spectrum branch, combined the selected rotations with a
  balanced even reflection choice and closed the exact `2q²` ordering.
- In the non-full branch, preserved the proper subgroup and both weight-coset
  conditions, then derived the source-labelled subgroup concentration.
- Specialized all numerical gates for `2 ≤ a ≤ 2q-1`; the remaining rank-two
  obligation is exactly the `K=0`/line-completion part of the manuscript.

## Round 5 — 2026-08-26

- Closed the `K = 0` non-full middle leaf from the explicit generalized-
  dihedral small-Davenport provider and the existing checked identity-padding
  construction.
- Proved internally that every nonzero proper additive subgroup of `F_q²` is
  a one-dimensional `ZMod q` subspace, hence both it and its quotient have
  cardinality `q`.
- No classification assumption was added; the remaining rank-two branch is
  now literally the manuscript's one-dimensional line completion.

## Round 6 — 2026-08-26

- Proved the general internal comparison `D_±(A) ≤ |A|` by transporting an
  ordinary zero-sum subsequence with all signs positive.
- Built an occurrence-faithful coordinate sequence for rotations lying in a
  fixed rank-two line; source occurrence labels are retained through the
  subtype transport.
- Closed the manuscript's `s ≤ q` line leaf from the explicit ordinary-GMO
  provider on the prime-order line.
- The only remaining line leaf is `s > q`: the dihedral quotient extraction
  followed by the second structural GMO application.

## Round 7 — 2026-08-26

- Formalized the manuscript's Cauchy--Davenport proof of the prime dihedral
  reflection-block lemma, retaining repeated source occurrences.
- Proved internally that every `q+1`-term sequence over `D₂q` has a nonempty
  product-one subsequence, hence `d(D₂q) ≤ q`.
- Transported the result through an arbitrary prime-cardinality additive
  quotient and back to the original labelled source.
- Combined it with the existing maximum reflection-containing quotient block
  construction; the literal complement is now checked to have at most `q`
  occurrences.
- Axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Round 8 — 2026-08-26

- Proved a literal first-reflection insertion identity: positive rotations
  are inserted before the lifted quotient word and negative rotations after
  its first reflection, so their signed sum cancels the kernel defect.
- Transported the second structural-GMO selection occurrence-by-occurrence
  from the line-valued coordinate list to the original source, checking
  disjointness, exact cardinality, and multiset equality.
- Closed the non-full second-GMO branch: a proper subgroup of the prime-order
  line is proved internally to be zero, after which the existing checked
  identity-padding base applies.
- Derived the source-shaped quotient small-Davenport interface from the
  genuine small-Davenport theorem on the quotient group.
- Closed the complete `s > q` line leaf from the prime dihedral block lemma,
  including `|R| ≤ q`, `τ ≥ q-1`, `m ≥ |K|`, and the GMO threshold.
- Server module and whole-repository build succeeded (8725 jobs).  The main
  line theorem's axiom print contains only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Round 9 — 2026-08-26

- Connected the first middle-range GMO output to the zero-subgroup base and
  the two concentrated-line leaves without a residual controller assumption.
- Proved `rankTwo_middle_upper` for the complete range `2 ≤ a ≤ 2q-1`.
- Dispatched the low, middle, and high reflection ranges to obtain the complete
  `rankTwo_upper` theorem at length `2q² + 2(q-1) + 1`.
- All cited literature inputs remain explicit proposition parameters; no
  condition was strengthened or hidden during assembly.
- Whole-repository server build succeeded (8726 jobs).  Both assembled
  theorem axiom prints contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
