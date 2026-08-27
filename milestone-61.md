# Milestone M61: faithful pattern measures and finite GMO maximization

Status: `LEAN_CHECKED` for the new proof infrastructure.  The 13-page PR #7
theorem remains `LEAN_CONDITIONAL`; this milestone does not claim the DGM
pattern theorem, GMO Theorem E, or signed Theorem 1.1.

M61 replaces two tempting but insufficient shortcuts by source-faithful
formal structures.

- `PGDGMCore` now represents quotient patterns by their exact selected-layer
  multiplicities and defines the corresponding proof-relevant pattern
  spectrum.  It proves the intersection--union transport of realizing
  choices, exact preservation of raw/capped incidence, and the strict
  decrease facts for the four-coordinate inner measure used by the original
  minimal-counterexample proof.  The older head/tail portion reduction is
  retained as checked exploratory infrastructure, but it is no longer
  presented as a direct transcription of the source convergent argument.
  The remaining work is the generalized pattern theorem, including the
  stabilizer quotient and the `D1,D2,D12` contradiction, followed by its
  top-pattern specialization to general DGM.
- `PGGMOTheorem21` constructs an occurrence-labelled `n`-setpartition from
  every admissible seed subsequence, not only from the full source.  It proves
  finiteness of the replacement-partition search space and performs three
  genuine finite argmax selections: full sumset cardinality, stabilizer
  quotient incidence at fixed sumset, and captured outside-common-core
  occurrences at fixed previous data.  It also closes the `N=1` terminal
  arithmetic and produces the complete periodic alternative.  The source
  dissertation uses a longer iterated `Lambda_r/F_r/Upsilon_r/G_r` extremal
  chain; M61 explicitly leaves that remaining iteration open.
- `PGGMOTheorem11` proves the literal DGM bound for the signed occurrence
  setpartition, quotient aperiodicity, and the trivial-stabilizer capped count.
  In odd order it turns a whole `{x,-x}` coset certificate into a subgroup
  centre and a repetition-preserving labelled `List K`, closing the
  over-group/translation seam needed by the 13-page specialization.  The
  remaining signed work is the Davenport convolution and an arbitrary-type
  cardinal induction that handles both strict subgroups and proper quotients.

The three modules build together in 8707 tasks.  The full `GaoLean` target
builds in 8753 tasks.  Forbidden declaration scans remain clean; printed
dependencies of completed declarations contain only `propext`,
`Classical.choice`, and `Quot.sound`.
