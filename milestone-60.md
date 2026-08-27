# Milestone M60: DGM portions and faithful GMO theorem boundaries

Status: `LEAN_CHECKED` for the new reductions and transport lemmas.  The
13-page PR #7 theorem remains `LEAN_CONDITIONAL`; this checkpoint does not
claim the DGM extension lemma, ordinary GMO induction, or signed GMO
induction.

This milestone advances the three remaining additive-combinatorics proof
lines without adding an axiom, provider inhabitant, or weakened manuscript
conclusion.

- `PGDGMCore` now defines proof-relevant exact-layer choices, raw capped
  multiplicities, the canonical DGM initial portion, and arbitrary DGM
  portions.  It proves the quotient-tail construction, finite
  minimum-stabilizer selection, trivial-stabilizer quotient transport, and
  the full mechanical implication
  `initial portion + extension property -> next aperiodic DGM bound`.
  The extension property explicitly assumes that the final exact-layer
  spectrum is aperiodic; omitting this hypothesis is false already in
  `ZMod 2`.  The remaining mathematical load is the general-setpartition
  intersection--union / `D1,D2,D12` extension argument and its final strong
  induction packaging.
- `PGGMOTheorem21` gives an occurrence-faithful statement of GMO Theorem 2.1
  and a literal Theorem E interface: replacement occurrences are labelled,
  cells are value-injective, and the exceptional count is over the whole
  source sequence.  Lean closes the trivial and full stabilizer branches,
  proves that `N = 1` makes the common core one literal subgroup coset, and
  derives the complete periodic/concentration output.  The remaining source
  work is Theorem E's maximal replacement-setpartition existence and the
  proper-nontrivial subgroup induction of Theorems 2.4/2.5.
- The proper-subgroup induction boundary was corrected after a source audit:
  it now includes the hypothesis `d*(G) <= n` and may return a new
  replacement partition.  It does not incorrectly force the initial
  Theorem E partition to survive the paper's rearrangement/maximality step.
- `PGGMOTheorem11` starts the direct signed proof of Theorem 1.1.  It proves
  exact signed-spectrum transport through arbitrary additive homomorphisms
  and quotients, closes the full-stabilizer branch, and converts a whole
  `{x,-x}` block certificate into the three required source/positive/negative
  coset facts.  Ordinary Theorem 2.1 is no longer an assumed premise of the
  signed induction engine.  The remaining work is the proper-stabilizer
  quotient lift, the trivial-stabilizer DGM count, and the signed Davenport
  subgroup--quotient convolution.

Independent finite-model checks found no counterexample to the corrected DGM
extension property in exhaustive cyclic tests previously recorded for small
orders, an exhaustive `ZMod 2 x ZMod 2` two-tail check (392 aperiodic inputs,
428 portions), or additional random noncyclic checks.  These checks are only
regression evidence and are not treated as proof.

All completed declarations in these modules are required to build under Lean
4.32.  The forbidden-declaration scan covers `sorry`, `admit`, project
`axiom`, `unsafe`, and `native_decide`; printed theorem dependencies may only
contain `propext`, `Classical.choice`, and `Quot.sound`.
