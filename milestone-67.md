# Milestone 67 — exceptional hypotheses eliminated and ordinary audit correction

Date: 2026-08-27

Status: **LEAN-CONDITIONAL**.  General DGM and ordinary GMO are still under
construction; the five providers in the final 13-page assembly have not been
eliminated.

## DGM progress

- Added proof-relevant quotient choices that exchange an actually unused
  labelled layer while preserving the transformed pattern exactly.
- Derived the tail multiplicity bound from infeasibility of the transformed
  two-step pattern.
- Derived all three exceptional conditions for both crossed cosets, instead
  of accepting them as hypotheses.
- Exposed the resulting weighted Xi estimate directly from transformed-pattern
  infeasibility and membership of the two crossed representatives.
- Added strict divisibility rounding and subgroup-saturated cardinality
  divisibility lemmas needed by equation (5).

## Ordinary GMO progress and correction

- The occurrence-labelled replacement construction now proves the maximality
  contradiction in the index-aligned case `d < k <= q`; it moves a labelled
  occurrence, preserves cell injectivity and support, propagates quotient
  images through the Definition 1 chain, and obtains an exact `+1` incidence
  contradiction.
- This theorem is a substantial reusable subcase, but it is **not the complete
  source Lemma 1**.  The source first uses `l = min (rho + 1) q`, and the
  stabilizer-stage index must not be identified with the tail starting index.
  The earlier informal description of this checkpoint as the complete Lemma 1
  is therefore withdrawn.
- Independent source audit also identified that the current Theorem E output
  and proper-induction boundary are too strong to serve as completion
  interfaces.  They must be replaced by source-faithful factor-form Lemmas
  1--5 and an explicit proper-subgroup/source-length induction.

## Verification

- Integrated hashes:
  - DGM: `b730ead81cf9dbba4109b2e301ada58e25f6d4093682802fda7f1e09ee7ed6ad`
  - ordinary GMO: `072ea28d9cbc5458cc5d7f652606fa583b5e7d863b439462e3eac980ef35ab6a`
  - signed GMO: `f110e76710410547ae7215ec4c130a8a88ff3bf04b23b9e211694911f55d73f4`
- Sequential joint build: **8707/8707 pass**.
- Reported axioms remain `propext`, `Classical.choice`, and `Quot.sound`.
- No source theorem or final provider was weakened or silently redefined as
  complete at this checkpoint.
