# Milestone 68 — actual tail stabilizer and source-faithful ordinary boundary

Date: 2026-08-27

Status: **LEAN-CONDITIONAL**.  This is a verified structural checkpoint, not
the completed formalization of the 13-page PR #7 manuscript.

## General DGM

- Formalized saturation of every tail layer by a subgroup, including
  nonemptiness, quotient multiplicity preservation, and proof-relevant
  choice lift/split lemmas.
- Proved the exact pattern-spectrum transport
  `Sigma_mu(P + L) = Sigma_mu(P) + L` for positive pattern weight.
- Derived the saturated tail's actual stabilizer from the stabilizer of the
  crossed sum, so Claim 1 no longer receives `stab(tail + L) = L` as a
  provider.
- Converted a genuine smaller saturated-tail `DGMPatternBound` into the
  original tail Xi bound and then into the three-summand Kneser inequality.
- Corrected the source-equation labels: the strict convergence inequality is
  equation (2); the three-summand Kneser connector is equation (3).
- The positive-weight hypothesis remains explicit.  The `ell = 2`, `k = 0`
  boundary has not been hidden by natural-number truncation and still needs
  a separate proof.

## Ordinary GMO

- Replaced the previously over-strong projected completion boundary with
  source-facing input, admissibility, output, and statement structures that
  retain initial sumset inclusion, distinguished anchors, and equality with
  the actual stabilizer.
- Removed unconditional `N >= 1` and global no-doubled assumptions from the
  source output.  Only the valid implications `exists unused -> N >= 1` and
  `N = 0 -> support = univ` are retained.
- Constructed the literal admissible `Lambda_0` maximizer and source chain at
  arbitrary depth.
- Added zero-based tail/leading indices and source-shaped `WeakFactorForm`
  and `FactorForm` records, including conditions I--V and the exact
  parenthesized natural-number deficits.
- The source-chain monotone replacement, `l = min ...` Lemma 1, and Lemmas
  2--5 remain to be proved.

## Verification

- Integrated source hashes:
  - DGM: `d994cdacf2479624a0d03b29ef8b58f2e73d9a19f4ee1664efb7d5cfaeb7dbc4`
  - ordinary GMO: `db79f9644e84845b521418c6a9ae01d2066f89bbff2179fbb7cd4e9abd6fdd63`
  - signed GMO: `f110e76710410547ae7215ec4c130a8a88ff3bf04b23b9e211694911f55d73f4`
- Sequential joint build: **8707/8707 pass**.
- Axiom output remains limited to `propext`, `Classical.choice`, and
  `Quot.sound`.
- The five final GMO providers remain present and are not reported as
  eliminated.
