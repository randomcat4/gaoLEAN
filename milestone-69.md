# Milestone 69 — strong-IH DGM Claim 1 and complete ordinary Lemma 1

Date: 2026-08-27

Status: **LEAN-CONDITIONAL**.  The local source lemmas below are verified, but
General DGM, ordinary GMO Theorem E/2.4/2.5, and the final five-provider
elimination are not yet complete.

## DGM

- Added a card-first `DGMPatternAtMeasure` relation across subgroup and
  pattern-weight types.
- Proved that an escaping saturated tail has strictly smaller spectrum
  cardinality, so the strong induction hypothesis is invoked on a genuinely
  smaller instance.
- Constructed Claim 1 from that strong induction result and the automatically
  derived actual tail stabilizer; no Claim 1 provider remains.
- Added a disjoint weight-zero base for `ell = 2`, avoiding use of the
  positive-weight saturation theorem at `k = 0`.
- Derived the source-shaped equation (3) from Claim 1.
- Preserved both Kneser losses in the three-summand strict Xi arithmetic:
  the connector uses `2 * |L|`, not one copy of `|L|`.
- Proved the abstract equation (4)/(5) divisibility-rounding connectors.

The crossed-data instantiation is still open: the code must generate the
actual equation (4)/(5) inputs, handle equal versus distinct coarse cosets,
establish the crossed nonempty gates, and turn the resulting contradiction
into a strict `DGMPortion` extension.  `DGMPortionExtensionProperty` and
`AperiodicDGMSetpartitionCore` therefore remain uninhabited definitions.

## Ordinary GMO

- Completed the constructive source Lemma 1, rather than only the earlier
  index-aligned subcase.
- The proof uses `l = min rho q`, propagates the source-chain replacement
  through every extremal stage, preserves the literal `Lambda_0` sumset and
  distinguished anchors, and proves nonperiodicity of the erased minimum
  tail.
- If the doubled representative is an anchor, the proof chooses an
  anchor-safe representative in the same quotient class while preserving
  doubledness and the exception data.
- Factor condition (I) rules out `q < rho`; hence the minimum tail is the
  `rho` tail and the full Lemma 1 conclusion follows.

Lemmas 2--5 and the proper-subgroup/source-length induction are still open.

## Verification

- Integrated hashes:
  - DGM: `58ca6e19bbd1fe9dcbbd976abcdf8514866a75c042f360487e578853408bc703`
  - ordinary GMO: `a26ba5a0f93c4b212bc6110a50ceea5680dc253c9bc74268a7f189f26d8cd8b9`
  - signed GMO: `f110e76710410547ae7215ec4c130a8a88ff3bf04b23b9e211694911f55d73f4`
- Sequential joint build: **8707/8707 pass**.
- Axiom output remains limited to `propext`, `Classical.choice`, and
  `Quot.sound`.
