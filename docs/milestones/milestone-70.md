# Milestone 70 — Scherk r=1, ordinary Lemma 2, and unified DGM Xi

Date: 2026-08-27

Status: **LEAN-CONDITIONAL**.  This checkpoint proves additional source
lemmas but does not yet eliminate the five final GMO providers.

## Scherk / Proposition 1.3

- Added `GaoLean.PGScherk` with the finite-set theorem
  `card_add_sub_one_le_of_add_ne_add_erase`.
- The theorem assumes only an additive commutative group and decidable
  equality.  It does not assume a finite ambient group, aperiodicity, or a
  trivial stabilizer.
- The proof extracts a unique representation from strict erase change, uses
  fibres of the actual sumset stabilizer and reflection, and combines the
  resulting saturation-growth estimate with `Finset.add_kneser`.

## Ordinary GMO

- Completed the dissertation's constructive Lemma 2.
- The proof uses the full Lemma 1 representative, exact erased-tail and
  without-cell identities, the new Scherk theorem for equation (3.3), and
  the previously verified natural-number closing calculation.
- Its signature uses a weak factor form plus condition III.  It does not
  assume the unrelated condition II.
- Split the source-facing Theorem E output from its actual-stabilizer
  normalization.  The literal source output now records subgroup periodicity
  `H <= stabilizer`, so the trivial-group/CDT conclusion used by Lemma 3 is
  expressible without pretending that the trivial subgroup is the actual
  stabilizer.

## DGM

- Unified the weighted Xi estimate before the coarse cosets are known to be
  distinct: the same-coset branch counts one exceptional fibre, while the
  distinct branch counts two.
- Removed the `hne` premise from the concrete equation (4) assembler.
- Added proof-relevant decomposition from an arbitrary feasible choice and
  infeasible intersection-union transform to the canonical two-step pattern,
  crossed representatives, nonempty `D12`, and the first crossed tail.
- Replaced an over-strong literal-membership gate for the second crossed tail
  by the source-faithful quotient-layer membership condition.

The numeric proof that forces the second crossed tail to be nonempty and the
two coarse cosets to be distinct is still open.  Minimal-convergent extension,
`DGMPortionExtensionProperty`, and the aperiodic core are also still open.

## Verification

- Integrated hashes:
  - DGM: `875f068c4ab1b6e253b395549b13ce022f13925f4cdbf0db4b2775ab74356eef`
  - ordinary GMO: `10204107cd6161ab161491278bd65d1116dcdfe2e50c46b44f3d9a2c931ff49c`
  - Scherk: `93459698cd395f1e33d4b84f9058cdf4f92f3232c0617c9afd1eed203b8f9dae`
  - signed GMO: `f110e76710410547ae7215ec4c130a8a88ff3bf04b23b9e211694911f55d73f4`
- Sequential joint build: **8708/8708 pass**.
- Axiom output remains limited to `propext`, `Classical.choice`, and
  `Quot.sound`.
