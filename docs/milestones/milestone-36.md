# Milestone 36: cyclic raw/padded capacity-entry falsification

Status: `LEAN_FULLY_DISPROVED` for the frozen unconditional raw and padded
capacity-entry assertions.  This is a negative interface result; it does not
disprove any Gao constant formula or the conditional fixed-target backend.

## Frozen family

For `n≥3` and `0≤t≤n-1`, Lean encodes the labelled word over
`(ZMod n)⋊_{-1}C₂`

`0^[2n-1-t] 1^[n-1] ρ`

as a list of distinct source positions, even when values repeat.  Its
canonical padded regrouping is

`0^[2n] 1^[n-1] ρ`.

## Checked conclusions

- The raw word has exact length `3n-1-t`.
- It has no product-one occurrence selection of cardinality `2n`.
- For every proper additive subgroup `K<ZMod n`, the raw capacity is exactly
  `2n-1-t`, strictly below the frozen raw `+2` gate.
- For every such `K`, the padded capacity is exactly `2n`, strictly below the
  padded `+2` gate.

The target-avoidance proof first shows that a product-one selection from a
rotation prefix plus one reflection pulls back to an additive zero-sum
selection of the same cardinality.  In the cyclic source, any `2n` selected
rotations must contain between one and `n-1` generator copies, whose sum
cannot vanish in `ZMod n`.  The capacity proof shows a proper subgroup cannot
contain the generator `1`, so only the identity block contributes.

## Fidelity boundary

Natural-language source:
`gao0824/research/sequence-entry-2026-08-24/RESULT.md`.  The module proves the
raw and padded universal entry statements false on the full infinite family.
It does not claim the padded word avoids the target (it contains `2n`
identities), and it does not weaken or contradict the PR #10 backend once a
valid capacity entry is actually supplied.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Final single-file check: exit 0 with no diagnostics.
- Full build, unified axiom audit, forbidden-declaration scan, and scoped
  whitespace check are recorded in `../build-log.md`.
