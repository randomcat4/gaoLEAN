# Milestone M57: finite GMO spectra and stabilizers

Status: `LEAN_CHECKED`; the 13-page theorem remains `LEAN_CONDITIONAL` solely
at the GMO source theorem.

`GaoLean/PGGMOSpectrum.lean` defines the ordinary and `{+1,-1}` exact-`n`
spectra as finite subsets of the ambient group. Membership is expressed with
the same source-position selections used throughout gaoLEAN, so repeated
values are never collapsed before selection.

The file proves that the manuscript-facing `OrdinarySpectrumFull` and
`PlusMinusSpectrumFull` propositions are equivalent to the corresponding
finite spectrum being the entire group. When `n ≤ |S|`, each spectrum is
nonempty; if it is not full, its translation stabilizer is mechanically a
proper additive subgroup.

Finally, explicit occurrence filters turn the ordinary source-coset bound and
the signed source/positive-weight/negative-weight coset bounds into the exact
`OrdinaryGMOConcentration` and `PlusMinusGMOConcentration` records consumed by
the proof. Thus no later bookkeeping remains hidden in the external source
boundary.

All audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. The unresolved step remains the substantive DGM/setpartition
large-coset theorem itself; no provider is claimed at M57. The full server
build completed 8746 jobs with exit 0.
