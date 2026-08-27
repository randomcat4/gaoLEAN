# Milestone M59: occurrence setpartitions and the exact DGM boundary

Status: `LEAN_CHECKED` for the new infrastructure; the 13-page theorem remains
`LEAN_CONDITIONAL` at the GMO source theorem.

This milestone opens the previous DGM/setpartition placeholder without
weakening any manuscript provider.

- `PGIteratedKneser` proves the finite-list Kneser inequality
  `Σ |B_i+H| + |H| ≤ |Σ B_i| + r|H|` by quotienting by the final
  stabilizer and lifting the aperiodic inequality.
- `PGSetpartitionOccurrences` proves the labelled setpartition criterion:
  if every value occurs at most `n` times and `n ≤ |S|`, all occurrences can
  be partitioned into exactly `n` nonempty cells, with no repeated value in a
  cell.  It also connects the full cell sumset to the ordinary exact-`n`
  spectrum without collapsing repetitions.
- `PGDGMCore` defines the literal exact-`n` layer spectrum and the capped
  quotient-layer multiplicity in the DeVos--Goddyn--Mohar formula.  The
  `n=1`, `n=|P|`, quotient transport, and the reduction of general DGM to its
  aperiodic core are checked.  The portion-minimality proof of
  `AperiodicDGMSetpartitionCore` remains unproved and explicit.
- `PGPlusMinusSetpartition` proves that the manuscript's labelled signed
  spectrum is exactly the DGM layer spectrum for the repeated block list
  `{x,-x}`.
- `PGGMOOrdinarySource` and `PGGMOPlusMinusSource` give bidirectional,
  occurrence-faithful translations between the published source corollaries
  and the five consumer providers.  `PGGMOSourceAssembly` mechanically
  replaces the five fields by the corresponding source theorem families.

An independent semantic audit found a second necessary boundary which must
not be hidden: the DGM cardinal inequality alone does not yield the full
Corollary 1.3 concentration data.  For a signed block `{x,-x}`, quotient-layer
multiplicity records that at least one sign lies in a quotient coset; the
source conclusion requires the source occurrence and both signs to lie in
specified common cosets.  Thus the structural setpartition theorem (paper
Theorem 2.1) and the induction proving Theorem 1.1 remain necessary after DGM.
`PGDGMStructuralGap` kernel-checks the concrete `ZMod 5` single-layer witness
showing why that stronger direct implication is false; it is explicitly not a
counterexample to DGM or GMO.

All completed new declarations print only `propext`, `Classical.choice`, and
`Quot.sound`.  No `sorry`, `admit`, project `axiom`, `unsafe`, or
conclusion-shaped provider inhabitant is introduced.
