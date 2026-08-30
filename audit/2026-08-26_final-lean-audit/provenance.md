# Provenance

- Statement and proof architecture: the self-contained manuscript under
  `paper/arxiv/` in this repository.
- Existing formal components: public `randomcat4/gaoLEAN` repository.
- Lean verification environment: Lean 4.32.0, Lake 5.0.0, Mathlib v4.32.0
  (`81a5d257...`) in the recorded remote verification environment.
- This run does not edit the source manuscript repositories.

Each formal declaration must be traceable either to a manuscript obligation,
an already proved local lemma, Mathlib, or a named external provider.

## GMO source check

The provider `PlusMinusGMOStructuralProvider` follows Grynkiewicz--Marchan--
Ordaz, Corollary 1.3 (arXiv:0903.2810v1): full `n`-term weighted spectrum, or
a proper subgroup `K`, source coset `alpha+K`, common weight coset `beta+K`,
and at least `|S|-|G/K|+2` retained occurrences.  The separate existence
provider follows Corollary 1.2.
