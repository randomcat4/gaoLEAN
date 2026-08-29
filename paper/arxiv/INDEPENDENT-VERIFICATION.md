# Independent verification required

## Non-reliance rule

The manuscript and every source-derived instance must be checked independently.
Do **not** treat any of the following as evidence:

- the Claude revision or its revision notes;
- GPT reviews or this rewrite report;
- summaries already present in the repository;
- the existence of a compiled PDF;
- a Lean directory, partial formalization, or repository claim not accompanied
  by a complete checked theorem and an axiom/statement-fidelity audit.

A referee should not be expected to read Lean files or navigate the repository.
The PDF must stand on its own.

## Required reading order

1. Build `main.pdf` from the source with `make pdf`, then read it from beginning
   to end without consulting the audit notes.
2. Reconstruct every target-length calculation and subgroup-concentration
   inequality.
3. Read the original external results, not paraphrases in this repository.
4. Compare the five GMO calls against their exact hypotheses.
5. Only then use `PROOF-AUDIT.md` as a checklist for anything that was missed.

## Source instances that must be checked independently

- Grynkiewicz-Marchan-Ordaz, Corollaries 1.2-1.3: verify the intersection with
  `nG`, the full-spectrum alternative, the length `|S|-|G/H|+2`, and especially
  the **single common coset** `beta+H` containing `A*s` for every selected `s`.
- Godara-Joshi-Mazumdar, Theorem 1.1: verify that it gives
  `d(B semidirect C2)=D(B)` under the manuscript's conventions.
- Olson's formula for finite abelian `p`-groups and its use for subgroups.
- The bibliographic metadata and mathematical role of every cited paper.
- The explicit `C_3^2` lower-bound witness; no computer search is claimed.

## Internal checks

- `2k` reflections create `2k+1` gaps.
- The many-reflection pair construction realizes every selected pair weight.
- Every selected position is used at most once.
- Quotient lifting produces a defect in the stated subgroup.
- Translation preserves the quotient obstruction and can be pulled back only
  for a `2|A|` all-rotation block.
- Both zero-subgroup base cases have enough unused identity rotations.
- Every induction step descends to a strict subgroup.
- Every terminal block has exactly `2|A|` terms.

## Requested report format

For each item, state `verified`, `error`, or `unresolved`. An `error` report
should include the smallest exact location in `main.tex`/`main.pdf` and either a
counterexample or the failed implication. An `unresolved` report should name the
missing source statement or proof obligation rather than replacing it with a
plausibility judgment.
