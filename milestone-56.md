# Milestone M56: GMO foundations

Status: `LEAN_CHECKED`; the 13-page manuscript remains `LEAN_CONDITIONAL` at
the Grynkiewicz--Marchan--Ordaz source theorem.

The published GMO proof depends on Kneser's addition theorem, the
DeVos--Goddyn--Mohar theorem, and a structural setpartition theorem. Mathlib
4.32 already contains a Chevalley--Warning proof of Erdős--Ginzburg--Ziv but
does not contain Kneser or the latter two results.

This milestone pins `YaelDillies/misc-yd` at commit `3c3f6d2`, its exact
Lean/Mathlib 4.32 compatibility point, and imports its formal Kneser theorem.
`GaoLean/PGGMOFoundations.lean` exposes that result and translates Mathlib EGZ
into the project's occurrence-labelled sequence semantics. It also proves by
disjoint iteration that `(t+1)n-1` labelled elements of `ZMod n` contain
exactly `tn` labelled elements summing to zero.

All new declarations preserve repeated source values by selecting positions.
Their axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No GMO provider has been declared proved at this milestone;
DeVos--Goddyn--Mohar and the structural setpartition layer remain explicit
work items. The full server build completed 8745 jobs with exit 0.
