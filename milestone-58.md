# Milestone M58: independent audit and clean-clone reproduction

Status: M53--M57 `LEAN_CHECKED`; the 13-page main theorem remains
`LEAN_CONDITIONAL` exactly at five visible GMO providers.

Two read-only reviewers worked independently. Reviewer A checked M53--M55 and
confirmed that Olson's exact Davenport formula, Proposition 3.1, the GJM
small-Davenport theorem, and Corollary 6.1 are represented with faithful
quantifiers and no conclusion-shaped assumptions. Reviewer B checked M56/M57
and passed the Kneser, EGZ, exact-spectrum, stabilizer, and concentration
source semantics. It correctly refused the initial local build certificate
because the older Windows checkout had a stale manifest.

The reproducibility objection was resolved without overwriting that worktree:
the public M57 branch was cloned into a fresh directory. Its committed
`lake-manifest.json` resolved MiscYD to
`3c3f6d2ef31dd82c82ea90fb0fef8508c976afb7`. After retrieving the official
Mathlib cache, Windows Lean 4.32 independently built
`GaoLean.PGGMOFoundations` and `GaoLean.PGGMOSpectrum`: 8684 jobs, exit 0.
Every audited new declaration printed only `propext`, `Classical.choice`, and
`Quot.sound`.

The server full build remains 8746 jobs, exit 0. No audit changes the final
mathematical verdict: ambient ordinary prescribed length, ambient weighted
prescribed length, ambient signed structural GMO, and ordinary/signed
structural GMO for every subgroup are still unproved and visibly present in
`PGGaoStructuralUpperInputs`.
