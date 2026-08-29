# Proof audit for the arXiv rewrite

## Status

This document records proof obligations; it is not a certificate. Every item
below must be checked independently from the paper and the original cited
sources. In particular, neither Claude/GPT output, repository summaries, nor a
Lean directory may be treated as a substitute for the paper proof.

The ambient data are

\[
A=\bigoplus_i C_{p^{\lambda_i}},\qquad p\text{ odd},\qquad
Q=|A|,\qquad D_A=D(A),\qquad G=A\rtimes_{-1}C_2.
\]

The target length in every terminal branch is `2Q = |G|`.

## External inputs that carry the proof

### Olson

Used for

\[
D(A)=1+\sum_i(p^{\lambda_i}-1)
\]

and the same formula for every subgroup of `A`. Consequences used internally:
`D_A <= Q`, `exp(A) | Q`, and oddness of `D_A` and `Q`.

### Godara-Joshi-Mazumdar

The paper uses the rewriting of their Theorem 1.1

\[
d\bigl(B\rtimes_{-1}C_2\bigr)=D(B)
\]

for finite abelian `B`. It is applied with `B=A` and `B=A/K`.

Independent check required: verify the authors' definitions of the ordered and
small Davenport constants and confirm that the displayed identity follows
exactly from their theorem, not merely from a nearby bound.

### Grynkiewicz-Marchan-Ordaz (GMO)

The manuscript specializes Corollaries 1.2 and 1.3. The structural alternative
must retain the **same** coset `beta + H` for `w x`, simultaneously for every
weight `w` and every selected value `x`:

\[
W x\subseteq \beta+H.
\]

A formulation in which the coset depends on `w` is insufficient for the signed
branches and must be rejected.

Independent check required: compare Theorem 2.2 of the manuscript directly with
Corollaries 1.2-1.3 in arXiv:0903.2810 or the published Ramanujan Journal version.

## Every GMO instance

### Instance 1: few reflections - Proposition 4.1

- Ambient group: `A`.
- Sequence: all rotation vectors of `S`.
- Weight set: `{1}`.
- Target: `n=2Q`.
- Target floor: `2Q >= |A|=Q`.
- Length threshold:
  \[
  b\ge 2Q+D_A-1=n+D_{\{1\}}(A)-1.
  \]
- Output set: the existence corollary gives a value in `2Q A = {0}`.
- Required conclusion: exactly `2Q` rotations with ordinary sum zero.

### Instance 2: many reflections - Proposition 4.2

- Ambient group: `A`.
- Sequence: pair labels after pairing within the rotation and reflection types.
- Weight set: `{-1,1}`.
- Target: `n=Q=|A|`.
- Pair-sequence length:
  \[
  Q+\frac{D_A-1}{2}.
  \]
- Surplus check:
  \[
  D_{\pm}(A)\le\frac{D_A+1}{2}
  \quad\Longrightarrow\quad
  Q+\frac{D_A-1}{2}\ge Q+D_{\pm}(A)-1.
  \]
- Output set: `Q A={0}`.
- Noncommutative reconstruction: each selected reflection pair contributes one
  positive and one negative reflection sign; at least one reflection pair is
  selected because there are at most `Q-1` rotation pairs.
- Length check: `Q` selected pairs use exactly `2Q` original positions.

### Instance 3: intermediate reflection range - Proposition 4.3

- Ambient group: `A`.
- Sequence: all `b` rotation vectors.
- Weight set: `{-1,1}`.
- Target:
  \[
  e=2\lfloor a/2\rfloor,\qquad \ell=2Q-e.
  \]
- Target floor: `ell >= Q=|A|`.
- Length surplus:
  \[
  b-\ell=D_A\text{ or }D_A-1\ge D_{\pm}(A)-1.
  \]
- Full branch: choose `e` reflections with balanced signs and `ell` rotations
  with the opposite signed sum; total length `e+ell=2Q`.
- Structural branch: the common weighted coset gives `x,-x in beta+K`, hence
  `2x in K`; odd order of `A/K` implies `x in K`.
- Trivial subgroup branch: the concentration threshold gives at least `D_A`
  identity rotations, so identity padding applies.

### Instance 4: reflection-containing quotient block - Proposition 5.6

- Ambient group: a nonzero subgroup `K<A`.
- Sequence: the `M` rotations of the current sequence whose vectors lie in `K`.
- Weight set: `{-1,1}`.
- Quotient remainder: after removing product-one blocks from `T_K(S)`, the
  product-one-free remainder `R` satisfies `|R| <= D(A/K)`.
- Defect surplus:
  \[
  \tau=D_A-|R|\ge D(K)-1\ge D_{\pm}(K)-1.
  \]
- Target:
  \[
  m=M-\tau=M-D_A+|R|.
  \]
- Target floor: `m >= |K|` by the concentration threshold and Lemma 5.3.
- Length threshold: `M >= m+D_pm(K)-1`.
- Full branch: choose a signed `m`-term rotation subsequence summing to the
  negative quotient-lift defect; disjointness holds because `T_K(S)` omits the
  rotations in `K`.
- Length check:
  \[
  |U|+m=a+c-|R|+M-D_A+|R|=2Q.
  \]
- Structural branch: the common weighted coset again implies actual membership
  in `H`, and the concentration estimate composes from `K` to `H`.

### Instance 5: rotation-only quotient case - Proposition 5.8

- Ambient group: a nonzero subgroup `K<A`.
- Sequence: the `M` rotations with vectors in `K`.
- Weight set: `{1}`.
- Quotient remainder: after removing zero-sum blocks from the outside rotations,
  the remainder `B_0`, together with all reflections, is product-one-free in
  `Dih(A/K)`; hence `a+|B_0| <= D(A/K)`.
- Define
  \[
  d_0=D_A-a-|B_0|,\qquad m=M-d_0.
  \]
- Surplus: `d_0 >= D(K)-1`, hence `M >= m+D(K)-1`.
- Target floor: `m >= |K|`.
- Full branch: positional complementation converts `Sigma_m(C)=K` to
  `Sigma_{d_0}(C)=K`; the selected complement and the outside zero-sum blocks
  have total length `2Q` and ordinary sum zero.
- Structural branch: ordinary coset concentration `alpha+H` is translated to
  `H`; membership in `K` is unchanged because `alpha in K`.

## Internal interfaces requiring line-by-line checking

### Sign-realization lemma

For `2k` reflections, their coefficients in any ordered product alternate. The
proof must use `2k+1` gaps, not `2k`. Both gap parities occur, and arbitrarily
many rotations can be inserted into a gap.

### Quotient defect correction

The signs read from the lifted quotient ordering must be retained as an
assignment, while the final application of the sign-realization lemma is allowed
to reorder the whole union. The reflection assignment is balanced because the
number of reflections is positive and even.

### Positional disjointness

- Quotient blocks use reflections and rotations outside `K`.
- Correcting rotations are selected from the rotations inside `K`.
- In the rotation-only full branch, `C D_0^{-1}` lies in `K` while `B'` uses
  positions outside `K`.
- Translation and projection change values but never duplicate positions.

### Translation invariant

The transformation `tau_alpha` subtracts `alpha` from every rotation and leaves
reflections unchanged. It is not a homomorphism. For `alpha in K`, rotations
outside `K` retain their `K`-cosets, and rotations in `K` remain in `K`.

If a reflection-containing product-one block existed modulo `H` after
translation, projecting it modulo `K` and deleting identity rotations would give
a forbidden reflection-containing block modulo `K`.

Only an all-rotation output may be pulled back automatically. A selected block
of length `2Q` changes its ordinary sum by `2Q alpha=0` because `exp(A)|Q`.

### Simultaneous induction

- `P_S(K)` is a statement about the fixed original sequence.
- `Q(K)` is universal over auxiliary sequences with the same reflection and
  rotation counts and has an all-rotation conclusion.
- Both base cases are at `K=0`.
- Every nonterminal call replaces `K` by a strict subgroup `H<K`.
- The induction is on subgroup order, not on `p`-rank.

## Independent-verification verdict

This audit does not supply a verdict. A verifier should record one of:

1. `verified`, with the source passages and calculations checked;
2. `error`, with an exact manuscript location and a counterexample or failed
   implication; or
3. `unresolved`, identifying the precise external or internal obligation that
   remains open.
