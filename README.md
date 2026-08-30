# Gao Lean

**The exact Gao constant of generalized dihedral groups, formalized in Lean**

> [Read the 13-page paper (PDF)](paper/arxiv/main.pdf)
>
> [LaTeX sources](paper/arxiv/) ·
> [Manuscript-to-Lean evidence map](docs/manuscript-lean-map.md) ·
> [Formalization status](docs/formalization-plan.md)

This is one of the formalization repositories in Euler's first batch of
publicly releasable results.

## The problem

For a finite group $G$, the Gao constant $E(G)$ is the least integer $L$ such
that every sequence of at least $L$ elements of $G$ contains exactly $|G|$
terms that can be reordered to have product one. The standard construction
gives the lower bound

$$
E(G) \ge |G| + d(G),
$$

where $d(G)$ is the small Davenport constant. The central question is when
this lower bound is exact.

## Historical context

| Year | Result |
|---|---|
| **1996** | Weidong Gao proved $E(G)=\lvert G\rvert+D(G)-1=\lvert G\rvert+d(G)$ for every finite abelian group. |
| **2005** | Zhuang and Gao conjectured the same equality for every finite group. This repository does not claim to settle that full conjecture. |
| **2026** | The result recorded here settles a new nonabelian infinite family: generalized dihedral groups with an arbitrary finite abelian odd $p$-group kernel. |

Primary references:
[Gao 1996](https://doi.org/10.1006/jnth.1996.0067) ·
[Zhuang–Gao 2005](https://doi.org/10.1016/j.ejc.2004.06.014) ·
[Godara–Joshi–Mazumdar 2026](https://doi.org/10.1016/j.jnt.2025.11.011)

## Main theorem

Let $p$ be an odd prime and let

$$
A = \bigoplus_{i=1}^{r} C_{p^{\lambda_i}},
\qquad
\mathrm{Dih}(A) = A \rtimes_{-1} C_2,
$$

where $C_2$ acts on $A$ by inversion. This project proves and formally
verifies

$$
E\bigl(\mathrm{Dih}(A)\bigr)
 = 2|A| + D(A)
 = 2|A| + 1 + \sum_{i=1}^{r}\bigl(p^{\lambda_i}-1\bigr).
$$

Together with $d(\mathrm{Dih}(A))=D(A)$, this gives

$$
E\bigl(\mathrm{Dih}(A)\bigr)
 = |\mathrm{Dih}(A)| + d\bigl(\mathrm{Dih}(A)\bigr).
$$

The theorem extends the cyclic-kernel dihedral formula to every finite
abelian odd $p$-group kernel, including noncyclic kernels. For example,

$$
E\bigl(\mathrm{Dih}(C_3^2)\bigr)=23.
$$

The project does not claim to cover mixed-prime kernels, $2$-group kernels,
all finite groups, or the inverse problem.

## Paper and formal verification

The repository contains:

- the [13-page paper](paper/arxiv/main.pdf);
- the complete [LaTeX source, bibliography, and build instructions](paper/arxiv/);
- the Lean 4 proof, its supporting theorems, and an axiom audit;
- a [section-by-section evidence map](docs/manuscript-lean-map.md); and
- the [open obligations and release gates](docs/formalization-plan.md).

| Scope | Status |
|---|---|
| Exact generalized-dihedral Gao formula stated above | **Unconditionally checked in Lean** |
| The $W=\{1\}$ and $W=\{\pm1\}$ GMO specializations used by the main proof | **Checked in Lean** |
| Full arbitrary-weight GMO theorem for every nonempty integer weight set $W$ | **In progress — PARTIALLY_VERIFIED** |

The repository-wide verdict remains **PARTIALLY_VERIFIED** only because the
paper also states the full arbitrary-weight GMO theorem, whose complete source
range is still being formalized. The final Gao formula does not depend on a
hidden assumption, a conditional engine, a provider parameter, or an admitted
result.

The stable public Lean entry point is
`GaoLean.ConcreteGDihedral.gaoGeneralizedDihedralOddPGroup`. Historical PR/V1
names are retained only as provenance-preserving internal interfaces.

## Reproduction

The repository pins Lean v4.32.0 and Mathlib v4.32.0.

```bash
lake update
lake exe cache get
lake build GaoLean GaoFormal.AxiomAudit
```

The latest server build from a separate checkout completed **8853/8853 jobs**
with exit code 0; see the
[build receipt](docs/build-receipts/2026-08-30-c5076bb.md). The public audit
surface uses only the standard Lean/Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound` where applicable. The repository scan
found no `sorry`, `admit`, project-defined top-level axiom, `unsafe`,
`native_decide`, or `sorryAx` escape.

To rebuild the paper:

```bash
cd paper/arxiv
make pdf
```

The committed PDF has 13 pages and was rebuilt from the committed sources.
The final build log contains no unresolved reference, unresolved citation,
overfull-box, or underfull-box warning.

## Repository layout

```text
paper/arxiv/       Paper PDF, LaTeX source, bibliography, and build report
GaoLean/           Main mathematics and the general-weight GMO formalization
GaoFormal/         Aggregate entry point and axiom audit
docs/              Current plan, evidence map, coverage tables, and build records
docs/milestones/   Archived development milestones
audit/             Frozen statements and independent review material
```

Please use GitHub Issues for proof suggestions, reproduction failures, and
other questions. Any upgrade to the verification status must update the
evidence map, axiom audit, and independent clean-build record together.
