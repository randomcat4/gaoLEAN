# Revision report

## Source material

This rewrite started from the uploaded Claude-produced LaTeX archive, its
compiled PDF, and its revision notes. Those materials were treated as an
untrusted draft rather than as an audited proof.

## Major corrections

1. **Paper scope restored.** The manuscript now proves only the odd abelian
   `p`-group-kernel formula. The inverse problem, mixed-prime extension,
   reusable general descent theorem, and broader group families were removed
   from the paper rather than advertised as open questions.

2. **Unsupported priority language removed.** The title and abstract no longer
   claim a first determination. The nearby exact calculation for
   `D_{2n} x C_2` is acknowledged in the introduction.

3. **GMO interface rebuilt from the original corollaries.** The existence clause
   now states `Sigma_n^W(T) intersect nB != empty`. The structural clause keeps
   a single common coset `beta+H` for all weighted values. This common-coset
   condition is explicitly used in both signed descent branches.

4. **Unsupported computation removed.** The `C_3^2` example no longer claims an
   exhaustive direct computation. It gives a fully explicit five-term
   product-one-free sequence and the standard identity-padding lower bound.

5. **Bibliography rebuilt.** Incorrect or unverifiable Claude-generated entries
   were discarded. The remaining entries were reconstructed from publisher,
   DOI, or arXiv metadata. They still require independent checking before
   submission.

6. **Proof narrative rewritten.** Software-engineering terms such as
   `controller`, `channel`, `interface`, `output`, and branch-coverage language
   were replaced by standard mathematical statements. Trivial occurrence
   bookkeeping was removed as a named lemma.

7. **Local mathematical errors corrected.** The ordering lemma uses `2k+1`
   gaps. The descent is described as induction on subgroup order rather than
   `p`-rank. The false claim that the Davenport half-bound is uniformly tighter
   than the logarithmic bound was removed. The false statement that inversion
   is trivial on all abelian `2`-groups was removed with the entire open-question
   section.

8. **The delicate steps were expanded.** The paper now states the sign
   realization lemma, the common-coset specialization, quotient-defect
   correction, translation obstruction, all-rotation pullback, and both
   simultaneous-induction base cases in paper-checkable form.

9. **Build and layout checked.** The final PDF has resolved references and
   citations, no overfull or underfull boxes, and no broken glyphs observed in a
   page-by-page render.

## Deliberate non-claims

This revision does not certify the theorem, complete a priority search, or
supply a Lean proof. It records a cleaner candidate proof and an explicit audit
surface. Independent verification remains mandatory.
