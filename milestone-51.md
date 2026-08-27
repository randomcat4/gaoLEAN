# Milestone M51: Proposition 3.1 group-algebra core

Status: `LEAN_CHECKED` for the coefficient-extraction and augmentation-product
layers; Proposition 3.1 as a whole remains `PARTIAL`.

`GaoLean/PGPlusMinusGroupAlgebra.lean` works literally in
`AddMonoidAlgebra (ZMod p) B`.  It proves that every support term in

`prod_j ([x_j]+[-x_j]-2[0])`

comes from an occurrence-indexed coefficient vector in `{-1,0,1}`.  If no
nonzero vector has weighted sum zero, the coefficient of `[0]` is exactly
`(-2)^m`; this is nonzero in odd prime characteristic, contradicting
vanishing of the product.

The file also proves the paper's identity

`[x]+[-x]-2[0]=[-x]([x]-[0])^2`

and factors the whole product into basis units times exactly two augmentation
generators per source occurrence.  Consequently generator-product
nilpotence at degree `D` implies the exact bound
`D_pm(B) <= (D+1)/2` for odd `D`.

The remaining Proposition 3.1 obligation is now precise: derive the
generator-product nilpotence interface from an invariant-factor presentation
`B = direct_sum C_(p^mu_i)` and degree
`D = 1 + sum_i (p^mu_i - 1)`.  That is the `I^D=0` portion of the manuscript;
it is not claimed here as already proved.

Server verification used Lean 4.32.0 / Mathlib v4.32.0.  The full build and
unified axiom audit completed 8738 jobs with exit code 0.  The new theorem
chain uses only `propext`, `Classical.choice`, and `Quot.sound`; the scan found
no project axiom, `sorry`, `admit`, `unsafe`, `native_decide`, or `sorryAx`.
