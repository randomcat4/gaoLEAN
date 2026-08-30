# Assumptions and external boundaries

## Intrinsic hypotheses of the frozen theorem

- `q : Nat`
- `q.Prime`
- `q != 2`
- `r : Nat`
- `2 <= r`

No additional mathematical hypothesis may be inserted into the exported
GAO-AR theorem.

## Published results allowed only as explicit interfaces

- Olson: `D(C_q^j) = j(q-1)+1` (unless reconstructed internally).
- Gao--Jin--Miao: the small Davenport constant for the relevant generalized
  dihedral group (unless reconstructed internally).
- The weighted prescribed-length/full-spectrum-or-concentration theorem used
  by the manuscript (GMO boundary).
- Cauchy--Davenport, already available from Mathlib and used internally.

An external result must appear as a named proposition parameter/provider with
its complete quantifiers and alternatives.  It must not be introduced as a
Lean `axiom`, a `sorry`, or an unconditional theorem.

## Logic policy

Standard Lean/Mathlib logical dependencies such as `propext`,
`Classical.choice`, and quotient soundness are permitted.  They are not
paper-specific mathematical assumptions.
