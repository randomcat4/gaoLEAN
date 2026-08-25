# Frozen theorem v1

Lean declaration: `GaoLean.GAOARV1Statement`.

```text
forall q r : Nat,
  q.Prime -> q != 2 -> 2 <= r ->
  IsExactProductOneThreshold
    ((C_q^r) semidirect_{-1} C_2)
    (2*q^r + r*(q-1) + 1)
    (2*q^r)
```

Semantic checks:

- sequences are lists, hence repeated values retain separate occurrences;
- selected blocks use finite sets of occurrence labels;
- product-one means that some ordering of the selected multiset multiplies
  to the identity;
- exact threshold includes both the upper statement at every length at least
  the threshold and counterexamples at every smaller length.

## Change control

Any proposed change to the hypotheses, target length, threshold, group, or
product-one semantics creates a new version and is not accepted as a proof of
v1.  No such change is currently authorized.
