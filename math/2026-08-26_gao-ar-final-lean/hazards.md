# Formalization hazards

1. Do not replace occurrence-cardinality by distinct-value cardinality.
2. Do not replace “some ordering has product one” by multiplication in the
   input order.
3. Do not turn a conditional consumer into an unconditional producer.
4. Do not drop the full-spectrum/concentration alternative from the weighted
   external theorem interface.
5. Do not assume the residual state; it is an internal theorem obligation.
6. Do not use `q != 2` as a substitute for primality, or vice versa.
7. Do not hide rank restrictions in typeclass inference.
8. Do not count a statement file, an `example`, or a theorem with extra
   premises as proof of `GAOARV1Statement`.
9. No `sorry`, `admit`, paper-specific `axiom`, or forbidden placeholder.
10. Every milestone must be rebuilt in the pinned server environment and
    synchronized to the public repository.
