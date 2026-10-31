import Phi2NB.Phi2.Statement

/-!
# Phi2NB: under RH, `Re s = 1` is a natural boundary of `Φ₂`

Under RH (with the classical premises RiemannVonMangoldt, LogDerivZetaLocal and `LittlewoodGap`), `Re s = 1` is a natural boundary of
`Φ₂(s) = ∑_{m,n ≥ 1} Λ(m)Λ(n)(m+n)^{-s}`: `GoldbachBoundaries.phi2_natural_boundary` in `Phi2NB/Phi2/Statement.lean`.

The library holds the declarations that the type and the proof of `phi2_natural_boundary` use, transitively, and
nothing else. The declarations keep the namespace `GoldbachBoundaries` (and its sub-namespaces) of the larger
development they were extracted from; the directory layout follows that development's modules. The only
dependencies are Mathlib and PrimeNumberTheoremAnd.

Warning: the larger development defines the same fully qualified names, so the two must never be imported into
one file or one build target.
-/
