import Phi2NB.PhiR.PremiseCorrespondence

/-!
# Definitions for "under RH, `Re s = r - 1` is a natural boundary of `Φ_r`" (`r ≥ 2`)

These are the objects of Section 7 of the paper (Theorem 7.1 and Proposition 7.2), proved by the Mellin transform.
Statement: `PhiR/Statement.lean`.

Only the objects the statements mention are here: the series `Φ_r`, the line `σ = a`, the pole set `{r} ∪ {r - 1 + ρ}`
of the continuation in `σ > r - 1`, its residues, and the polynomial `P_j(s) = (s-1)(s-2)⋯(s-j)` of Section 7.
Everything else (`halfPlane`, `HH`, `lineOne`, `NontrivialZeros`, `zetaMult`, `HasResidue`, `IsNaturalBoundary`, and
`Phi2`) is reused unchanged from `Phi2NB/Defs.lean` and `Phi2NB/Phi2/Defs.lean`.

## Junk values (as for `Phi2`)

`PhiR r` is a `tsum`, so it is `0` where the `r`-fold series is not summable (for `Re s ≤ r`). No statement evaluates it
off `σ > r`: continuations are quantified functions that agree with it on `σ > r`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- `Φ_r(s) = ∑_{k_1, …, k_r ≥ 1} Λ(k_1) ⋯ Λ(k_r) (k_1 + ⋯ + k_r)^{-s}`, over ordered `r`-tuples. Meaningful for
`Re s > r` only.

Indexed by `Fin r → ℕ`: a tuple with some `k_i = 0` contributes `0` because `Λ(0) = 0`, so this is the sum over
`k_i ≥ 1` (`PhiR_term_eq_zero` in `Statement.lean`). For `r = 2` it is `Phi2` at every `s` (`PhiR_two`). -/
def PhiR (r : ℕ) (s : ℂ) : ℂ :=
  ∑' k : Fin r → ℕ, (∏ i, ((ArithmeticFunction.vonMangoldt (k i) : ℝ) : ℂ)) *
    (((∑ i, k i : ℕ) : ℂ)) ^ (-s)

/-- The vertical line `σ = a`. (`lineAt 1 = lineOne`, `lineAt_one`.) -/
def lineAt (a : ℝ) : Set ℂ := {s | s.re = a}

/-- `P_j(s) = (s - 1)(s - 2) ⋯ (s - j)`, `P_0 = 1` (Section 7 of the paper). `Γ(s - j)/Γ(s) = 1/P_j(s)`. -/
def polyP (j : ℕ) (s : ℂ) : ℂ := ∏ l ∈ Finset.Icc 1 j, (s - (l : ℂ))

/-- The poles of the continuation of `Φ_r` in `σ > r - 1`: `r` and `r - 1 + ρ` for every non-trivial zero `ρ` (under
RH the points `r - 1/2 + iγ`). Defined without RH; it lies in `σ > r - 1` unconditionally (`phiRPoles_subset`).
`phiRPoles 2 = phi2Poles` (`phiRPoles_two`). -/
def phiRPoles (r : ℕ) : Set ℂ := {(r : ℂ)} ∪ {s | ∃ ρ ∈ NontrivialZeros, s = ((r : ℂ) - 1) + ρ}

/-- The residues of the continuation of `Φ_r` at its poles in `σ > r - 1`: `1/(r-1)! = 1/Γ(r)` at `r`, and
`-r m(ρ) Γ(ρ)/Γ(ρ + r - 1)` at `r - 1 + ρ`. They come from the terms `x^{-r}` and `r x^{-(r-1)} h(x)` of
`F(x)^r = (1/x + h(x))^r` (identity (21) of Section 7 of the paper): `Γ(s)Φ_r(s)` has residue `1` at `r` and
`-r m(ρ) Γ(ρ)` at `r - 1 + ρ`. For `r = 2` these are `1` and `-2m(ρ)/ρ`, i.e. `HasPhi2Residues` (`hasPhiRResidues_two_iff`).

The residue at `r - 1 + ρ` is derived in the proof of Theorem 7.1(i) of the paper from identity (21) and the residues
of `ζ'/ζ` and `Φ₂` (both terms have a pole there; they combine to `m(ρ) Γ(ρ)/Γ(ρ + r - 1) · (r(r-2) - r(r-1))`). -/
def HasPhiRResidues (r : ℕ) (v : ℂ → ℂ) : Prop :=
  v (r : ℂ) = 1 / ((r - 1).factorial : ℂ) ∧
  ∀ ρ ∈ NontrivialZeros,
    v (((r : ℂ) - 1) + ρ) = -((r : ℂ) * (zetaMult ρ : ℂ)) * Gamma ρ / Gamma (ρ + ((r : ℂ) - 1))

end GoldbachBoundaries
