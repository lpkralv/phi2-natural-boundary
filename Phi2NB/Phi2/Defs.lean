import Phi2NB.Defs

/-!
# Definitions for the statement "under RH, `Re s = 1` is a natural boundary of `Φ₂`"

Only the objects the statement mentions are here: the series `Φ₂`, its pole set `{2} ∪ {1 + ρ}` in `ℍ`, and the
residue values. The general notions (`HH`, `halfPlane`, `lineOne`, `NontrivialZeros`, `zetaMult`, `HasResidue`,
`IsNaturalBoundary`) are in `Defs.lean`. The statement is in `Phi2/Statement.lean`; proof-internal definitions live
in `Phi2/Proof/Defs.lean`.

## Junk values

`Phi2` is a `tsum`, so it is `0` where the double series is not summable (for `Re s ≤ 2`). No statement evaluates it
off `σ > 2`: the continuation is a quantified function that agrees with it on `σ > 2`, and the boundary statement
compares functions off a discrete set.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- `Φ₂(s) = ∑_{m,n ≥ 1} Λ(m) Λ(n) (m+n)^{-s}`, over ordered pairs. Meaningful for `Re s > 2` only.

Indexed by `ℕ × ℕ`: the terms with `m = 0` or `n = 0` vanish because `Λ(0) = 0` (Mathlib's
`ArithmeticFunction.map_zero`), so this is the sum over `m, n ≥ 1`. -/
def Phi2 (s : ℂ) : ℂ :=
  ∑' mn : ℕ × ℕ, ((ArithmeticFunction.vonMangoldt mn.1 : ℝ) : ℂ) *
    ((ArithmeticFunction.vonMangoldt mn.2 : ℝ) : ℂ) * (((mn.1 + mn.2 : ℕ) : ℂ)) ^ (-s)

/-- The poles of `Φ₂` in `ℍ`: `2` and `1 + ρ` for every non-trivial zero `ρ`. (Under RH these are `2` and the points
`3/2 + iγ`; the set is defined without RH. It lies in `ℍ` unconditionally, since `Re ρ > 0`.) -/
def phi2Poles : Set ℂ := {2} ∪ {s | ∃ ρ ∈ NontrivialZeros, s = 1 + ρ}

/-- The residues of `Φ₂` at its poles in `ℍ`: `1` at `2`, and `-2 m(ρ)/ρ` at `1 + ρ`. (These are `1/Γ(2)` and
`-2 m(ρ) Γ(ρ)/Γ(1 + ρ)`, from the terms `1/(s-2)` and `-2 m(ρ) Γ(ρ)/(s - 1 - ρ)` of `Γ(s)Φ₂(s)`.) The two clauses
never assign two values to one point, since `1 + ρ ≠ 2` (as `Re ρ < 1`) and `ρ ↦ 1 + ρ` is injective. -/
def HasPhi2Residues (v : ℂ → ℂ) : Prop :=
  v 2 = 1 ∧ ∀ ρ ∈ NontrivialZeros, v (1 + ρ) = -(2 * (zetaMult ρ : ℂ)) / ρ

end GoldbachBoundaries
