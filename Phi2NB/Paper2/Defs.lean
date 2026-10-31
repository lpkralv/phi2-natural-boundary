import Phi2NB.Defs

/-!
# The classical premises on the zeros of `ζ`

The counting function `N(t)` and the classical facts about the non-trivial zeros that the main theorem takes as
explicit premises: (RiemannVonMangoldt) the local count of zeros `N(t+1) - N(t) ≪ log t`, (LogDerivZetaLocal) the local expansion of `ζ'/ζ`, and
Littlewood's gap theorem `LittlewoodGap`. The symmetry statement (ZeroSymmetry) is also defined here; it is not a premise of the
main theorem, which proves it from RH (`Phi2Proof.zeroSymmetry_of_RH`).

## Junk-value discipline

`tsum`, `∑ᶠ`, `Set.ncard` and Bochner integrals return junk (`0`) when the sum, set or integral is not summable,
finite or integrable. Every statement that relies on a count or a sum being finite says so (`Set.Finite`,
`Summable`, `Integrable`) or proves it, so that a junk `0` can never make a statement true. A pointwise formula is
asserted only at points where every function in it is analytic.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

/-- `(H_∞)`: for every `δ > 0` only finitely many zeros have `β > 1/2 + δ`.

This is **not** a hypothesis of the main theorem and is used by no proof in this library. It is kept only because
the elaborated term of `LogDerivZetaLocal` refers to the auxiliary declaration `Hinf._proof_1`, which Lean generated while
elaborating this definition (the instance proof `(1 + 1).AtLeastTwo` behind the numeral `2`) and reuses later. -/
def Hinf : Prop := ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ 1 / 2 + δ < ρ.re}.Finite

/-! ## The classical inputs

Each is a `Prop`, true by the cited classical theorem and not proved here, and appears as an explicit hypothesis
exactly on the statements whose proofs use it. None is an `axiom`. -/

/-- (ZeroSymmetry), the symmetry of the zeros: `ρ̄` and `1 - ρ̄` are zeros of the same multiplicity as `ρ`. (The classical
(ZeroSymmetry) also says `0 < β < 1`, true here by the definition of `NontrivialZeros`; `ζ(1 + it) ≠ 0`, Mathlib's
`riemannZeta_ne_zero_of_one_le_re`; and `ζ(x) ≠ 0` for `0 < x < 1`, `riemannZeta_ne_zero_of_mem_Ioo`. Only the
symmetry is stated; `conj_mem_nontrivialZeros` proves that `ρ̄` is a zero, but not its multiplicity.) Under RH it is
a theorem, `Phi2Proof.zeroSymmetry_of_RH`. -/
def ZeroSymmetry : Prop :=
  ∀ ρ ∈ NontrivialZeros,
    (conj ρ ∈ NontrivialZeros ∧ zetaMult (conj ρ) = zetaMult ρ) ∧
      (1 - conj ρ ∈ NontrivialZeros ∧ zetaMult (1 - conj ρ) = zetaMult ρ)

/-- `N(t)`: the number of zeros with `0 < γ ≤ t`, counted with multiplicity. The set is finite (zeros are
discrete and avoid a neighbourhood of `1`), so `∑ᶠ` is the finite sum. -/
def Nzero (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}, (zetaMult ρ : ℝ)

/-- (RiemannVonMangoldt), the local count of zeros (Titchmarsh, Thm 9.2: `N(T+1) - N(T) = O(log T)`), in the form
`N(t+1) - N(t) ≤ C₁ log(t+3)` for all `t ≥ 0` (on bounded `t` this holds because `N` is bounded there). The
Riemann–von Mangoldt asymptotic for `N(t)` itself is not part of the premise: no proof here uses it. -/
def RiemannVonMangoldt : Prop :=
  ∃ C₁ : ℝ, ∀ t : ℝ, 0 ≤ t → Nzero (t + 1) - Nzero t ≤ C₁ * Real.log (t + 3)

/-- (LogDerivZetaLocal), the local expansion of `ζ'/ζ`: for `-1 ≤ Re z ≤ 2`, `|Im z| ≥ 2`,
`ζ'/ζ(z) = ∑_{|γ - Im z| ≤ 1} m(ρ)/(z - ρ) + O(log |Im z|)` uniformly. Asserted at points with `ζ(z) ≠ 0`
(at a zero both sides have a pole; the identity is one of meromorphic functions). -/
def LogDerivZetaLocal : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 →
    ‖deriv riemannZeta z / riemannZeta z -
        ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1}, (zetaMult ρ : ℂ) / (z - ρ)‖ ≤
      C * Real.log |z.im|

/-- Littlewood's theorem on gaps between ordinates (Titchmarsh, Ch. IX): for large `t` there is an ordinate `γ`
with `|γ - t| < a / log log log t`. -/
def LittlewoodGap : Prop :=
  ∃ a : ℝ, ∀ᶠ t in atTop, ∃ ρ ∈ NontrivialZeros,
    |ρ.im - t| < a / Real.log (Real.log (Real.log t))

namespace Aff

end Aff

end GoldbachBoundaries.Paper2
