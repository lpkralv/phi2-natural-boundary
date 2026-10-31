import Phi2NB.Phi2.Defs
import Phi2NB.Paper2.Defs
import Phi2NB.LogDerivZeta

/-!
# Proof-internal definitions

Everything here is a definition; there are no lemmas. Notation of the proof:

* `ψ = negLogDerivZeta = -ζ'/ζ` (`LogDerivZeta.lean`), `Λ = ArithmeticFunction.vonMangoldt`.
* `FL(t) = ∑_n Λ(n) e^{-nt}`, `hL(t) = FL(t) - 1/t`.
* The Mellin pieces `m1L`, `e1L`, `E2L`, `RrL` (integrals of `hL`, `FL`, `FL²`, `hL²` over `(0, 1]` or `(1, ∞)`).
* `Hphi2(s) = (E2L(s) - 2 e1L(s-1) + RrL(s)) / Γ(s)`, holomorphic on `ℍ` under RH, and
  `phi2Main(s) = 2ψ(s-1)/(s-1) - 1/(Γ(s)(s-2))`, meromorphic on `ℂ`. The continuation is `Phi2c = phi2Main + Hphi2`,
  from the identity `Φ₂ = phi2Main + Hphi2` on `σ > 2`.
* `zeroCoef ρ = a_ρ = m(ρ) Γ(ρ)`, `zeroSum t = ∑_ρ a_ρ t^{-ρ}` (the zero part of the explicit formula),
  `cauchyT s = ∑_{(ρ,ρ')} a_ρ a_ρ' / (s - ρ - ρ')` (the Cauchy transform of `μ = ν * ν`, shifted by `1`),
  `pairAtom τ = μ{τ} = ∑_{ρ + ρ' = 1 + iτ} a_ρ a_ρ'` (ordered pairs of distinct zeros-as-points, so a diagonal pair is
  counted once), `Kc` the remainder of `RrL` after `cauchyT`.
* `kernelL t w = t^{-w} Γ(w) ψ(w)`, the inverse-Mellin integrand of `FL`.
* `bKer τ u = b_τ(u) = Γ(1/2 + i(u+τ)) Γ(1/2 - iu)`, and the index set `Aidx τ` of the opposite-sign pairs
  `(ρ + iτ, ρ̄)` with `ρ = 1/2 + iu`, `u > 0`.

Junk values: `tsum`s are `0` when not summable and Bochner integrals `0` when not integrable. Every lemma that
evaluates one of these at a point states (or its hypotheses imply) summability or integrability there; under RH
and (RiemannVonMangoldt) `zeroCoef` is absolutely summable (`summable_norm_zeroCoef`), which makes `zeroSum`, `cauchyT` (for `Re s > 1`) and
`pairAtom` genuine sums.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-! ## The Mellin side -/

/-- `FL(t) = ∑_{n ≥ 1} Λ(n) e^{-nt}` (`Λ(0) = 0`). Meaningful for `t > 0`. -/
def FL (t : ℝ) : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Real.exp (-((n : ℝ) * t))

/-- `hL(t) = FL(t) - 1/t`. -/
def hL (t : ℝ) : ℝ := FL t - 1 / t

/-- `m₁(z) = ∫_0^1 hL(t) t^{z-1} dt`. -/
def m1L (z : ℂ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, (hL t : ℂ) * (t : ℂ) ^ (z - 1)

/-- `e₁(z) = ∫_1^∞ FL(t) t^{z-1} dt` (entire). -/
def e1L (z : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (FL t : ℂ) * (t : ℂ) ^ (z - 1)

/-- `E₂(s) = ∫_1^∞ FL(t)² t^{s-1} dt` (entire). -/
def E2L (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((FL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- `R(s) = ∫_0^1 hL(t)² t^{s-1} dt` (holomorphic on `ℍ` under RH). -/
def RrL (s : ℂ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, ((hL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- `H(s) = (E₂(s) - 2 e₁(s-1) + R(s)) / Γ(s)`. -/
def Hphi2 (s : ℂ) : ℂ := (E2L s - 2 * e1L (s - 1) + RrL s) * (Gamma s)⁻¹

/-- The meromorphic part `2ψ(s-1)/(s-1) - 1/(Γ(s)(s-2))`, meromorphic on all of `ℂ`; it carries the poles at `2` and
`1 + ρ`. -/
def phi2Main (s : ℂ) : ℂ := 2 * negLogDerivZeta (s - 1) / (s - 1) - 1 / (Gamma s * (s - 2))

/-- The continuation of `Φ₂` to `ℍ`: `phi2Main + Hphi2` (junk at the poles, which no statement reads). -/
def Phi2c (s : ℂ) : ℂ := phi2Main s + Hphi2 s

/-- The inverse-Mellin integrand `t^{-w} Γ(w) ψ(w)` of `FL`. -/
def kernelL (t : ℝ) (w : ℂ) : ℂ := (t : ℂ) ^ (-w) * (Gamma w * negLogDerivZeta w)

/-! ## The zero side -/

/-- `a_ρ = m(ρ) Γ(ρ)`. -/
def zeroCoef (ρ : ℂ) : ℂ := (zetaMult ρ : ℂ) * Gamma ρ

/-- `∑_ρ a_ρ t^{-ρ}`, over the distinct non-trivial zeros (the zero part of the explicit formula for `FL`). -/
def zeroSum (t : ℝ) : ℂ := ∑' ρ : NontrivialZeros, zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))

/-- `∑_{(ρ, ρ')} a_ρ a_ρ' / (s - ρ - ρ')` over ordered pairs of zeros: under RH, the Cauchy transform
`∫ dμ(t)/(s - 1 - it)` of `μ = ν * ν`. -/
def cauchyT (s : ℂ) : ℂ :=
  ∑' p : NontrivialZeros × NontrivialZeros, zeroCoef p.1 * zeroCoef p.2 / (s - p.1 - p.2)

/-- The ordered pairs of zeros `(ρ, ρ')` with `ρ + ρ' = 1 + iτ`. A diagonal pair `(ρ, ρ)` occurs once. -/
def pairIdx (τ : ℝ) : Type := {p : NontrivialZeros × NontrivialZeros // (p.1 : ℂ) + p.2 = 1 + τ * I}

/-- The atom `μ{τ} = ∑_{ρ + ρ' = 1 + iτ} a_ρ a_ρ'` (`0` if there is no pair). The radial coefficient of `Φ₂` at
`1 + iτ`, `τ ≠ 0`, is `C(τ) = pairAtom τ / Γ(1 + iτ)`. -/
def pairAtom (τ : ℝ) : ℂ := ∑' p : pairIdx τ, zeroCoef p.1.1 * zeroCoef p.1.2

/-- `Kc(s) = ∫_0^1 (hL(t)² - zeroSum(t)²) t^{s-1} dt`: the part of `RrL` left after the Cauchy transform. -/
def Kc (s : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, (((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2) * (t : ℂ) ^ (s - 1)

/-! ## The non-cancellation lemma -/

/-- `b_τ(u) = Γ(1/2 + i(u+τ)) Γ(1/2 - iu)`. -/
def bKer (τ u : ℝ) : ℂ := Gamma (1 / 2 + ((u + τ : ℝ) : ℂ) * I) * Gamma (1 / 2 - (u : ℂ) * I)

/-- The zeros `ρ = 1/2 + iu` with `u > 0` such that `ρ + iτ` is also a zero: the index set `A_τ` of the
non-cancellation lemma. Each gives the two ordered pairs `(ρ + iτ, ρ̄)`, `(ρ̄, ρ + iτ)` with sum `1 + iτ` (under RH). -/
def Aidx (τ : ℝ) : Type :=
  {ρ : NontrivialZeros // 0 < (ρ : ℂ).im ∧ (ρ : ℂ) + τ * I ∈ NontrivialZeros}

/-- The weight `q_τ(u) = m(ρ) m(ρ + iτ)` of `i : Aidx τ`. -/
def Aweight (τ : ℝ) (i : Aidx τ) : ℕ := zetaMult (i.1 : ℂ) * zetaMult ((i.1 : ℂ) + τ * I)

end GoldbachBoundaries.Phi2Proof
