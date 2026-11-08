import Phi2NB.PhiR.Defs
import Phi2NB.Phi2.Proof.Defs

/-!
# Proof-internal definitions for `Φ_r`

Everything here is a definition; there are no lemmas.

Notation (Section 7 of the paper, with the names of `Phi2/Proof/Defs.lean`):

* `FL(t) = ∑ Λ(n) e^{-nt}` (the paper's `F(x)`), `hL(t) = FL(t) - 1/t` (the paper's `h(x)`),
  `ψ = negLogDerivZeta = -ζ'/ζ`, `e1L`, `E2L` (the Mellin pieces over `[1, ∞)` of `FL`, `FL²`) and the continuation `Phi2c` of `Φ₂` are
  reused from `Phi2/Proof/Defs.lean`.
* The binomial coefficients of the expansion (23), as reals: `cC r = C(r,2) = r(r-1)/2`, `cB r = B_r = -r(r-2)`,
  `cA r = A_r = (r-1)(r-2)/2`.
* `QR r t = FL^r - cC t^{-(r-2)} FL² - cB t^{-(r-1)} FL - cA t^{-r}` (the paper's `Q_r` in (23); it equals
  `∑_{k=3}^r C(r,k) t^{-(r-k)} hL^k`, `QR_eq_sum`).
* `JR r s = ∫_0^1 QR t^{s-1}` (the first integral of `K_r` in the proof of Proposition 7.2), `ER r s = ∫_1^∞ FL^r t^{s-1}`, and
  `KR r s = JR + ER - cC E2L(s-r+2) - cB e1L(s-r+1)` (the paper's `K_r`, identity (21)).
* The continuation of `Φ_r` in Γ-form (identity (21) divided by `Γ(s)`, with `Phi2c` for `Φ₂`):
  `PhiRc r s = phiRCoef r s · Phi2c(s-r+2) + phiRRest r s`, where
  `phiRCoef r s = cC Γ(s-r+2)/Γ(s)` (`= C(r,2)/P_{r-2}(s)`, holomorphic and non-zero on `σ > r - 2`) and
  `phiRRest r s = (cB Γ(s-r+1) ψ(s-r+1) + cA/(s-r) + KR r s)/Γ(s)` (meromorphic on `σ > r - 3/2` under RH).
* `RRraw r s = KR/Γ(s) + cA (1/(Γ(s)(s-r)) - ζ(s-r+1)/(r-1)!)` (the paper's `R_r`, identity (22)); it has a removable
  singularity at `s = r` (`exists_RR`).

Junk values: Bochner integrals are `0` when not integrable, `x/0 = 0`, `Γ` is junk at its poles. Every lemma that
evaluates these at a point states (or its hypotheses imply) integrability there; the poles of `Γ(s-r+1)` (at
`s = r-1, r-2, …`) and of `1/(s-r)` are where `PhiRc` is a meromorphic, not a pointwise, object.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-! ## Coefficients of the binomial expansion (23) -/

/-- `C(r,2) = r(r-1)/2`, the coefficient of `Φ₂`. -/
def cC (r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) / 2

/-- `B_r = -r(r-2)`, the coefficient of `Γ(s-r+1)ψ(s-r+1)`. -/
def cB (r : ℕ) : ℝ := -((r : ℝ) * ((r : ℝ) - 2))

/-- `A_r = (r-1)(r-2)/2`, the coefficient of `x^{-r}`. -/
def cA (r : ℕ) : ℝ := ((r : ℝ) - 1) * ((r : ℝ) - 2) / 2

/-! ## The Mellin side -/

/-- `Q_r(t) = FL^r - C(r,2) t^{-(r-2)} FL² - B_r t^{-(r-1)} FL - A_r t^{-r}` (the expansion (23)). Meaningful for `t > 0`
and `r ≥ 2` (natural-number exponents `r - 2`, `r - 1`). -/
def QR (r : ℕ) (t : ℝ) : ℝ :=
  FL t ^ r - cC r * FL t ^ 2 / t ^ (r - 2) - cB r * FL t / t ^ (r - 1) - cA r / t ^ r

/-- `J_r(s) = ∫_0^1 Q_r(t) t^{s-1} dt` (holomorphic on `σ > r - 3/2` under RH). -/
def JR (r : ℕ) (s : ℂ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, (QR r t : ℂ) * (t : ℂ) ^ (s - 1)

/-- `E_r(s) = ∫_1^∞ FL(t)^r t^{s-1} dt` (entire). -/
def ER (r : ℕ) (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((FL t ^ r : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- `K_r(s) = J_r(s) + E_r(s) - C(r,2) E₂(s-r+2) - B_r e₁(s-r+1)` (identity (21)). -/
def KR (r : ℕ) (s : ℂ) : ℂ :=
  JR r s + ER r s - (cC r : ℂ) * E2L (s - r + 2) - (cB r : ℂ) * e1L (s - r + 1)

/-! ## The continuation of `Φ_r` to `σ > r - 1` -/

/-- `f₄(s) = C(r,2) Γ(s-r+2)/Γ(s)`, the coefficient of `Φ₂(s-r+2)` (`= C(r,2)/P_{r-2}(s)`). -/
def phiRCoef (r : ℕ) (s : ℂ) : ℂ := (cC r : ℂ) * Gamma (s - r + 2) * (Gamma s)⁻¹

/-- The rest of identity (21) divided by `Γ(s)`: `(B_r Γ(s-r+1) ψ(s-r+1) + A_r/(s-r) + K_r(s))/Γ(s)`. Meromorphic on
`σ > r - 3/2` under RH (`meromorphicOn_phiRRest`). -/
def phiRRest (r : ℕ) (s : ℂ) : ℂ :=
  ((cB r : ℂ) * Gamma (s - r + 1) * negLogDerivZeta (s - r + 1) + (cA r : ℂ) / (s - r) + KR r s) *
    (Gamma s)⁻¹

/-- The continuation of `Φ_r` to `σ > r - 1`: `f₄(s) Φ₂c(s-r+2) + rest(s)` (junk at the poles, which no statement
reads). -/
def PhiRc (r : ℕ) (s : ℂ) : ℂ := phiRCoef r s * Phi2c (s - r + 2) + phiRRest r s

/-! ## The remainder of identity (22) -/

/-- The paper's `R_r` (identity (22)) before removing the singularity at `s = r`:
`K_r(s)/Γ(s) + A_r (1/(Γ(s)(s-r)) - ζ(s-r+1)/(r-1)!)`. -/
def RRraw (r : ℕ) (s : ℂ) : ℂ :=
  KR r s * (Gamma s)⁻¹ +
    (cA r : ℂ) * ((Gamma s)⁻¹ / (s - r) - riemannZeta (s - r + 1) / ((r - 1).factorial : ℂ))

end GoldbachBoundaries.PhiRProof
