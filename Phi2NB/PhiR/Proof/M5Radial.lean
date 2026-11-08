import Phi2NB.PhiR.Proof.M3Boundary
import Phi2NB.PhiR.Fill.riemannZeta_ne_zero_of_re_eq_zero
import Phi2NB.PhiR.Fill.tendsto_eta_Phi2c
import Phi2NB.PhiR.Fill.analyticAt_phiRRest_line

/-!
# Step M5: the radial limit (Theorem 7.1(iii))

For `τ ≠ 0`, `η Φ_r(r - 1 + iτ + η) → C(r,2) μ{τ}/Γ(r - 1 + iτ)` as `η → 0+`, where
`μ{τ} = Phi2Proof.pairAtom τ` (equation (15) of the paper). From `PhiRc = rest + f₄ · Phi2c(· - r + 2)`: `rest` is analytic at
`r - 1 + iτ` (`ζ(iτ) ≠ 0` and `Γ` has no pole at `iτ`), `f₄(r - 1 + iτ) = C(r,2) Γ(1 + iτ)/Γ(r - 1 + iτ)`, and
`η Phi2c(1 + iτ + η) → μ{τ}/Γ(1 + iτ)` (`Phi2Proof.tendsto_eta_Hphi2`, `phi2Main` analytic at `1 + iτ`).

Lemmas proved in `Fill/`: `riemannZeta_ne_zero_of_re_eq_zero`, `tendsto_eta_Phi2c`, `analyticAt_phiRRest_line`.
Proved in this file: `tendsto_eta_PhiRc`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.Paper2

/-- **`ζ(iτ) ≠ 0` for real `τ ≠ 0`** (no RH). Proof: Mathlib's functional equation `riemannZeta_one_sub` at
`s = 1 - iτ` (not a non-positive integer, `≠ 1`): `ζ(iτ) = 2(2π)^{-s} Γ(s) cos(πs/2) ζ(s)`, with `ζ(s) ≠ 0`
(`riemannZeta_ne_zero_of_one_le_re`), `Γ(s) ≠ 0`, and `cos(π(1 - iτ)/2) = sin(iπτ/2) = i sinh(πτ/2) ≠ 0`. -/
theorem riemannZeta_ne_zero_of_re_eq_zero {τ : ℝ} (hτ : τ ≠ 0) : riemannZeta (τ * I) ≠ 0 :=
  FillB.riemannZeta_ne_zero_of_re_eq_zero' hτ

/-- **Radial limit of `Phi2c`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)), `τ ≠ 0`: `η Phi2c(1 + iτ + η) → μ{τ}/Γ(1 + iτ)`.
Proof: `Phi2c = phi2Main + Hphi2`; `tendsto_eta_Hphi2`; `phi2Main = 2ψ(s-1)/(s-1) - 1/(Γ(s)(s-2))` is analytic at
`1 + iτ` (`ψ` analytic at `iτ` by `analyticAt_negLogDerivZeta`, `iτ ≠ 1` and `riemannZeta_ne_zero_of_re_eq_zero`;
`1 + iτ ≠ 1, 2`), so `η phi2Main(1 + iτ + η) → 0`. -/
theorem tendsto_eta_Phi2c (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * Phi2c (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I))) :=
  FillB.tendsto_eta_Phi2c' hRH hRvM hLD hτ

/-- **`rest` is analytic at `r - 1 + iτ`, `τ ≠ 0`** (RH). `Γ(s - r + 1)` is analytic at `iτ` (not a non-positive
integer; `Complex.differentiableAt_Gamma`, then analytic on an open set), `ψ(s - r + 1)` at `iτ`
(`analyticAt_negLogDerivZeta`, `riemannZeta_ne_zero_of_re_eq_zero`), `A_r/(s - r)` (`r - 1 + iτ ≠ r`), `K_r`
(`differentiableOn_KR`), `1/Γ`. -/
theorem analyticAt_phiRRest_line (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ≠ 0) :
    AnalyticAt ℂ (phiRRest r) ((r : ℂ) - 1 + τ * I) :=
  FillB.analyticAt_phiRRest_line' hRH hr hτ

/-- **Theorem 7.1(iii), the radial limit** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)), `τ ≠ 0`: `η PhiRc(r - 1 + iτ + η) → C(r,2) μ{τ}/Γ(r - 1 + iτ)`.
Proved in this file: `rest` is continuous at `s₀ = r - 1 + iτ`, so `η rest → 0`; `f₄ → f₄(s₀)`; `tendsto_eta_Phi2c`; and
`f₄(s₀) · μ{τ}/Γ(1 + iτ) = C(r,2) μ{τ}/Γ(s₀)`. -/
theorem tendsto_eta_PhiRc (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ}
    (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * PhiRc r ((r : ℂ) - 1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 ((cC r : ℂ) * pairAtom τ / Gamma ((r : ℂ) - 1 + τ * I))) := by
  set s0 : ℂ := (r : ℂ) - 1 + τ * I with hs0
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hs : Tendsto (fun η : ℝ => s0 + η) (𝓝[>] 0) (𝓝 s0) := by
    simpa using (tendsto_const_nhds (x := s0)).add hη
  have hRest : Tendsto (fun η : ℝ => (η : ℂ) * phiRRest r (s0 + η)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (analyticAt_phiRRest_line hRH hr hτ).continuousAt.tendsto.comp hs
    simpa using hη.mul hc
  have hre : (r : ℝ) - 2 < s0.re := by simp [hs0]
  have hCoef : Tendsto (fun η : ℝ => phiRCoef r (s0 + η)) (𝓝[>] 0) (𝓝 (phiRCoef r s0)) :=
    (analyticAt_phiRCoef hre).continuousAt.tendsto.comp hs
  have hsum := hRest.add (hCoef.mul (tendsto_eta_Phi2c hRH hRvM hLD hτ))
  have h12 : s0 - r + 2 = 1 + τ * I := by rw [hs0]; ring
  have hΓ1 : Gamma (1 + τ * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hval : 0 + phiRCoef r s0 * (pairAtom τ / Gamma (1 + τ * I)) =
      (cC r : ℂ) * pairAtom τ / Gamma s0 := by
    rw [zero_add, phiRCoef, h12]
    field_simp
  rw [hval] at hsum
  refine hsum.congr' (Filter.Eventually.of_forall fun η => ?_)
  have h : s0 + η - r + 2 = 1 + τ * I + η := by rw [hs0]; ring
  simp only [PhiRc, h]
  ring

end GoldbachBoundaries.PhiRProof
