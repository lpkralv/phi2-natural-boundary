import Phi2NB.PhiR.Fill.BCommon

/-!
# `analyticAt_phiRRest_line` (step M5)

`phiRRest r s = (B Γ(s-r+1) ψ(s-r+1) + A/(s-r) + K(s)) Γ(s)⁻¹` at `s₀ = r - 1 + iτ`, `τ ≠ 0`: `s₀ - r + 1 = iτ` is
off the real axis, so `Γ` is analytic there (`fillB_analyticAt_Gamma_of_im_ne_zero`); `ψ` is analytic at `iτ`
(`iτ ≠ 1`, `ζ(iτ) ≠ 0`); `s₀ - r = -1 + iτ ≠ 0`; `K_r` is holomorphic on `σ > r - 3/2 ∋ s₀` (`differentiableOn_KR`,
RH); `1/Γ` is entire.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillB

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- **`rest` is analytic at `r - 1 + iτ`, `τ ≠ 0`** (RH). Statement of `PhiRProof.analyticAt_phiRRest_line`,
verbatim. -/
theorem analyticAt_phiRRest_line' (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ≠ 0) :
    AnalyticAt ℂ (phiRRest r) ((r : ℂ) - 1 + τ * I) := by
  have hw : (r : ℂ) - 1 + τ * I - r + 1 = τ * I := by ring
  have hG0 : AnalyticAt ℂ Gamma ((r : ℂ) - 1 + τ * I - r + 1) := by
    rw [hw]
    exact fillB_analyticAt_Gamma_of_im_ne_zero (by simpa using hτ)
  have hG1 : AnalyticAt ℂ (fun z : ℂ => Gamma (z - r + 1)) ((r : ℂ) - 1 + τ * I) :=
    AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - r + 1) hG0 (by fun_prop)
  have hψ0 : AnalyticAt ℂ negLogDerivZeta ((r : ℂ) - 1 + τ * I - r + 1) := by
    rw [hw]
    refine analyticAt_negLogDerivZeta (fun h => ?_) (fillB_zeta_ne_zero_imI hτ)
    have := congrArg Complex.re h
    simp at this
  have hψ : AnalyticAt ℂ (fun z : ℂ => negLogDerivZeta (z - r + 1)) ((r : ℂ) - 1 + τ * I) :=
    AnalyticAt.comp (g := negLogDerivZeta) (f := fun z : ℂ => z - r + 1) hψ0 (by fun_prop)
  have hsr : (r : ℂ) - 1 + τ * I - r ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hA : AnalyticAt ℂ (fun z : ℂ => (cA r : ℂ) / (z - r)) ((r : ℂ) - 1 + τ * I) :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsr
  have hK : AnalyticAt ℂ (KR r) ((r : ℂ) - 1 + τ * I) :=
    (differentiableOn_KR hRH hr).analyticAt ((isOpen_halfPlane _).mem_nhds
      (show (r : ℝ) - 3 / 2 < ((r : ℂ) - 1 + τ * I).re by simp; norm_num))
  exact ((((analyticAt_const.mul hG1).mul hψ).add hA).add hK).mul (fillB_analyticAt_inv_Gamma _)

end GoldbachBoundaries.PhiRProof.FillB
