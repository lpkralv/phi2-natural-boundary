import Phi2NB.PhiR.Fill.BCommon

/-!
# `analyticOnNhd_PhiRc` (step M2)

`PhiRc r = f₄ · Phi2c(· - r + 2) + rest` is analytic at every `s` with `Re s > r - 1`, `s ∉ phiRPoles r` (RH):
`f₄` is analytic on `σ > r - 2` (`analyticAt_phiRCoef`); `s - r + 2 ∈ ℍ ∖ phi2Poles`, where `Phi2c` is analytic
(`phi2_continuation`); `Γ(s - r + 1)` is analytic (`Re > 0`); `ψ(s - r + 1)` is analytic
(`fillB_analyticAt_negLogDerivZeta_shift`); `A_r/(s - r)` is analytic (`s ≠ r`); `K_r` is holomorphic on
`σ > r - 3/2` (`differentiableOn_KR`); `1/Γ` is entire.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillB

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- **`PhiRc r` is analytic on `σ > r - 1` off the poles** (RH). Statement of
`PhiRProof.analyticOnNhd_PhiRc`, verbatim. -/
theorem analyticOnNhd_PhiRc' (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    AnalyticOnNhd ℂ (PhiRc r) (halfPlane ((r : ℝ) - 1) \ phiRPoles r) := by
  rintro s ⟨hs, hP⟩
  have hs' : (r : ℝ) - 1 < s.re := hs
  have hK : AnalyticAt ℂ (KR r) s :=
    (differentiableOn_KR hRH hr).analyticAt ((isOpen_halfPlane _).mem_nhds
      (show (r : ℝ) - 3 / 2 < s.re by linarith))
  have hP2 : AnalyticAt ℂ (fun z : ℂ => Phi2c (z - r + 2)) s :=
    AnalyticAt.comp (g := Phi2c) (f := fun z : ℂ => z - r + 2)
      ((phi2_continuation hRH).2.2.1 _ (fillB_mem_HH_diff_phi2Poles hs' hP)) (by fun_prop)
  have hG1 : AnalyticAt ℂ (fun z : ℂ => Gamma (z - r + 1)) s :=
    AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - r + 1)
      (fillB_analyticAt_Gamma_of_re_pos (by simp; linarith)) (by fun_prop)
  have hψ := fillB_analyticAt_negLogDerivZeta_shift hs' hP
  have hsr : s - r ≠ 0 := fun h => hP (Or.inl (by rw [mem_singleton_iff]; linear_combination h))
  have hA : AnalyticAt ℂ (fun z : ℂ => (cA r : ℂ) / (z - r)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsr
  have hRest : AnalyticAt ℂ (phiRRest r) s :=
    ((((analyticAt_const.mul hG1).mul hψ).add hA).add hK).mul (fillB_analyticAt_inv_Gamma s)
  exact ((fillB_analyticAt_phiRCoef (by linarith)).mul hP2).add hRest

end GoldbachBoundaries.PhiRProof.FillB
