import Phi2NB.PhiR.Fill.BCommon
import Phi2NB.Phi2.Proof.M3Radial

/-!
# `tendsto_eta_Phi2c` (step M5)

`Phi2c = phi2Main + Hphi2`. `η Hphi2(1 + iτ + η) → μ{τ}/Γ(1 + iτ)` is `Phi2Proof.tendsto_eta_Hphi2`. For `τ ≠ 0`,
`phi2Main(s) = 2ψ(s-1)/(s-1) - 1/(Γ(s)(s-2))` is analytic at `1 + iτ`: `ψ` is analytic at `iτ` (`iτ ≠ 1`,
`ζ(iτ) ≠ 0` by `fillB_zeta_ne_zero_imI`), `iτ ≠ 0`, `1 + iτ ≠ 2`, `1/Γ` entire. So `η phi2Main(1 + iτ + η) → 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillB

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof GoldbachBoundaries.Paper2

/-- `phi2Main` is analytic at `1 + iτ`, `τ ≠ 0` (no RH). -/
theorem fillB_analyticAt_phi2Main_line {τ : ℝ} (hτ : τ ≠ 0) : AnalyticAt ℂ phi2Main (1 + τ * I) := by
  have h1 : 1 + (τ : ℂ) * I - 1 = τ * I := by ring
  have hτI : (τ : ℂ) * I ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hτ) I_ne_zero
  have hψ0 : AnalyticAt ℂ negLogDerivZeta (1 + (τ : ℂ) * I - 1) := by
    rw [h1]
    refine analyticAt_negLogDerivZeta (fun h => ?_) (fillB_zeta_ne_zero_imI hτ)
    have := congrArg Complex.re h
    simp at this
  have hψ : AnalyticAt ℂ (fun s : ℂ => negLogDerivZeta (s - 1)) (1 + τ * I) :=
    AnalyticAt.comp (g := negLogDerivZeta) (f := fun s : ℂ => s - 1) hψ0 (by fun_prop)
  have hs01 : 1 + (τ : ℂ) * I - 1 ≠ 0 := by rw [h1]; exact hτI
  have hs02 : 1 + (τ : ℂ) * I - 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  have hA : AnalyticAt ℂ (fun s : ℂ => 2 * negLogDerivZeta (s - 1) / (s - 1) - (Gamma s)⁻¹ * (s - 2)⁻¹)
      (1 + τ * I) :=
    ((analyticAt_const.mul hψ).div (analyticAt_id.sub analyticAt_const) hs01).sub
      ((fillB_analyticAt_inv_Gamma _).mul ((analyticAt_id.sub analyticAt_const).inv hs02))
  refine hA.congr (Eventually.of_forall fun z => ?_)
  simp only [phi2Main, one_div, mul_inv]

/-- **Radial limit of `Phi2c`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)), `τ ≠ 0`. Statement of `PhiRProof.tendsto_eta_Phi2c`, verbatim. -/
theorem tendsto_eta_Phi2c' (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * Phi2c (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I))) := by
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hs : Tendsto (fun η : ℝ => 1 + (τ : ℂ) * I + η) (𝓝[>] 0) (𝓝 (1 + τ * I)) := by
    simpa using (tendsto_const_nhds (x := 1 + (τ : ℂ) * I)).add hη
  have hM : Tendsto (fun η : ℝ => (η : ℂ) * phi2Main (1 + τ * I + η)) (𝓝[>] 0) (𝓝 0) := by
    have hc := (fillB_analyticAt_phi2Main_line hτ).continuousAt.tendsto.comp hs
    simpa using hη.mul hc
  have hsum := hM.add (tendsto_eta_Hphi2 hRH hRvM hLD τ)
  rw [zero_add] at hsum
  refine hsum.congr' (Eventually.of_forall fun η => ?_)
  simp only [Phi2c]
  ring

end GoldbachBoundaries.PhiRProof.FillB
