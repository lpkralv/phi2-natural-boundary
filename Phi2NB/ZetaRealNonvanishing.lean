import Mathlib
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

/-!
# `ζ(x) < 0` for real `x ∈ (0, 1)`

Mathlib proves `ζ(s) ≠ 0` only for `re s ≥ 1`. Here we prove that `ζ` is real and negative on the
open interval `(0, 1)`, hence non-vanishing there; in particular `ζ(1/2) ≠ 0`.

Route: the Abel-summation formula
`ζ(s) = 1 + 1/(s - 1) - s ∫_{(1,∞)} {u} u^{-s-1} du`
(PNT+, `riemannZeta_eq_zetaAbelContinuationFormula`, proved there on `re s > 1/10`). We first
extend it to the whole half-plane `re s > 0`, `s ≠ 1`, by the identity theorem, reusing PNT+'s
`riemannZeta_abel_integral` (the formula on `re s > 1`) and
`ZetaAbelFractKernel.integral_analytic` (analyticity of the integral on `re s > 0`). For real
`x ∈ (0, 1)` the integral is the integral of a non-negative real function, so
`ζ(x) = x/(x - 1) - x·(non-negative real) < 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace GoldbachBoundaries

/-- The punctured half-plane `{s : s ≠ 1, re s > 0}`. -/
private def posDomain : Set ℂ := {s | s ≠ (1 : ℂ) ∧ 0 < s.re}

private lemma isPreconnected_posDomain : IsPreconnected posDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := 0) (p := (1 : ℂ)) (by simp)).isConnected.isPreconnected using 1
  ext z; simp [posDomain, and_comm]

private lemma analyticOnNhd_formula_posDomain :
    AnalyticOnNhd ℂ zetaAbelContinuationFormula posDomain := by
  intro s ⟨hs_ne, hs_re⟩
  exact analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hs_ne)) |>.sub
    (analyticAt_id.mul (ZetaAbelFractKernel.integral_analytic s hs_re))

/-- The Abel formula for `ζ` on the whole half-plane `re s > 0`, `s ≠ 1`. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos {s : ℂ} (hs1 : s ≠ 1)
    (hs : 0 < s.re) : riemannZeta s = zetaAbelContinuationFormula s := by
  have hζ : AnalyticOnNhd ℂ riemannZeta posDomain := fun z hz => analyticOn_riemannZeta z hz.1
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hζ analyticOnNhd_formula_posDomain
    isPreconnected_posDomain (by simp [posDomain]) hEq) ⟨hs1, hs⟩

/-- For real `x > 0`, the Abel integral is the integral of a non-negative real function. -/
private lemma abel_integral_ofReal {x : ℝ} :
    (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel (x : ℂ) u) =
      ((∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-x - 1) : ℝ) : ℂ) := by
  refine (setIntegral_congr_fun (g := fun u => ((Int.fract u * u ^ (-x - 1) : ℝ) : ℂ))
    measurableSet_Ioi fun u hu => ?_).trans (integral_ofReal (𝕜 := ℂ))
  have hu0 : (0 : ℝ) ≤ u := le_of_lt (lt_trans one_pos hu)
  simp only [zetaAbelFractKernel, ofReal_mul, ofReal_cpow hu0]
  push_cast
  ring_nf

private lemma abel_integral_real_nonneg (x : ℝ) :
    0 ≤ ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-x - 1) := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  exact mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg (le_of_lt (lt_trans one_pos hu)) _)

/-- On `(0, 1)`, `ζ` is real: `ζ(x) = x/(x - 1) - x · I(x)` with `I(x) ≥ 0` real. -/
private lemma riemannZeta_ofReal_eq {x : ℝ} (hx : x ∈ Ioo 0 1) :
    riemannZeta x = ((x / (x - 1) - x * ∫ u in Ioi (1 : ℝ), Int.fract u * u ^ (-x - 1) : ℝ) : ℂ) := by
  have hx1 : (x : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [hx.2]
  have hsub : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hsubR : x - 1 ≠ 0 := by linarith [hx.2]
  rw [riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos hx1 (by simpa using hx.1),
    zetaAbelContinuationFormula, abel_integral_ofReal]
  push_cast
  field_simp
  ring

/-- **`ζ` is real and negative on `(0, 1)`.** -/
theorem riemannZeta_re_neg_and_im_zero_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (riemannZeta x).re < 0 ∧ (riemannZeta x).im = 0 := by
  rw [riemannZeta_ofReal_eq hx, ofReal_re, ofReal_im]
  refine ⟨?_, rfl⟩
  have h1 : x / (x - 1) < 0 := div_neg_of_pos_of_neg hx.1 (by linarith [hx.2])
  have h2 := mul_nonneg hx.1.le (abel_integral_real_nonneg x)
  linarith

/-- `ζ(x) ≠ 0` for real `x ∈ (0, 1)`. -/
theorem riemannZeta_ne_zero_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) : riemannZeta x ≠ 0 := by
  intro h
  have := (riemannZeta_re_neg_and_im_zero_of_mem_Ioo hx).1
  rw [h, zero_re] at this
  exact lt_irrefl 0 this

end GoldbachBoundaries
