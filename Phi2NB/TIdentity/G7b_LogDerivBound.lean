import Phi2NB.TIdentity.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# Logarithmic-derivative bound from Borel–Carathéodory

The helper lemmas `borelCaratheodory'`, `cauchy_formula_deriv`, `DerivativeBound`,
`BorelCaratheodoryDeriv` and `LogOfAnalyticFunction` are copied (Apache-2.0) from PNT+
`PrimeNumberTheoremAnd/StrongPNT.lean` (upstreamed there from math-inc/strongpnt), whose import chain this
library avoids; blueprint attributes are dropped. They are placed in the namespace
`GoldbachBoundaries.TIdentity.G7b` to avoid clashes.

Constant check. `BorelCaratheodoryDeriv`: if `J` is analytic on `ball 0 R`, `J 0 = 0`,
`Re J ≤ A` there (`A > 0`), then `‖J'‖ ≤ 16 A R²/(R-r)³` on `closedBall 0 r` (via Cauchy on the
circle of radius `r' = (R+r)/2` and Borel–Carathéodory there: `4A(R+r)²/(R-r)³ ≤ 16AR²/(R-r)³`).
With `J` a logarithm of `f(z₀ + ·)/f(z₀)`, `Re J = log|f| - log|f z₀| ≤ log M = A > 0` (as
`M > 1`), and `J' = f'/f`. This is exactly the constant in the statement, `16 log M R²/(R-r)³`.
-/

noncomputable section

open Complex Set Metric

namespace GoldbachBoundaries

namespace TIdentity

namespace G7b

theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn,
      fun z hz => by rw [Set.mem_ofPred_eq]; linarith [realPartBounded z hz],
      Rpos, by exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hyp_z) hyp_r),
      zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact Continuous.div_const
        ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const) _
    refine le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ?_
    exact Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith)
    (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr

theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
    _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
      DerivativeBound Mpos rpos (by linarith) (by linarith)
        analytic_f zeroAtZero realPartBounded hyp_z
    _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
      have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
      rw [this]; bound

theorem LogOfAnalyticFunction {r R : ℝ} {B : ℂ → ℂ}
    (zero_lt_r : 0 < r) (r_lt_R : r < R)
    (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ), (AnalyticOnNhd ℂ J_B (Metric.ball 0 R)) ∧
      (J_B 0 = 0) ∧
      (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
      (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
  obtain ⟨J_B, hJB⟩ : ∃ J_B : ℂ → ℂ, (∀ z ∈ Metric.ball 0 R, (HasDerivAt J_B (deriv B z / B z) z)) ∧
      J_B 0 = 0 ∧ (∀ z ∈ Metric.ball 0 R, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    set f : ℂ → ℂ := fun z => deriv B z / B z;
    have hf : AnalyticOnNhd ℂ f (Metric.ball 0 R) :=
      (BanalyticOnNhdOfDR.deriv.mono Metric.ball_subset_closedBall).div
        (BanalyticOnNhdOfDR.mono Metric.ball_subset_closedBall)
        (fun z hz => Bnonzero z <| Metric.ball_subset_closedBall hz)
    obtain ⟨J, hJ⟩ := DifferentiableOn.isExactOn_ball hf.differentiableOn
    refine ⟨fun z ↦ J z - J 0, fun z hz ↦ (hJ z hz).sub_const _, by simp, ?_⟩
    set H : ℂ → ℂ := fun z => Complex.exp (J z - J 0) / B z
    have hJB_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt (fun z ↦ J z - J 0) (f z) z :=
      fun z hz ↦ (hJ z hz).sub_const _
    have hH_deriv : ∀ z ∈ Metric.ball 0 R, HasDerivAt H 0 z := by
      intro z hz
      have := (Complex.hasDerivAt_exp _).comp z (hJB_deriv z hz)
      convert! this.div (BanalyticOnNhdOfDR.differentiableOn.differentiableAt
        (Metric.closedBall_mem_nhds_of_mem hz) |>.hasDerivAt)
        (Bnonzero z <| Metric.ball_subset_closedBall hz) using 1
      ring_nf!; grind
    have hH_const : ∀ z ∈ Metric.ball 0 R, H z = H 0 := by
      intro z hz
      have h_diffOn : DifferentiableOn ℂ H (Metric.ball 0 R) :=
        fun z hz ↦ (hH_deriv z hz).differentiableAt.differentiableWithinAt
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball 0 R) h_diffOn ?_ hz
        (Metric.mem_ball_self (Metric.pos_of_mem_ball hz))
      intro x hx
      rw [fderivWithin_of_isOpen Metric.isOpen_ball hx,
        ← ContinuousLinearMap.toSpanSingleton_zero]
      exact (hH_deriv x hx).hasFDerivAt.fderiv
    have h_exp_re : ∀ z ∈ Metric.ball 0 R, Real.exp (J z - J 0).re = ‖B z‖ / ‖B 0‖ := by
      intro z hz
      have hc := hH_const z hz
      simp only [H, sub_self, Complex.exp_zero, one_div] at hc
      rw [div_eq_iff (Bnonzero z (Metric.ball_subset_closedBall hz)), mul_comm] at hc
      rw [← Complex.norm_exp, ← norm_div, div_eq_mul_inv]
      exact enorm_eq_iff_norm_eq.mp (congrArg enorm hc)
    intro z hz
    have hBz := Bnonzero z (Metric.ball_subset_closedBall hz)
    have hB0 := Bnonzero 0 (by norm_num; linarith)
    rw [← Real.log_div (norm_ne_zero_iff.mpr hBz) (norm_ne_zero_iff.mpr hB0),
      ← h_exp_re z hz, Real.log_exp]
  have hmem : ∀ z, z ∈ Metric.ball (0 : ℂ) r → z ∈ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [Metric.mem_ball] at hz
    linarith
  refine ⟨J_B, fun z hz => ?_, hJB.2.1, fun z hz => ?_, hJB.2.2⟩
  · exact DifferentiableOn.analyticAt
      (fun w hw ↦ (hJB.1 w hw).differentiableAt.differentiableWithinAt)
      (IsOpen.mem_nhds Metric.isOpen_ball hz)
  · exact (hJB.1 z (Metric.closedBall_subset_ball r_lt_R hz)).deriv

end G7b

/-- **Logarithmic-derivative bound from Borel–Carathéodory** (standard; Titchmarsh §3.9,
Lemma α; Montgomery–Vaughan Lemma 6.3 has the same shape). If `f` is analytic and zero-free on the
closed disc `|z - z₀| ≤ R` and `|f| ≤ M |f(z₀)|` there (`M > 1`), then on `|z - z₀| ≤ r < R`,
`|f'/f| ≤ 16 log M · R² / (R - r)³`.

Proof. Translate to `z₀ = 0`. `LogOfAnalyticFunction` gives `J` analytic on `ball 0 R`, `J 0 = 0`,
`J' = f'/f` on `closedBall 0 r`, `Re J = log|f| - log|f 0| ≤ log M`; then `BorelCaratheodoryDeriv`
(with `M := log M > 0`) gives exactly `‖J'‖ ≤ 16 log M R²/(R-r)³`. -/
theorem norm_logDeriv_le_of_closedBall {f : ℂ → ℂ} {z₀ : ℂ} {r R M : ℝ} (hr : 0 < r)
    (hrR : r < R) (hM : 1 < M) (hf : AnalyticOnNhd ℂ f (closedBall z₀ R))
    (hne : ∀ z ∈ closedBall z₀ R, f z ≠ 0) (hbound : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∀ z ∈ closedBall z₀ r, ‖deriv f z / f z‖ ≤ 16 * Real.log M * R ^ 2 / (R - r) ^ 3 := by
  intro z hz
  set g : ℂ → ℂ := fun w => f (w + z₀) with hgdef
  have hmem : ∀ w ∈ closedBall (0 : ℂ) R, w + z₀ ∈ closedBall z₀ R := by
    intro w hw
    simpa [mem_closedBall, dist_eq_norm] using hw
  have hg : AnalyticOnNhd ℂ g (closedBall 0 R) := fun w hw =>
    (hf _ (hmem w hw)).comp (f := fun w : ℂ => w + z₀) (analyticAt_id.add analyticAt_const)
  have hgne : ∀ w ∈ closedBall (0 : ℂ) R, g w ≠ 0 := fun w hw => hne _ (hmem w hw)
  obtain ⟨J, hJan, hJ0, hJd, hJre⟩ := G7b.LogOfAnalyticFunction hr hrR hg hgne
  have hg0 : g 0 = f z₀ := by simp [hgdef]
  have hf0 : f z₀ ≠ 0 := hne z₀ (mem_closedBall_self (by linarith))
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hRe : ∀ u ∈ ball (0 : ℂ) R, (J u).re ≤ Real.log M := by
    intro u hu
    rw [← hJre u hu, hg0]
    have hu' : u + z₀ ∈ closedBall z₀ R := hmem u (ball_subset_closedBall hu)
    have hgu : 0 < ‖g u‖ := norm_pos_iff.mpr (hgne u (ball_subset_closedBall hu))
    have h1 : ‖g u‖ ≤ M * ‖f z₀‖ := hbound _ hu'
    have h2 : Real.log ‖g u‖ ≤ Real.log (M * ‖f z₀‖) := Real.log_le_log hgu h1
    rw [Real.log_mul (by linarith) (norm_ne_zero_iff.mpr hf0)] at h2
    linarith
  have hw : z - z₀ ∈ closedBall (0 : ℂ) r := by
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hB := G7b.BorelCaratheodoryDeriv hlogM hr hrR (hJan.analyticOn) hJ0 hRe hw
  rw [hJd _ hw] at hB
  have hdg : deriv g (z - z₀) = deriv f z := by
    rw [hgdef, deriv_comp_add_const]; simp
  have hgz : g (z - z₀) = f z := by simp [hgdef]
  rwa [hdg, hgz] at hB
