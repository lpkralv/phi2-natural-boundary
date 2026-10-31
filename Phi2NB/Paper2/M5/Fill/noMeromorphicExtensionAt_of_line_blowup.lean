import Phi2NB.Paper2.Defs
import Phi2NB.Defs
import Phi2NB.ZetaRealNonvanishing
import Phi2NB.SigmaFinite
import Phi2NB.SigmaMeromorphic
import Phi2NB.TIdentity.Assembly
import Phi2NB.Density
import Phi2NB.TBoundary
import Mathlib.MeasureTheory.Group.Prod
import Phi2NB.TIdentity.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.Module.Cardinality
import Phi2NB.Paper2.M1.Fill.BCommon
import Phi2NB.TIdentity.G8d_ContourShift
import Phi2NB.Paper2.M1.Fill.sum_zetaMult_window_le
import Phi2NB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles
import Phi2NB.Paper2.M2.Fill.ncard_zeros_im_Icc_le
import Phi2NB.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.Paper2.M2.Fill.ACommon
import PrimeNumberTheoremAnd.Consequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Phi2NB.Paper2.M4b.Fill.BCommon
import Phi2NB.Paper2.M4b.Fill.isBigO_mul_sub_residue
import Phi2NB.Paper2.M5.Fill.order_residue_of_codiscrete_line
import Phi2NB.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep
import Phi2NB.Paper2.M5.Fill.exists_sep_height
import Phi2NB.Paper2.M5.Fill.QCommon
import Phi2NB.Paper2.M5.Fill.rectangleIntegral'_eq_sum_of_simplePoles_rect
import Phi2NB.Paper2.M5.Fill.summable_zeros_inv_sq

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M5
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem noMeromorphicExtensionAt_of_line_blowup {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F HH) {τ : ℝ}
    (h : ∀ ε > 0, ∃ τ₀ : ℝ, τ₀ ≠ τ ∧ |τ₀ - τ| < ε ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun η : ℝ => (η : ℂ) * F (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 c)) :
    NoMeromorphicExtensionAt F HH (1 + τ * I) := by
  rintro r hr ⟨f, hf, hfF⟩
  set s₁ : ℂ := 1 + τ * I with hs₁
  obtain ⟨δ, hδ, hδan⟩ : ∃ δ > 0, ∀ z ∈ ball s₁ δ, z ≠ s₁ → AnalyticAt ℂ f z := by
    have hev := (hf s₁ (mem_ball_self hr)).eventually_analyticAt
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
    obtain ⟨δ, hδ, hev⟩ := hev
    exact ⟨δ, hδ, fun z hz hne => hev z hz hne⟩
  obtain ⟨τ₀, hne, hlt, c, hc, hlim⟩ := h (min δ (r / 2)) (lt_min hδ (by linarith))
  set s₀ : ℂ := 1 + τ₀ * I with hs₀
  have hdist : dist s₀ s₁ = |τ₀ - τ| := by
    rw [dist_eq_norm]
    have heq : s₀ - s₁ = ((τ₀ - τ : ℝ) : ℂ) * I := by
      rw [hs₀, hs₁]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hnot : s₀ ≠ s₁ := by
    intro heq
    apply hne
    have him := congrArg Complex.im heq
    simpa [hs₀, hs₁] using him
  have hsub : ball s₀ (r / 2) ⊆ ball s₁ r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z s₁ ≤ dist z s₀ + dist s₀ s₁ := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hz (by rw [hdist]; exact hlt.trans_le (min_le_right _ _))
      _ = r := by ring
  have hpole := order_residue_of_codiscrete_line hF (s₀ := s₀)
    (by simp [hs₀]) (by linarith : 0 < r / 2) (hf.mono_set hsub)
    (hfF.filter_mono (Filter.codiscreteWithin_mono (inter_subset_inter_left HH hsub))) hc hlim
  have han := hδan s₀ (by rw [mem_ball, hdist]; exact hlt.trans_le (min_le_left _ _)) hnot
  have hnonneg := han.meromorphicOrderAt_nonneg
  rw [hpole.1] at hnonneg
  have hneg : (-1 : WithTop ℤ) < 0 := by decide
  exact (not_le_of_gt hneg) hnonneg

end GoldbachBoundaries.Paper2.M5
