import Phi2NB.Phi2.Fill.BCommon

/-! The remainder on `Re w = 2/5`: `norm_verticalIntegral'_kernelL_two_fifths_le`. On the line, `|t^{-w}| = t^{-2/5}`, so
`|(2πi)⁻¹ ∫ kernelL t| ≤ (2π)⁻¹ t^{-2/5} ∫ |Γψ(2/5 + iy)| dy`. The inequality `‖∫ f‖ ≤ ∫ ‖f‖` and
`∫ c f = c ∫ f` hold with no integrability hypothesis, so the constant `(2π)⁻¹ ∫ |Γψ|` works whatever its value
(it is finite and genuine under RH, (RiemannVonMangoldt), (LogDerivZetaLocal): `fillB_integrable_kernelL_line`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The remainder on `Re w = 2/5`** (no hypotheses): `|(2πi)⁻¹ ∫_{(2/5)} kernelL t| ≤ C t^{-2/5}` for `t > 0`, with
`C = (2π)⁻¹ ∫ |Γ(2/5 + iy) ψ(2/5 + iy)| dy`, from `|t^{-w}| = t^{-2/5}` on the line. -/
theorem norm_verticalIntegral'_kernelL_two_fifths_le :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖VerticalIntegral' (kernelL t) (2 / 5)‖ ≤ C * t ^ (-(2 / 5 : ℝ)) := by
  set b : ℝ := 2 / 5 with hb
  set g : ℝ → ℂ := fun y => Gamma (b + y * I) * negLogDerivZeta (b + y * I) with hg
  refine ⟨(1 / (2 * Real.pi)) * ∫ y, ‖g y‖, fun t ht => ?_⟩
  have hnorm : ∀ y : ℝ, ‖kernelL t (b + y * I)‖ = t ^ (-b) * ‖g y‖ := by
    intro y
    simp only [kernelL, norm_mul, hg]
    rw [fillB_norm_cpow_neg ht]
    simp
  have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  calc ‖VerticalIntegral' (kernelL t) b‖
      = ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ * ‖∫ y : ℝ, kernelL t (b + y * I)‖ := by
        simp only [VerticalIntegral', VerticalIntegral, norm_smul]; ring
    _ ≤ 1 / (2 * Real.pi) * ∫ y : ℝ, ‖kernelL t (b + y * I)‖ := by
        rw [hI]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = 1 / (2 * Real.pi) * (t ^ (-b) * ∫ y : ℝ, ‖g y‖) := by
        rw [integral_congr_ae (Eventually.of_forall hnorm), integral_const_mul]
    _ = 1 / (2 * Real.pi) * (∫ y, ‖g y‖) * t ^ (-b) := by ring

end GoldbachBoundaries.Phi2Proof
