import Phi2NB.Phi2.Fill.BCommon

/-! `∑_ρ |a_ρ| < ∞`: `summable_norm_zeroCoef`. `‖a_ρ‖ = m(ρ)|Γ(1/2 + iγ)|`, with
`m(ρ) ≤ C log(|γ| + 3) ≤ 2C(1 + |γ|)` (`M2.zetaMult_le_log`) and `|Γ(1/2 + iγ)|(1 + |γ|)³ ≤ K`
(`TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le`), so `‖a_ρ‖ ≤ 2CK(1 + |γ|)^{-2}`, summable by
`M5.summable_zeros_inv_sq`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`∑_ρ |m(ρ)Γ(ρ)| < ∞`** (RH, (RiemannVonMangoldt)): `|Γ(1/2 + iγ)| (1 + |γ|)³` is bounded
(`TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le`), `m(ρ) ≤ C log(|γ| + 3)` (`M2.zetaMult_le_log`) and
`∑ (1 + |γ|)^{-2} < ∞` (`M5.summable_zeros_inv_sq`). -/
theorem summable_norm_zeroCoef (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) :
    Summable (fun ρ : NontrivialZeros => ‖zeroCoef ρ‖) := by
  have hZ1 := fillB_Z1 hRH
  obtain ⟨Cm, hCm⟩ := M2.zetaMult_le_log hZ1 hRvM
  obtain ⟨K, hK⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := 1 / 2) (a' := 1 / 2)
    (by norm_num) 3
  have hs := M5.summable_zeros_inv_sq hZ1 hRvM
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_) (hs.mul_left (2 * |Cm| * |K|))
  set γ := (ρ : ℂ).im with hγ
  have hre := sigmaFinite_re_eq_half hRH ρ.2
  have hm := hCm ρ ρ.2
  have hG := hK ρ (le_of_eq hre.symm) (le_of_eq hre)
  have hy0 : 0 ≤ |γ| := abs_nonneg _
  have hpos : 0 < 1 + |γ| := by linarith
  have hlog : Real.log (|γ| + 3) ≤ 2 * (1 + |γ|) := by
    have := Real.log_le_sub_one_of_pos (show 0 < |γ| + 3 by positivity)
    linarith
  have hlog0 : 0 ≤ Real.log (|γ| + 3) := Real.log_nonneg (by linarith)
  have hm' : (zetaMult (ρ : ℂ) : ℝ) ≤ |Cm| * (2 * (1 + |γ|)) :=
    hm.trans ((mul_le_mul_of_nonneg_right (le_abs_self Cm) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg Cm)))
  have hG' : ‖Gamma (ρ : ℂ)‖ ≤ |K| / (1 + |γ|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    exact hG.trans (le_abs_self K)
  rw [zeroCoef, norm_mul, Complex.norm_natCast]
  calc (zetaMult (ρ : ℂ) : ℝ) * ‖Gamma (ρ : ℂ)‖ ≤ (|Cm| * (2 * (1 + |γ|))) * (|K| / (1 + |γ|) ^ 3) :=
        mul_le_mul hm' hG' (norm_nonneg _) (by positivity)
    _ = 2 * |Cm| * |K| * (1 / (1 + |γ|) ^ 2) := by
        field_simp

end GoldbachBoundaries.Phi2Proof
