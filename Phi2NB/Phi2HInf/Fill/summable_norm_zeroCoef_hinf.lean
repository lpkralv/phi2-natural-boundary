import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.HInfSupport.Paper2.M5.Fill.summable_zeros_inv_sq
import Phi2NB.Phi2HInf.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.summable_norm_zeroCoef_hinf`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem summable_norm_zeroCoef_hinf (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    Summable (fun ρ : NontrivialZeros => ‖zeroCoef ρ‖) := by
  obtain ⟨Cm, hCm⟩ := _root_.GoldbachBoundaries.Paper2.M2.zetaMult_le_log_fullZ2 hZ1 hZ2
  obtain ⟨K, hK⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := 1) (a' := 2)
    (by norm_num) 3
  have hs := _root_.GoldbachBoundaries.Paper2.M5.summable_zeros_inv_sq_fullZ2 hZ1 hZ2
  have hfin : {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ 1}.Finite := by
    refine ((M1.finite_zeros_abs_im_le 1).preimage
      (Subtype.val_injective (p := fun ρ : ℂ => ρ ∈ NontrivialZeros)).injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, hρ⟩
  have hev : ∀ᶠ ρ : NontrivialZeros in cofinite, 1 < |(ρ : ℂ).im| := by
    rw [Filter.eventually_cofinite]
    simpa only [not_lt] using hfin
  apply (hs.mul_left (2 * |Cm| * |K|)).of_norm_bounded_eventually
  filter_upwards [hev] with ρ hρ
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  set γ := (ρ : ℂ).im with hγ
  have hm := hCm ρ ρ.2
  have hG := hK ((ρ : ℂ) + 1)
    (by simp only [add_re, one_re]; linarith [ρ.2.2.1])
    (by simp only [add_re, one_re]; linarith [ρ.2.2.2])
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro he
    have hr := ρ.2.2.1
    rw [he] at hr
    simp at hr
  rw [Gamma_add_one _ hρ0, norm_mul] at hG
  simp only [add_im, one_im, add_zero] at hG
  have hnorm : 1 ≤ ‖(ρ : ℂ)‖ := hρ.le.trans (abs_im_le_norm _)
  have hGbase : ‖Gamma (ρ : ℂ)‖ * (1 + |(ρ : ℂ).im|) ^ 3 ≤ K := by
    calc ‖Gamma (ρ : ℂ)‖ * (1 + |(ρ : ℂ).im|) ^ 3 ≤
        (‖(ρ : ℂ)‖ * ‖Gamma (ρ : ℂ)‖) * (1 + |(ρ : ℂ).im|) ^ 3 := by
          gcongr
          exact le_mul_of_one_le_left (norm_nonneg _) hnorm
      _ ≤ K := hG
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
    exact hGbase.trans (le_abs_self K)
  rw [zeroCoef, norm_mul, Complex.norm_natCast]
  calc (zetaMult (ρ : ℂ) : ℝ) * ‖Gamma (ρ : ℂ)‖ ≤ (|Cm| * (2 * (1 + |γ|))) * (|K| / (1 + |γ|) ^ 3) :=
        mul_le_mul hm' hG' (norm_nonneg _) (by positivity)
    _ = 2 * |Cm| * |K| * (1 / (1 + |γ|) ^ 2) := by
        field_simp

end GoldbachBoundaries.Phi2HInf
