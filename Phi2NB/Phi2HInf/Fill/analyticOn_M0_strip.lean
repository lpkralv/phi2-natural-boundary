import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon
import Phi2NB.HInfSupport.Paper2.Statements
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.analyticOn_M0_strip`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem analyticAt_L_hinf (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ L s := by
  let d := (s.re - 1) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hden (ρ : NontrivialZeros) (z : ℂ) (hz : z ∈ halfPlane (1 + d)) :
      d ≤ ‖z - ρ‖ := by
    have hn := Complex.re_le_norm (z - ρ)
    rw [sub_re] at hn
    change 1 + d < z.re at hz
    linarith [ρ.2.2.2]
  have hdiff : DifferentiableOn ℂ L (halfPlane (1 + d)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((summable_norm_zeroCoef_hinf hZ1 hZ2 hStir).div_const d)
    · intro ρ z hz
      exact (differentiableWithinAt_const _).div (differentiableWithinAt_id.sub_const _)
        (norm_pos_iff.mp (hd.trans_le (hden ρ z hz)))
    · exact isOpen_halfPlane _
    · intro ρ z hz
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hden ρ z hz)
  exact hdiff.analyticOnNhd (isOpen_halfPlane _) s
    (show s ∈ halfPlane (1 + d) by change 1 + d < s.re; dsimp [d]; linarith)

theorem analyticOn_M0_strip (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    AnalyticOnNhd ℂ M0 {s : ℂ | 1 < s.re ∧ s.re < 1 + (1 - Bsup)} := by
  intro s hs
  have hB : 1 / 2 ≤ Bsup := (lem_B_i hZ1).1.trans (lem_B_i hZ1).2.1
  have hs2 : s ≠ 2 := by
    intro h
    have hr : s.re = 2 := by rw [h]; norm_num
    linarith [hs.2]
  have hs10 : s - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re, one_re, zero_re] at hr
    linarith [hs.1]
  have hP : s ∉ phi2Poles := by
    rintro (h | ⟨ρ, hρ, hsum⟩)
    · exact hs2 (mem_singleton_iff.mp h)
    · have hr := M1.re_le_Bsup ((hZ1 ρ hρ).2.1)
      simp only [sub_re, one_re, conj_re] at hr
      have he := congrArg Complex.re hsum
      simp only [add_re, one_re] at he
      linarith [hs.2]
  have hψ := analyticAt_negLogDerivZeta_sub_one hs.1 hP
  have hΓ := differentiable_one_div_Gamma.analyticAt s
  have hm := (((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) s).mul hψ).div
    (analyticAt_id.sub analyticAt_const) hs10).sub
    (hΓ.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs2)))
  have hL := analyticAt_L_hinf hZ1 hZ2 hStir hs.1
  convert hm.sub (((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => 2 * c0) s).mul hL).mul hΓ) using 1
  ext z
  simp only [M0, phi2Main, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply,
    id_eq, div_eq_mul_inv, mul_inv, one_mul]

end GoldbachBoundaries.Phi2HInf
