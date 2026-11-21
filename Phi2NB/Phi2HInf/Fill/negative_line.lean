import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M5.Fill.QCommon

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.negative_line`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

lemma zeta_ne_zero_negative_strip {z : ℂ} (hzlo : -(1 / 2 : ℝ) ≤ z.re)
    (hzhi : z.re ≤ 0) : riemannZeta z ≠ 0 := by
  by_cases hz : z = 0
  · subst z
    simp [riemannZeta_zero]
  let s : ℂ := 1 - z
  have hsre : 1 ≤ s.re := by change 1 ≤ 1 - z.re; linarith
  have hspos : 0 < s.re := lt_of_lt_of_le zero_lt_one hsre
  have hsN : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have he := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs1 : s ≠ 1 := by
    intro he
    apply hz
    change 1 - z = 1 at he
    linear_combination -he
  have hfe := riemannZeta_one_sub hsN hs1
  have hcos : cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have he : s = 2 * (k : ℂ) + 1 := by
      apply mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero : (Real.pi : ℂ) ≠ 0)
      linear_combination 2 * hk
    have hre := congrArg Complex.re he
    simp only [s, sub_re, one_re, add_re, mul_re, re_ofNat, intCast_re,
      im_ofNat, intCast_im, mul_zero, sub_zero] at hre
    have hk0 : 0 ≤ k := by exact_mod_cast (show (0 : ℝ) ≤ k by linarith)
    have hk1 : k < 1 := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
    have hkzero : k = 0 := by omega
    rw [hkzero] at he
    simp only [Int.cast_zero, mul_zero, zero_add] at he
    exact hs1 he
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
    by
      intro h
      rw [cpow_eq_zero_iff] at h
      exact (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) h.1
  have hn := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow)
    (Gamma_ne_zero_of_re_pos hspos)) hcos) (riemannZeta_ne_zero_of_one_le_re hsre)
  rwa [← hfe, show 1 - s = z by dsimp [s]; ring] at hn

lemma negative_line_log_bound (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      ‖negLogDerivZeta (((-(1 / 2) : ℝ) : ℂ) + y * I)‖ ≤ K * Real.log (|y| + 3) := by
  obtain ⟨C, hC, hb⟩ := _root_.GoldbachBoundaries.Paper2.M5.exists_sep_bound_nonneg_fullZ2 hZ1 hZ2 hZ3
  have hn (y : ℝ) : riemannZeta (((-(1 / 2) : ℝ) : ℂ) + y * I) ≠ 0 :=
    zeta_ne_zero_negative_strip (by simp) (by norm_num)
  have hc := fillB_continuous_negLogDerivZeta_line (σ := -(1 / 2)) (by norm_num) hn
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨2 * C + |D|, by positivity, ?_⟩
  intro y
  have hl : 1 ≤ Real.log (|y| + 3) := M5.one_le_log_add_three (abs_nonneg _)
  by_cases hy : 2 ≤ |y|
  · have hh := hb (((-(1 / 2) : ℝ) : ℂ) + y * I) (by norm_num) (by norm_num)
      (by simpa using hy) (hn y) (1 / 2) (by norm_num) (by norm_num) (by
        intro ρ hρ _
        have h := abs_re_le_norm ((((-(1 / 2) : ℝ) : ℂ) + y * I) - ρ)
        simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, zero_mul, sub_self, add_zero] at h
        have := neg_le_abs (-(1 / 2 : ℝ) - ρ.re)
        linarith [hρ.2.1])
    simp only [add_im, ofReal_im, ofReal_re, mul_im, I_im, mul_one, I_re, mul_zero, add_zero, zero_add] at hh
    have : 0 ≤ |D| * Real.log (|y| + 3) := mul_nonneg (abs_nonneg _) (by linarith)
    linarith
  · have h := hD y (abs_le.mp (not_le.mp hy).le)
    have : |D| ≤ (2 * C + |D|) * Real.log (|y| + 3) := by nlinarith [abs_nonneg D]
    exact h.trans ((le_abs_self D).trans this)

lemma integrable_kernelL_negative (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => kernelL x (((-(1 / 2) : ℝ) : ℂ) + y * I)) := by
  obtain ⟨K, hK, hb⟩ := negative_line_log_bound hZ1 hZ2 hZ3
  let w : ℝ → ℂ := fun y => ((-(1 / 2) : ℝ) : ℂ) + y * I
  have hw (y : ℝ) : 1 / 2 ≤ ‖w y‖ := by
    have h := abs_re_le_norm (w y)
    norm_num [w] at h ⊢
    exact h
  have hw0 (y : ℝ) : w y ≠ 0 := by
    intro he
    have h := hw y
    rw [he, norm_zero] at h
    norm_num at h
  let q : ℝ → ℂ := fun y => (x : ℂ) ^ (-w y) * negLogDerivZeta (w y) / w y
  have hqc : Continuous q := by
    change Continuous (fun y => ((x : ℂ) ^ (-w y) * negLogDerivZeta (w y)) / w y)
    apply Continuous.div _ (show Continuous w by dsimp [w]; fun_prop) hw0
    apply Continuous.mul _ (fillB_continuous_negLogDerivZeta_line (σ := -(1 / 2)) (by norm_num)
      (fun y => zeta_ne_zero_negative_strip (by simp) (by norm_num)))
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (TIdentity.differentiableAt_ofReal_cpow_neg hx _).continuousAt.comp
      (f := w) (by fun_prop)
  have hqb (y : ℝ) : ‖q y‖ ≤ (4 * K * x ^ (1 / 2 : ℝ)) * (1 + |y|) := by
    have hl : Real.log (|y| + 3) ≤ 2 * (1 + |y|) := by
      have := Real.log_le_sub_one_of_pos (show 0 < |y| + 3 by positivity)
      linarith [abs_nonneg y]
    have hp : ‖(x : ℂ) ^ (-w y)‖ = x ^ (1 / 2 : ℝ) := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]
      simp [w]
    dsimp [q]
    rw [norm_div, norm_mul, hp]
    calc x ^ (1 / 2 : ℝ) * ‖negLogDerivZeta (w y)‖ / ‖w y‖
        ≤ x ^ (1 / 2 : ℝ) * (K * Real.log (|y| + 3)) / (1 / 2) := by
          gcongr
          · exact mul_nonneg (Real.rpow_nonneg hx.le _)
              (mul_nonneg hK (Real.log_nonneg (by linarith [abs_nonneg y])))
          · exact hb y
          · exact hw y
      _ ≤ x ^ (1 / 2 : ℝ) * (K * (2 * (1 + |y|))) / (1 / 2) := by gcongr
      _ = _ := by ring
  have hi := TIdentity.integrable_Gamma_mul_of_bound (by norm_num : 0 < (1 / 2 : ℝ)) hqc hqb
  convert hi using 1
  funext y
  have he : ((1 / 2 : ℝ) : ℂ) + y * I = w y + 1 := by dsimp [w]; push_cast; ring
  rw [he, Gamma_add_one _ (hw0 y)]
  have hz0 := hw0 y
  dsimp [q, kernelL, w] at hz0 ⊢
  field_simp [hz0]

lemma norm_Gamma_negative_strip (n : ℕ) :
    ∃ K : ℝ, ∀ z : ℂ, -(1 / 2 : ℝ) ≤ z.re → z.re ≤ 2 → 1 ≤ |z.im| →
      ‖Gamma z‖ * (1 + |z.im|) ^ n ≤ K := by
  obtain ⟨K, hK⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le
    (a := 1 / 2) (a' := 3) (by norm_num) n
  refine ⟨K, ?_⟩
  intro z hzlo hzhi hzim
  have hz0 : z ≠ 0 := by intro he; norm_num [he] at hzim
  have hz : 1 ≤ ‖z‖ := hzim.trans (abs_im_le_norm _)
  have h := hK (z + 1) (by simp; linarith) (by simp; linarith)
  rw [Gamma_add_one _ hz0, norm_mul] at h
  simp only [add_im, one_im, add_zero] at h
  calc
    ‖Gamma z‖ * (1 + |z.im|) ^ n ≤ (‖z‖ * ‖Gamma z‖) * (1 + |z.im|) ^ n := by
      gcongr
      exact le_mul_of_one_le_left (norm_nonneg _) hz
    _ ≤ K := h

end GoldbachBoundaries.Phi2HInf
