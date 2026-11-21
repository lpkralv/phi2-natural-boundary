import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M5.Fill.QCommon
import Phi2NB.HInfSupport.Paper2.M5.Fill.exists_sep_height
import Phi2NB.Phi2HInf.Fill.negative_line

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.good_height`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem negative_strip_good_height (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ C : ℝ, ∀ Y : ℝ, 3 ≤ Y → ∃ Y' ∈ Icc Y (Y + 1), ∀ x ∈ Icc (-(1 / 2 : ℝ)) 2,
      riemannZeta (x + Y' * I) ≠ 0 ∧ riemannZeta (x - Y' * I) ≠ 0 ∧
      ‖negLogDerivZeta (x + Y' * I)‖ ≤ C * Real.log Y ^ 2 ∧
      ‖negLogDerivZeta (x - Y' * I)‖ ≤ C * Real.log Y ^ 2 := by
  obtain ⟨Ks, hKs0, hKs⟩ := _root_.GoldbachBoundaries.Paper2.M5.exists_sep_bound_nonneg_fullZ2 hZ1 hZ2 hZ3
  obtain ⟨Cs, hCs0, hCs⟩ := _root_.GoldbachBoundaries.Paper2.M5.exists_sep_height_fullZ2 hZ1 hZ2
  refine ⟨2 * Ks * (1 + Cs), fun Y hY => ?_⟩
  obtain ⟨Y', hY'mem, hsep⟩ := hCs Y hY
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set δ := 1 / (1 + Cs * L) with hδdef
  have hden : 0 < 1 + Cs * L := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hden]
    nlinarith
  have hY'3 : 3 ≤ Y' := le_trans hY hY'mem.1
  have key : ∀ w : ℂ, -(1 / 2 : ℝ) ≤ w.re → w.re ≤ 2 → |w.im| = Y' →
      (∀ ρ ∈ NontrivialZeros, δ ≤ |w.im - ρ.im|) →
      riemannZeta w ≠ 0 ∧ ‖negLogDerivZeta w‖ ≤ 2 * Ks * (1 + Cs) * L ^ 2 := by
    intro w hw1 hw2 hwim hws
    have hζ : riemannZeta w ≠ 0 := by
      by_cases h1 : 1 ≤ w.re
      · exact riemannZeta_ne_zero_of_one_le_re h1
      · by_cases h0 : w.re ≤ 0
        · exact zeta_ne_zero_negative_strip hw1 h0
        · intro hz
          have := hws w ⟨hz, lt_of_not_ge h0, lt_of_not_ge h1⟩
          rw [sub_self, abs_zero] at this
          linarith
    refine ⟨hζ, ?_⟩
    have h := hKs w (by linarith) (by linarith) (by rw [hwim]; linarith) hζ δ hδ0 hδ1 (fun ρ hρ _ => by
      have h1 := Complex.abs_im_le_norm (w - ρ)
      rw [Complex.sub_im] at h1
      exact (hws ρ hρ).trans h1)
    rw [hwim] at h
    have hlogY : Real.log (Y' + 3) ≤ 2 * L := by
      rw [hLdef, show (2 : ℝ) * Real.log Y = Real.log (Y ^ 2) by rw [Real.log_pow]; push_cast; ring]
      refine Real.log_le_log (by linarith) ?_
      nlinarith [hY'mem.2]
    have hinvδ : 1 / δ ≤ (1 + Cs) * L := by
      rw [hδdef, one_div_one_div]
      nlinarith
    have hl0 : 0 ≤ Real.log (Y' + 3) := Real.log_nonneg (by linarith)
    calc ‖negLogDerivZeta w‖ ≤ Ks / δ * Real.log (Y' + 3) := h
      _ = Ks * (1 / δ) * Real.log (Y' + 3) := by ring
      _ ≤ Ks * ((1 + Cs) * L) * (2 * L) := by gcongr
      _ = 2 * Ks * (1 + Cs) * L ^ 2 := by ring
  refine ⟨Y', hY'mem, fun x hx => ?_⟩
  have hp := key ((x : ℂ) + Y' * I) (by simpa using hx.1) (by simpa using hx.2)
    (by rw [show ((x : ℂ) + Y' * I).im = Y' by simp]; exact abs_of_nonneg (by linarith))
    (fun ρ hρ => by
      have h := hsep 1 le_rfl (by norm_num) ρ hρ
      rw [show ((x : ℂ) + Y' * I).im = Y' by simp]
      simpa using h)
  have hm := key ((x : ℂ) - Y' * I) (by simpa using hx.1) (by simpa using hx.2)
    (by rw [show ((x : ℂ) - Y' * I).im = -Y' by simp, abs_neg]; exact abs_of_nonneg (by linarith))
    (fun ρ hρ => by
      have h := hsep 1 le_rfl (by norm_num) (conj ρ) (conj_mem_nontrivialZeros hρ)
      rw [show ((x : ℂ) - Y' * I).im = -Y' by simp]
      rw [Complex.conj_im] at h
      calc δ ≤ |((1 : ℕ) : ℝ) * Y' - -ρ.im| := h
        _ = |-Y' - ρ.im| := by
            rw [← abs_neg]; congr 1; push_cast; ring)
  exact ⟨hp.1, hm.1, by rw [hLdef] at hp; exact hp.2, by rw [hLdef] at hm; exact hm.2⟩

end GoldbachBoundaries.Phi2HInf
