import Phi2NB.Phi2.Fill.BCommon

/-! Good heights for `ψ`: `negLogDerivZeta_good_height`. `M5.exists_sep_height` (with `n = 1`) gives
`Y' ∈ [Y, Y + 1]` with `|Y' - γ| ≥ δ = 1/(1 + C log Y)` for every zero; on `x ± iY'`,
`1/3 ≤ x ≤ 1`, `ζ ≠ 0` (a zero there would have ordinate `±Y'`) and `M5.exists_sep_bound_nonneg` gives
`|ψ| ≤ K δ⁻¹ log(Y' + 3) ≤ 2K(1 + C) log² Y`. The lower side uses `ρ̄` (`conj_mem_nontrivialZeros`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Good heights** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)): for every `Y ≥ 3` some `Y' ∈ [Y, Y + 1]` has no zero on the horizontal
segments `x ± iY'`, `1/3 ≤ x ≤ 1`, and `|ψ| ≤ C log² Y` there. From `M5.exists_sep_height` (`n = 1`) and
`M5.exists_sep_bound_nonneg`. -/
theorem negLogDerivZeta_good_height (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) :
    ∃ C : ℝ, ∀ Y : ℝ, 3 ≤ Y → ∃ Y' ∈ Icc Y (Y + 1), ∀ x ∈ Icc (1 / 3 : ℝ) 1,
      riemannZeta (x + Y' * I) ≠ 0 ∧ riemannZeta (x - Y' * I) ≠ 0 ∧
      ‖negLogDerivZeta (x + Y' * I)‖ ≤ C * Real.log Y ^ 2 ∧
      ‖negLogDerivZeta (x - Y' * I)‖ ≤ C * Real.log Y ^ 2 := by
  have hZ1 := fillB_Z1 hRH
  obtain ⟨Ks, hKs0, hKs⟩ := M5.exists_sep_bound_nonneg hZ1 hRvM hLD
  obtain ⟨Cs, hCs0, hCs⟩ := M5.exists_sep_height hZ1 hRvM
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
  have key : ∀ w : ℂ, 1 / 3 ≤ w.re → w.re ≤ 1 → |w.im| = Y' →
      (∀ ρ ∈ NontrivialZeros, δ ≤ |w.im - ρ.im|) →
      riemannZeta w ≠ 0 ∧ ‖negLogDerivZeta w‖ ≤ 2 * Ks * (1 + Cs) * L ^ 2 := by
    intro w hw1 hw2 hwim hws
    have hζ : riemannZeta w ≠ 0 := by
      by_cases h1 : 1 ≤ w.re
      · exact riemannZeta_ne_zero_of_one_le_re h1
      · intro hz
        have := hws w ⟨hz, by linarith, lt_of_not_ge h1⟩
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

end GoldbachBoundaries.Phi2Proof
