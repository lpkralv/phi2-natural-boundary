import Phi2NB.Phi2.Fill.zetaMult_conj
import Phi2NB.Paper2.M5.Fill.QCommon
import Phi2NB.Paper2.M5.Fill.exists_sep_height
import Phi2NB.Paper2.M5.Fill.summable_zeros_inv_sq
import Phi2NB.Paper2.M5.Fill.rectangleIntegral'_eq_sum_of_simplePoles_rect
import Phi2NB.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.Paper2.M4b.Fill.isBigO_mul_sub_residue

/-!
# Helpers for the explicit formula (`Phi2/Proof/M2Explicit.lean`)

* `fillB_Z1`: (ZeroSymmetry) under RH, from `zetaMult_conj`; the same statement as `zeroSymmetry_of_RH`, which comes later in the
  import order.
* `fillB_zeta_ne_zero`: under RH, `ζ(z) ≠ 0` for `Re z > 0`, `Re z ≠ 1/2`.
* `fillB_norm_cpow_neg`: `‖t^{-w}‖ = t^{-Re w}`.
* `fillB_continuous_negLogDerivZeta_line`: `ψ` is continuous along a line `Re = σ < 1` that misses the zeros.
* `fillB_line_log_bound`: under RH, (RiemannVonMangoldt), (LogDerivZetaLocal), on a line `Re = σ ∈ (0, 1)`, `σ ≠ 1/2`:
  `ζ ≠ 0` and `‖ψ(σ + iy)‖ ≤ C log(|y| + 3)` (every zero is at distance `≥ |σ - 1/2|` from the line).
* `fillB_integrable_kernelL_line`: `kernelL t` is integrable on such a line.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- (ZeroSymmetry) under RH, through `zetaMult_conj` (the same statement as `zeroSymmetry_of_RH`). -/
theorem fillB_Z1 (hRH : RiemannHypothesis) : ZeroSymmetry := by
  intro ρ hρ
  have hc : conj ρ ∈ NontrivialZeros := conj_mem_nontrivialZeros hρ
  have hre : ρ.re = 1 / 2 := sigmaFinite_re_eq_half hRH hρ
  have h1 : 1 - conj ρ = ρ := by
    apply Complex.ext
    · simp [hre]; norm_num
    · simp
  refine ⟨⟨hc, zetaMult_conj hρ⟩, ?_, ?_⟩
  · rw [h1]; exact hρ
  · rw [h1]

/-- Under RH, `ζ(z) ≠ 0` for `Re z > 0`, `Re z ≠ 1/2`. -/
lemma fillB_zeta_ne_zero (hRH : RiemannHypothesis) {z : ℂ} (h0 : 0 < z.re) (hh : z.re ≠ 1 / 2) :
    riemannZeta z ≠ 0 := by
  intro hz
  by_cases h1 : 1 ≤ z.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hz
  · exact hh (sigmaFinite_re_eq_half hRH ⟨hz, h0, lt_of_not_ge h1⟩)

/-- `‖t^{-w}‖ = t^{-Re w}` for `t > 0`. -/
lemma fillB_norm_cpow_neg {t : ℝ} (ht : 0 < t) (w : ℂ) : ‖(t : ℂ) ^ (-w)‖ = t ^ (-w.re) := by
  rw [norm_cpow_eq_rpow_re_of_pos ht, neg_re]

/-- `ψ` is continuous along a line `Re = σ < 1` on which `ζ` does not vanish. -/
lemma fillB_continuous_negLogDerivZeta_line {σ : ℝ} (hσ : σ < 1)
    (hz : ∀ y : ℝ, riemannZeta ((σ : ℂ) + y * I) ≠ 0) :
    Continuous fun y : ℝ => negLogDerivZeta ((σ : ℂ) + y * I) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hne : (σ : ℂ) + y * I ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  exact (analyticAt_negLogDerivZeta hne (hz y)).continuousAt.comp
    (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)

/-- **`ψ` on a line `Re = σ ∈ (0, 1)`, `σ ≠ 1/2`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)): `ζ ≠ 0` there and
`‖ψ(σ + iy)‖ ≤ C log(|y| + 3)`. Every zero is at distance `≥ |σ - 1/2|` from the line (RH); `exists_sep_bound_nonneg`
for `|y| ≥ 2`, continuity on the compact segment for `|y| ≤ 2`. -/
lemma fillB_line_log_bound (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hσh : σ ≠ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, riemannZeta ((σ : ℂ) + y * I) ≠ 0 ∧
      ‖negLogDerivZeta ((σ : ℂ) + y * I)‖ ≤ C * Real.log (|y| + 3) := by
  have hZ1 := fillB_Z1 hRH
  obtain ⟨Ks, hKs0, hKs⟩ := M5.exists_sep_bound_nonneg hZ1 hRvM hLD
  have hre : ∀ y : ℝ, ((σ : ℂ) + y * I).re = σ := fun y => by simp
  have him : ∀ y : ℝ, ((σ : ℂ) + y * I).im = y := fun y => by simp
  have hnz : ∀ y : ℝ, riemannZeta ((σ : ℂ) + y * I) ≠ 0 := fun y =>
    fillB_zeta_ne_zero hRH (by rw [hre]; exact hσ0) (by rw [hre]; exact hσh)
  have hcont := fillB_continuous_negLogDerivZeta_line hσ1 hnz
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  set d : ℝ := min |σ - 1 / 2| 1 with hd
  have hd0 : 0 < d := lt_min (abs_pos.mpr (sub_ne_zero.mpr hσh)) one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdle : d ≤ |σ - 1 / 2| := min_le_left _ _
  refine ⟨Ks / d + |B0|, by positivity, fun y => ⟨hnz y, ?_⟩⟩
  have hlog1 : 1 ≤ Real.log (|y| + 3) := M5.one_le_log_add_three (abs_nonneg _)
  have hc1 : 0 ≤ Ks / d := by positivity
  by_cases hy : 2 ≤ |y|
  · have h := hKs _ (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hy) (hnz y) d hd0 hd1
      (fun ρ hρ _ => by
        have h1 := Complex.abs_re_le_norm ((σ : ℂ) + y * I - ρ)
        rw [Complex.sub_re, sigmaFinite_re_eq_half hRH hρ, hre] at h1
        linarith)
    rw [him] at h
    have hB := abs_nonneg B0
    nlinarith
  · push Not at hy
    have hb := hB0 y (abs_le.mp hy.le)
    have hB := abs_nonneg B0
    have : |B0| ≤ (Ks / d + |B0|) * Real.log (|y| + 3) := by nlinarith
    exact hb.trans ((le_abs_self B0).trans this)

/-- **`kernelL t` is integrable on a line `Re = σ ∈ (0, 1)`, `σ ≠ 1/2`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)). -/
lemma fillB_integrable_kernelL_line (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (hσh : σ ≠ 1 / 2) {t : ℝ} (ht : 0 < t) :
    Integrable fun y : ℝ => kernelL t ((σ : ℂ) + y * I) := by
  obtain ⟨C, hC0, hC⟩ := fillB_line_log_bound hRH hRvM hLD hσ0 hσ1 hσh
  have hcont := fillB_continuous_negLogDerivZeta_line hσ1 fun y => (hC y).1
  set q : ℝ → ℂ := fun y => (t : ℂ) ^ (-((σ : ℂ) + y * I)) * negLogDerivZeta ((σ : ℂ) + y * I) with hq
  have hqc : Continuous q := by
    refine Continuous.mul ?_ hcont
    rw [continuous_iff_continuousAt]
    intro y
    exact (TIdentity.differentiableAt_ofReal_cpow_neg ht _).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  have hqb : ∀ y : ℝ, ‖q y‖ ≤ (t ^ (-σ) * (2 * C)) * (1 + |y|) := by
    intro y
    rw [hq, norm_mul, fillB_norm_cpow_neg ht]
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    rw [hre]
    have hlog : Real.log (|y| + 3) ≤ 2 * (1 + |y|) := by
      have := Real.log_le_sub_one_of_pos (show 0 < |y| + 3 by positivity)
      linarith [abs_nonneg y]
    have h1 := (hC y).2
    have htp : 0 ≤ t ^ (-σ) := by positivity
    calc t ^ (-σ) * ‖negLogDerivZeta ((σ : ℂ) + y * I)‖ ≤ t ^ (-σ) * (C * (2 * (1 + |y|))) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hlog hC0)) htp
      _ = _ := by ring
  have hI := TIdentity.integrable_Gamma_mul_of_bound hσ0 hqc hqb
  refine hI.congr (Eventually.of_forall fun y => ?_)
  simp only [hq, kernelL]
  ring

end GoldbachBoundaries.Phi2Proof
