import Phi2NB.Phi2.Proof.M3Base
import Phi2NB.Phi2.Fill.CCommon
import Phi2NB.Phi2.Fill.norm_zeroSum_le

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The explicit-formula error after squaring is `O(t^(-9/10))`. -/
lemma C_sq_error_bound (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2‖ ≤ D * t ^ (-(9 / 10 : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := hL_explicit hRH hRvM hLD
  obtain ⟨S, hS, hSb⟩ := norm_zeroSum_le hRH hRvM
  let C : ℝ := |C₀|
  have hCnon : 0 ≤ C := abs_nonneg _
  have hC (t : ℝ) (ht : 0 < t) :
      ‖(hL t : ℂ) + zeroSum t‖ ≤ C * t ^ (-(2 / 5 : ℝ)) :=
    (hC₀ t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg ht.le _))
  refine ⟨C ^ 2 + 2 * S * C, by positivity, ?_⟩
  intro t ht
  have he : ((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2 =
      ((hL t : ℂ) + zeroSum t) ^ 2 - 2 * zeroSum t * ((hL t : ℂ) + zeroSum t) := by
    push_cast
    ring
  have hpow : (t ^ (-(2 / 5 : ℝ))) ^ 2 = t ^ (-(4 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast (t ^ (-(2 / 5 : ℝ))) 2, ← Real.rpow_mul ht.1.le]
    norm_num
  have hprod : t ^ (-(1 / 2 : ℝ)) * t ^ (-(2 / 5 : ℝ)) = t ^ (-(9 / 10 : ℝ)) := by
    rw [← Real.rpow_add ht.1]
    norm_num
  have hmono : t ^ (-(4 / 5 : ℝ)) ≤ t ^ (-(9 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by norm_num)
  calc
    ‖((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2‖ ≤
        ‖(hL t : ℂ) + zeroSum t‖ ^ 2 +
        2 * ‖zeroSum t‖ * ‖(hL t : ℂ) + zeroSum t‖ := by
      rw [he]
      have h := norm_sub_le (((hL t : ℂ) + zeroSum t) ^ 2)
        (2 * zeroSum t * ((hL t : ℂ) + zeroSum t))
      simpa only [norm_pow, norm_mul, norm_ofNat] using h
    _ ≤ (C * t ^ (-(2 / 5 : ℝ))) ^ 2 +
        2 * (S * t ^ (-(1 / 2 : ℝ))) * (C * t ^ (-(2 / 5 : ℝ))) := by
      gcongr
      · exact hC t ht.1
      · exact mul_nonneg (by norm_num) (mul_nonneg hS (Real.rpow_nonneg ht.1.le _))
      · exact (hSb t ht.1).2
      · exact hC t ht.1
    _ = C ^ 2 * t ^ (-(4 / 5 : ℝ)) + 2 * S * C * t ^ (-(9 / 10 : ℝ)) := by
      rw [mul_pow, hpow, ← hprod]
      ring
    _ ≤ (C ^ 2 + 2 * S * C) * t ^ (-(9 / 10 : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hmono (sq_nonneg C)]

/-- **`Kc` is bounded on `1 ≤ σ ≤ 2`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)): with `R = hL + Z`, `hL² - Z² = R² - 2ZR`, so the integrand is
`≤ (C² + 2SC) t^{-9/10}` on `(0, 1]` (`hL_explicit`, `norm_zeroSum_le`), and `∫_0^1 t^{-9/10} = 10`. -/
theorem norm_Kc_le (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) :
    ∃ B : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → ‖Kc s‖ ≤ B := by
  obtain ⟨D, hD, hb⟩ := C_sq_error_bound hRH hRvM hLD
  refine ⟨D * (∫ t in Ioc (0 : ℝ) 1, t ^ (-(9 / 10 : ℝ))), ?_⟩
  intro s hs hs2
  have hh : AEStronglyMeasurable (fun t : ℝ => ((hL t ^ 2 : ℝ) : ℂ))
      (volume.restrict (Ioc 0 1)) := by
    have hc := (norm_hL_le hRH (b := 3 / 4) (by norm_num) (by norm_num)).1
    exact (Complex.continuous_ofReal.comp_continuousOn
      ((hc.mono Ioc_subset_Ioi_self).pow 2)).aestronglyMeasurable measurableSet_Ioc
  have hg := (hh.sub (C_zeroSum_meas.pow 2)).mul (C_cpow_meas (s - 1))
  have hmajor : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2) * (t : ℂ) ^ (s - 1))‖ ≤
        D * t ^ (-(9 / 10 : ℝ)) := by
    intro t ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re]
    have hp : t ^ (s.re - 1) ≤ 1 := Real.rpow_le_one ht.1.le ht.2 (by linarith)
    calc
      _ ≤ ‖((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ _ := by simpa using hb t ht
  have hi := (C_integrableOn_rpow (r := -(9 / 10 : ℝ)) (by norm_num)).const_mul D
  calc
    ‖Kc s‖ ≤ ∫ t in Ioc (0 : ℝ) 1,
        ‖((((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2) * (t : ℂ) ^ (s - 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, D * t ^ (-(9 / 10 : ℝ)) := by
      exact integral_mono_ae (hi.mono' hg (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hmajor t ht)).norm hi
        (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hmajor t ht)
    _ = _ := integral_const_mul _ _

end GoldbachBoundaries.Phi2Proof
