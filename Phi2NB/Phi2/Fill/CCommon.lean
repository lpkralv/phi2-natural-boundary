import Phi2NB.Phi2.Proof.M3Base

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

lemma C_countable_zeros : Countable NontrivialZeros :=
  ((isClosed_riemannZetaZeros.isLindelof.countable_of_isDiscrete
    isDiscrete_riemannZetaZeros).mono (fun _ h => h.1)).to_subtype

lemma C_cpow_meas (r : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ r) (volume.restrict (Ioc 0 1)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
  intro t ht
  exact (continuousAt_ofReal_cpow_const t r (Or.inr ht.1.ne')).continuousWithinAt

lemma C_zeroSum_meas : AEStronglyMeasurable zeroSum (volume.restrict (Ioc 0 1)) := by
  letI := C_countable_zeros
  exact AEStronglyMeasurable.tsum (fun ρ : NontrivialZeros =>
    (C_cpow_meas (-(ρ : ℂ))).const_mul (zeroCoef ρ))

lemma C_integrableOn_rpow {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun t : ℝ => t ^ r) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

/-- An integrable majorant for a Mellin integral on `(0,1]`. -/
lemma C_integrableOn_mellin {g : ℝ → ℂ} {a C : ℝ} {s : ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc 0 1)))
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ (-a)) (hs : a < s.re) :
    IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ (s - 1)) (Ioc 0 1) := by
  refine ((C_integrableOn_rpow (r := -a + (s.re - 1)) (by linarith)).const_mul C).mono'
    (hg.mul (C_cpow_meas (s - 1))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re]
  calc ‖g t‖ * t ^ (s.re - 1) ≤ (C * t ^ (-a)) * t ^ (s.re - 1) :=
      mul_le_mul_of_nonneg_right (hb t ht) (Real.rpow_nonneg ht.1.le _)
    _ = C * t ^ (-a + (s.re - 1)) := by rw [mul_assoc, Real.rpow_add ht.1]

lemma C_hsq_integrable (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((hL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioc 0 1) := by
  let b : ℝ := min ((1 + s.re) / 4) (3 / 4)
  have hb : 1 / 2 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h2b : 2 * b < s.re := by
    have : b ≤ (1 + s.re) / 4 := min_le_left _ _
    linarith
  obtain ⟨hc, C, hC⟩ := norm_hL_le hRH hb hb1
  apply C_integrableOn_mellin (a := 2 * b) (C := C ^ 2) _ _ h2b
  · exact (Complex.continuous_ofReal.comp_continuousOn
      ((hc.mono Ioc_subset_Ioi_self).pow 2)).aestronglyMeasurable measurableSet_Ioc
  · intro t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := pow_le_pow_left₀ (abs_nonneg (hL t)) (hC t ht.1) 2
    rw [sq_abs] at h1
    calc hL t ^ 2 ≤ (C * t ^ (-b)) ^ 2 := h1
      _ = C ^ 2 * t ^ (-(2 * b)) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ (-b)) 2, ← Real.rpow_mul ht.1.le]
        ring_nf

end GoldbachBoundaries.Phi2Proof
