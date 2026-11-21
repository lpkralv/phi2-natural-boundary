import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.good_height
import Phi2NB.Phi2HInf.Fill.negative_line
import Phi2NB.Phi2HInf.Fill.rect_regularization
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.contour_regularization`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate
open scoped Interval
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

lemma regularized_rpow_neg_le {t x : ℝ} (ht : 0 < t) (hx1 : -(1 / 2) ≤ x) (hx2 : x ≤ 2) :
    t ^ (-x) ≤ t ^ (-(-(1 / 2) : ℝ)) + t ^ (-(2 : ℝ)) := by
  have h1 : 0 ≤ t ^ (-(-(1 / 2) : ℝ)) := by positivity
  have h2 : 0 ≤ t ^ (-(2 : ℝ)) := by positivity
  rcases le_or_gt 1 t with h | h
  · have : t ^ (-x) ≤ t ^ (-(-(1 / 2) : ℝ)) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith
  · have : t ^ (-x) ≤ t ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith)
    linarith

theorem verticalIntegral'_kernelL_regularized (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) {t : ℝ}
    (ht : 0 < t) :
    VerticalIntegral' (kernelL t) (2) = VerticalIntegral' (kernelL t) (-(1 / 2)) + c0 + 1 / (t : ℂ) - zeroSum t := by
  classical
  
  have hsum : Summable (fun ρ : NontrivialZeros => zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))) := by
    refine Summable.of_norm_bounded ((summable_norm_zeroCoef_hinf hZ1 hZ2 hStir).mul_right (1 + t⁻¹)) ?_
    intro ρ
    rw [norm_mul, fillB_norm_cpow_neg ht]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rcases le_or_gt 1 t with h | h
    · have he : t ^ (-(ρ : ℂ).re) ≤ 1 := by
        simpa using Real.rpow_le_rpow_of_exponent_le h (neg_nonpos.mpr ρ.2.2.1.le)
      linarith [inv_nonneg.mpr ht.le]
    · have he := Real.rpow_le_rpow_of_exponent_ge ht h.le
        (show (-1 : ℝ) ≤ -(ρ : ℂ).re by linarith [ρ.2.2.2])
      rw [Real.rpow_neg_one] at he
      linarith
  have hintA := FillA.integrable_kernelL ht
    (FillA.integrable_Gamma_mul_negLogDerivZeta_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hintB := integrable_kernelL_negative hZ1 hZ2 hZ3 ht
  have hA : Tendsto (fun Y : ℝ => ∫ y in -Y..Y, kernelL t (((2 : ℝ) : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, kernelL t (((2 : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hintA tendsto_neg_atTop_atBot tendsto_id
  have hB : Tendsto (fun Y : ℝ => ∫ y in -Y..Y, kernelL t (((-(1 / 2) : ℝ) : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, kernelL t (((-(1 / 2) : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hintB tendsto_neg_atTop_atBot tendsto_id
  
  obtain ⟨Cg, hCg⟩ := negative_strip_good_height hZ1 hZ2 hZ3
  obtain ⟨KΓ, hKΓ⟩ := norm_Gamma_negative_strip 4
  set T : ℝ := t ^ (-(-(1 / 2) : ℝ)) + t ^ (-(2 : ℝ)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hK0 : 0 ≤ max KΓ 0 := le_max_right _ _
  have hC0 : 0 ≤ max Cg 0 := le_max_right _ _
  set M : ℝ := T * max KΓ 0 * max Cg 0 with hM
  have hM0 : 0 ≤ M := by positivity
  have hhor : ∀ Y' : ℝ, 1 ≤ Y' → ∀ y : ℝ, |y| = Y' →
      (∀ x ∈ Icc (-(1 / 2) : ℝ) (2), ‖negLogDerivZeta (x + y * I)‖ ≤ max Cg 0 * (1 + Y') ^ 2) →
      ‖HIntegral (kernelL t) (-(1 / 2)) (2) y‖ ≤ 3 * M / (1 + Y') := by
    intro Y' hY' y hyY hψ
    have hY0 : 0 < 1 + Y' := by linarith
    have hpt : ∀ x ∈ Ι (-(1 / 2) : ℝ) (2), ‖kernelL t (x + y * I)‖ ≤ M / (1 + Y') := by
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hx1 : -(1 / 2) ≤ x := hx.1.le
      have hx2 : x ≤ 2 := hx.2
      have hzre : ((x : ℂ) + y * I).re = x := by simp
      have hzim : ((x : ℂ) + y * I).im = y := by simp
      have hg := hKΓ ((x : ℂ) + y * I) (by rw [hzre]; exact hx1) (by rw [hzre]; exact hx2) (by rw [hzim, hyY]; exact hY')
      rw [hzim, hyY] at hg
      have hg' : ‖Gamma ((x : ℂ) + y * I)‖ ≤ max KΓ 0 / (1 + Y') ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        exact hg.trans (le_max_left _ _)
      have htx : ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ ≤ T := by
        rw [fillB_norm_cpow_neg ht, hzre]
        exact regularized_rpow_neg_le ht hx1 hx2
      have hp := hψ x ⟨hx1, hx2⟩
      have hsq : (1 + Y') ≤ (1 + Y') ^ 2 := by nlinarith
      simp only [kernelL, norm_mul]
      calc ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ * (‖Gamma ((x : ℂ) + y * I)‖ *
            ‖negLogDerivZeta ((x : ℂ) + y * I)‖)
          ≤ T * (max KΓ 0 / (1 + Y') ^ 4 * (max Cg 0 * (1 + Y') ^ 2)) := by
            gcongr
        _ = M / (1 + Y') ^ 2 := by
            rw [hM]; field_simp
        _ ≤ M / (1 + Y') := div_le_div_of_nonneg_left hM0 hY0 hsq
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlen : |(2 : ℝ) - -(1 / 2)| ≤ 3 := by norm_num [abs_le]
    have hMY : 0 ≤ M / (1 + Y') := div_nonneg hM0 hY0.le
    calc ‖HIntegral (kernelL t) (-(1 / 2)) (2) y‖ ≤ M / (1 + Y') * |(2 : ℝ) - -(1 / 2)| := h
      _ ≤ M / (1 + Y') * 3 := mul_le_mul_of_nonneg_left hlen hMY
      _ = _ := by ring
  
  set D : ℂ := VerticalIntegral' (kernelL t) (2) - VerticalIntegral' (kernelL t) (-(1 / 2)) + zeroSum t - c0 - 1 / (t : ℂ)
    with hD
  suffices h : ∀ ε > 0, ‖D‖ < 3 * ε by
    have h0 : D = 0 := by
      by_contra hne
      have hpos := norm_pos_iff.mpr hne
      have := h (‖D‖ / 3) (by positivity)
      linarith
    rw [hD] at h0
    linear_combination h0
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hA (ε / 4) hε4
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hB (ε / 4) hε4
  obtain ⟨u₀, hu₀⟩ := (Metric.tendsto_atTop.mp hsum.hasSum) ε hε
  set Y₁ : ℝ := ∑ ρ ∈ u₀, |(ρ : ℂ).im| + 1 with hY₁
  set Y₃ : ℝ := 3 * M / (ε / 4) with hY₃
  set Y : ℝ := max (max 3 Y₁) (max (max N₁ N₂) Y₃) with hY
  have hY3 : 3 ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
  have hYY₁ : Y₁ ≤ Y := (le_max_right _ _).trans (le_max_left _ _)
  have hYN₁ : N₁ ≤ Y := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hYN₂ : N₂ ≤ Y := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hYY₃ : Y₃ ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨Y', hY'mem, hY'⟩ := hCg Y hY3
  have hY'Y : Y ≤ Y' := hY'mem.1
  have hY'pos : 0 < Y' := by linarith
  have hY'1 : 1 ≤ Y' := by linarith
  have hx13 : ∀ x ∈ Icc (-(1 / 2) : ℝ) (2), x ∈ Icc (-(1 / 2) : ℝ) 2 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hside : ∀ x ∈ Icc (-(1 / 2) : ℝ) (2),
      riemannZeta (x + Y' * I) ≠ 0 ∧ riemannZeta (x - Y' * I) ≠ 0 := fun x hx =>
    ⟨(hY' x (hx13 x hx)).1, (hY' x (hx13 x hx)).2.1⟩
  
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogY : Real.log Y ^ 2 ≤ (1 + Y') ^ 2 :=
    pow_le_pow_left₀ hlogY0 (by linarith [Real.log_le_self (show (0 : ℝ) ≤ Y by linarith)]) 2
  have hCl : Cg * Real.log Y ^ 2 ≤ max Cg 0 * (1 + Y') ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hlogY hC0)
  have hbot := hhor Y' hY'1 (-Y') (by rw [abs_neg]; exact abs_of_nonneg hY'pos.le) (fun x hx => by
    have h := (hY' x (hx13 x hx)).2.2.2
    have he : ((x : ℂ) + ((-Y' : ℝ) : ℂ) * I) = (x : ℂ) - Y' * I := by push_cast; ring
    rw [he]
    exact h.trans hCl)
  have htop := hhor Y' hY'1 Y' (abs_of_nonneg hY'pos.le) (fun x hx => (hY' x (hx13 x hx)).2.2.1.trans hCl)
  have hMlt : 3 * M / (1 + Y') < ε / 4 := by
    rw [div_lt_iff₀ (by linarith)]
    have h1 : 3 * M / (ε / 4) ≤ Y' := hYY₃.trans hY'Y
    rw [div_le_iff₀ hε4] at h1
    nlinarith
  have ha := hN₁ Y' (hYN₁.trans hY'Y)
  have hb := hN₂ Y' (hYN₂.trans hY'Y)
  rw [dist_eq_norm] at ha hb
  
  obtain ⟨hfin, hrect⟩ := rect_kernelL_regularized ht hY'pos hside
  set v : Finset NontrivialZeros := hfin.toFinset.subtype (· ∈ NontrivialZeros) with hv
  have hvsum : ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'}, -(zeroCoef ρ * (t : ℂ) ^ (-ρ)) =
      -∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_neg_distrib, hv,
      Finset.sum_subtype_of_mem (fun ρ => zeroCoef ρ * (t : ℂ) ^ (-ρ)) (p := (· ∈ NontrivialZeros))]
    intro x hx
    exact ((hfin.mem_toFinset).mp hx).1
  have hu₀v : u₀ ≤ v := by
    intro ρ hρ
    rw [hv, Finset.mem_subtype, hfin.mem_toFinset]
    refine ⟨ρ.2, ?_⟩
    have h1 : |(ρ : ℂ).im| ≤ ∑ ρ ∈ u₀, |(ρ : ℂ).im| :=
      Finset.single_le_sum (f := fun ρ : NontrivialZeros => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
    linarith
  have hvT : dist (∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ))) (zeroSum t) < ε := hu₀ v hu₀v
  rw [dist_eq_norm] at hvT
  rw [hvsum] at hrect
  
  set Hb := HIntegral (kernelL t) (-(1 / 2)) (2) (-Y') with hHb
  set Ht := HIntegral (kernelL t) (-(1 / 2)) (2) Y' with hHt
  set A1 := ∫ y in -Y'..Y', kernelL t (((2 : ℝ) : ℂ) + y * I) with hA1
  set L1 := ∫ y : ℝ, kernelL t (((2 : ℝ) : ℂ) + y * I) with hL1
  set A2 := ∫ y in -Y'..Y', kernelL t (((-(1 / 2) : ℝ) : ℂ) + y * I) with hA2
  set L2 := ∫ y : ℝ, kernelL t (((-(1 / 2) : ℝ) : ℂ) + y * I) with hL2
  have hid : RectangleIntegral' (kernelL t) (((-(1 / 2) : ℝ) : ℂ) - I * Y') (((2 : ℝ) : ℂ) + I * Y') -
      (VerticalIntegral' (kernelL t) (2) - VerticalIntegral' (kernelL t) (-(1 / 2))) =
      (1 / (2 * Real.pi * I)) * (Hb - Ht + I * (A1 - L1) - I * (A2 - L2)) := by
    have hzre : (((-(1 / 2) : ℝ) : ℂ) - I * Y').re = -(1 / 2) := by simp
    have hzim : (((-(1 / 2) : ℝ) : ℂ) - I * Y').im = -Y' := by simp
    have hwre : (((2 : ℝ) : ℂ) + I * Y').re = 2 := by simp
    have hwim : (((2 : ℝ) : ℂ) + I * Y').im = Y' := by simp
    rw [RectangleIntegral', RectangleIntegral, hzre, hzim, hwre, hwim, VerticalIntegral',
      VerticalIntegral', VerticalIntegral, VerticalIntegral, VIntegral, VIntegral]
    simp only [smul_eq_mul]
    rw [hHb, hHt, hA1, hL1, hA2, hL2]
    ring
  have hc : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, mul_one, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hX : ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖ < ε := by
    have hbot' : ‖Hb‖ < ε / 4 := lt_of_le_of_lt hbot hMlt
    have htop' : ‖Ht‖ < ε / 4 := lt_of_le_of_lt htop hMlt
    calc ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖
        ≤ ‖Hb‖ + ‖Ht‖ + ‖A1 - L1‖ + ‖A2 - L2‖ := by
          have h1 := norm_sub_le (Hb - Ht + I * (A1 - L1)) (I * (A2 - L2))
          have h2 := norm_add_le (Hb - Ht) (I * (A1 - L1))
          have h3 := norm_sub_le Hb Ht
          rw [norm_mul, norm_I, one_mul] at h1 h2
          linarith
      _ < ε / 4 + ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ = ε := by ring
  have hXn : ‖RectangleIntegral' (kernelL t) (((-(1 / 2) : ℝ) : ℂ) - I * Y') (((2 : ℝ) : ℂ) + I * Y') -
      (VerticalIntegral' (kernelL t) (2) - VerticalIntegral' (kernelL t) (-(1 / 2)))‖ < ε := by
    rw [hid, norm_mul]
    calc ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖
        ≤ 1 * ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < ε := by rw [one_mul]; exact hX
  rw [hrect] at hXn
  simp only [← sub_eq_add_neg] at hXn
  calc ‖D‖ = ‖-(c0 + 1 / (t : ℂ) - ∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) -
          (VerticalIntegral' (kernelL t) (2) - VerticalIntegral' (kernelL t) (-(1 / 2)))) -
          (∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) - zeroSum t)‖ := by
        rw [hD]; congr 1; ring
    _ ≤ ‖c0 + 1 / (t : ℂ) - ∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) -
          (VerticalIntegral' (kernelL t) (2) - VerticalIntegral' (kernelL t) (-(1 / 2)))‖ +
          ‖∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) - zeroSum t‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ < ε + ε := add_lt_add hXn hvT
    _ < 3 * ε := by linarith

end GoldbachBoundaries.Phi2HInf
