import Phi2NB.Phi2.Fill.summable_norm_zeroCoef
import Phi2NB.Phi2.Fill.negLogDerivZeta_good_height
import Phi2NB.Phi2.Fill.rect_kernelL

/-!
# The shift across the zeros: `verticalIntegral'_kernelL_zero_shift`

Fix `ε > 0`.

* Both lines are integrable (`fillB_integrable_kernelL_line`), so the truncated line integrals over `[-Y, Y]` are
  `ε/4`-close to the full ones for `Y` large.
* `∑_ρ a_ρ t^{-ρ}` converges absolutely (`summable_norm_zeroCoef`, `|t^{-ρ}| = t^{-1/2}` under RH); a finite set
  `u₀` of zeros makes every larger partial sum `ε`-close to `zeroSum t`.
* At a good height `Y' ≥ Y` (`negLogDerivZeta_good_height`), `|ψ| ≤ C log² Y ≤ C(1 + Y')²` on the horizontal
  sides, `|Γ| ≤ K(1 + Y')^{-4}` (`TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le`) and `|t^{-w}| ≤ t^{-2/5} + t^{-3/4}`,
  so each horizontal integral is `≤ M/(1 + Y') < ε/4`.
* `rect_kernelL` writes the rectangle as `-∑_{|γ| < Y'} a_ρ t^{-ρ}`, and `{|γ| < Y'} ⊇ u₀`.

So `‖(2πi)⁻¹∫_{(3/4)} - (2πi)⁻¹∫_{(2/5)} + zeroSum t‖ < 2ε` for every `ε`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate
open scoped Interval

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `t^{-x} ≤ t^{-2/5} + t^{-3/4}` for `x ∈ [2/5, 3/4]`, `t > 0`. -/
lemma fillB_rpow_neg_le {t x : ℝ} (ht : 0 < t) (hx1 : 2 / 5 ≤ x) (hx2 : x ≤ 3 / 4) :
    t ^ (-x) ≤ t ^ (-(2 / 5 : ℝ)) + t ^ (-(3 / 4 : ℝ)) := by
  have h1 : 0 ≤ t ^ (-(2 / 5 : ℝ)) := by positivity
  have h2 : 0 ≤ t ^ (-(3 / 4 : ℝ)) := by positivity
  rcases le_or_gt 1 t with h | h
  · have : t ^ (-x) ≤ t ^ (-(2 / 5 : ℝ)) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    linarith
  · have : t ^ (-x) ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith)
    linarith

/-- **The shift to `Re w = 2/5`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)): for `t > 0`,
`(2πi)⁻¹ ∫_{(3/4)} kernelL t = (2πi)⁻¹ ∫_{(2/5)} kernelL t - ∑_ρ a_ρ t^{-ρ}`. Both lines are integrable
(`fillB_integrable_kernelL_line`). Take rectangles at the good heights `Y' → ∞` (`negLogDerivZeta_good_height`); the
horizontal integrals tend to `0`; the residue sums converge to `-zeroSum t` by `summable_norm_zeroCoef` and
`|t^{-ρ}| = t^{-1/2}`. Uses `rect_kernelL`. -/
theorem verticalIntegral'_kernelL_zero_shift (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {t : ℝ}
    (ht : 0 < t) :
    VerticalIntegral' (kernelL t) (3 / 4) = VerticalIntegral' (kernelL t) (2 / 5) - zeroSum t := by
  classical
  -- the zero side
  have hsum : Summable (fun ρ : NontrivialZeros => zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))) := by
    refine Summable.of_norm_bounded ((summable_norm_zeroCoef hRH hRvM).mul_right (t ^ (-(1 / 2 : ℝ))))
      (fun ρ => ?_)
    rw [norm_mul, fillB_norm_cpow_neg ht, sigmaFinite_re_eq_half hRH ρ.2]
  -- the two lines
  have hintA := fillB_integrable_kernelL_line hRH hRvM hLD (σ := 3 / 4) (by norm_num) (by norm_num)
    (by norm_num) ht
  have hintB := fillB_integrable_kernelL_line hRH hRvM hLD (σ := 2 / 5) (by norm_num) (by norm_num)
    (by norm_num) ht
  have hA : Tendsto (fun Y : ℝ => ∫ y in -Y..Y, kernelL t (((3 / 4 : ℝ) : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, kernelL t (((3 / 4 : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hintA tendsto_neg_atTop_atBot tendsto_id
  have hB : Tendsto (fun Y : ℝ => ∫ y in -Y..Y, kernelL t (((2 / 5 : ℝ) : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, kernelL t (((2 / 5 : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hintB tendsto_neg_atTop_atBot tendsto_id
  -- the horizontal sides
  obtain ⟨Cg, hCg⟩ := negLogDerivZeta_good_height hRH hRvM hLD
  obtain ⟨KΓ, hKΓ⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := 2 / 5) (a' := 3 / 4)
    (by norm_num) 4
  set T : ℝ := t ^ (-(2 / 5 : ℝ)) + t ^ (-(3 / 4 : ℝ)) with hT
  have hT0 : 0 ≤ T := by positivity
  have hK0 : 0 ≤ max KΓ 0 := le_max_right _ _
  have hC0 : 0 ≤ max Cg 0 := le_max_right _ _
  set M : ℝ := T * max KΓ 0 * max Cg 0 with hM
  have hM0 : 0 ≤ M := by positivity
  have hhor : ∀ Y' : ℝ, 1 ≤ Y' → ∀ y : ℝ, |y| = Y' →
      (∀ x ∈ Icc (2 / 5 : ℝ) (3 / 4), ‖negLogDerivZeta (x + y * I)‖ ≤ max Cg 0 * (1 + Y') ^ 2) →
      ‖HIntegral (kernelL t) (2 / 5) (3 / 4) y‖ ≤ M / (1 + Y') := by
    intro Y' hY' y hyY hψ
    have hY0 : 0 < 1 + Y' := by linarith
    have hpt : ∀ x ∈ Ι (2 / 5 : ℝ) (3 / 4), ‖kernelL t (x + y * I)‖ ≤ M / (1 + Y') := by
      intro x hx
      rw [uIoc_of_le (by norm_num)] at hx
      have hx1 : 2 / 5 ≤ x := hx.1.le
      have hx2 : x ≤ 3 / 4 := hx.2
      have hzre : ((x : ℂ) + y * I).re = x := by simp
      have hzim : ((x : ℂ) + y * I).im = y := by simp
      have hg := hKΓ ((x : ℂ) + y * I) (by rw [hzre]; exact hx1) (by rw [hzre]; exact hx2)
      rw [hzim, hyY] at hg
      have hg' : ‖Gamma ((x : ℂ) + y * I)‖ ≤ max KΓ 0 / (1 + Y') ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        exact hg.trans (le_max_left _ _)
      have htx : ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ ≤ T := by
        rw [fillB_norm_cpow_neg ht, hzre]
        exact fillB_rpow_neg_le ht hx1 hx2
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
    have hlen : |(3 / 4 : ℝ) - 2 / 5| ≤ 1 := by norm_num [abs_le]
    have hMY : 0 ≤ M / (1 + Y') := div_nonneg hM0 hY0.le
    calc ‖HIntegral (kernelL t) (2 / 5) (3 / 4) y‖ ≤ M / (1 + Y') * |(3 / 4 : ℝ) - 2 / 5| := h
      _ ≤ M / (1 + Y') * 1 := mul_le_mul_of_nonneg_left hlen hMY
      _ = _ := mul_one _
  -- the `ε` argument
  set D : ℂ := VerticalIntegral' (kernelL t) (3 / 4) - VerticalIntegral' (kernelL t) (2 / 5) + zeroSum t
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
  set Y₃ : ℝ := M / (ε / 4) with hY₃
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
  have hx13 : ∀ x ∈ Icc (2 / 5 : ℝ) (3 / 4), x ∈ Icc (1 / 3 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hside : ∀ x ∈ Icc (2 / 5 : ℝ) (3 / 4),
      riemannZeta (x + Y' * I) ≠ 0 ∧ riemannZeta (x - Y' * I) ≠ 0 := fun x hx =>
    ⟨(hY' x (hx13 x hx)).1, (hY' x (hx13 x hx)).2.1⟩
  -- `C log² Y ≤ max C 0 (1 + Y')²`
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
  have hMlt : M / (1 + Y') < ε / 4 := by
    rw [div_lt_iff₀ (by linarith)]
    have h1 : M / (ε / 4) ≤ Y' := hYY₃.trans hY'Y
    rw [div_le_iff₀ hε4] at h1
    nlinarith
  have ha := hN₁ Y' (hYN₁.trans hY'Y)
  have hb := hN₂ Y' (hYN₂.trans hY'Y)
  rw [dist_eq_norm] at ha hb
  -- the rectangle
  obtain ⟨hfin, hrect⟩ := rect_kernelL hRH ht hY'pos hside
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
  -- the identity for the rectangle minus the two lines
  set Hb := HIntegral (kernelL t) (2 / 5) (3 / 4) (-Y') with hHb
  set Ht := HIntegral (kernelL t) (2 / 5) (3 / 4) Y' with hHt
  set A1 := ∫ y in -Y'..Y', kernelL t (((3 / 4 : ℝ) : ℂ) + y * I) with hA1
  set L1 := ∫ y : ℝ, kernelL t (((3 / 4 : ℝ) : ℂ) + y * I) with hL1
  set A2 := ∫ y in -Y'..Y', kernelL t (((2 / 5 : ℝ) : ℂ) + y * I) with hA2
  set L2 := ∫ y : ℝ, kernelL t (((2 / 5 : ℝ) : ℂ) + y * I) with hL2
  have hid : RectangleIntegral' (kernelL t) (((2 / 5 : ℝ) : ℂ) - I * Y') (((3 / 4 : ℝ) : ℂ) + I * Y') -
      (VerticalIntegral' (kernelL t) (3 / 4) - VerticalIntegral' (kernelL t) (2 / 5)) =
      (1 / (2 * Real.pi * I)) * (Hb - Ht + I * (A1 - L1) - I * (A2 - L2)) := by
    have hzre : (((2 / 5 : ℝ) : ℂ) - I * Y').re = 2 / 5 := by simp
    have hzim : (((2 / 5 : ℝ) : ℂ) - I * Y').im = -Y' := by simp
    have hwre : (((3 / 4 : ℝ) : ℂ) + I * Y').re = 3 / 4 := by simp
    have hwim : (((3 / 4 : ℝ) : ℂ) + I * Y').im = Y' := by simp
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
  have hXn : ‖RectangleIntegral' (kernelL t) (((2 / 5 : ℝ) : ℂ) - I * Y') (((3 / 4 : ℝ) : ℂ) + I * Y') -
      (VerticalIntegral' (kernelL t) (3 / 4) - VerticalIntegral' (kernelL t) (2 / 5))‖ < ε := by
    rw [hid, norm_mul]
    calc ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖
        ≤ 1 * ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < ε := by rw [one_mul]; exact hX
  rw [hrect] at hXn
  calc ‖D‖ = ‖-(-∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) -
          (VerticalIntegral' (kernelL t) (3 / 4) - VerticalIntegral' (kernelL t) (2 / 5))) -
          (∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) - zeroSum t)‖ := by
        rw [hD]; congr 1; ring
    _ ≤ ‖-∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) -
          (VerticalIntegral' (kernelL t) (3 / 4) - VerticalIntegral' (kernelL t) (2 / 5))‖ +
          ‖∑ ρ ∈ v, zeroCoef (ρ : ℂ) * (t : ℂ) ^ (-(ρ : ℂ)) - zeroSum t‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ < ε + ε := add_lt_add hXn hvT
    _ < 3 * ε := by linarith

end GoldbachBoundaries.Phi2Proof
