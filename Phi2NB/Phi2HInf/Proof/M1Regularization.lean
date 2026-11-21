import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.contour_regularization
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Fill.zero_mellin
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Proof.M1Regularization`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem norm_zeroSum_le_hinf (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖zeroSum x‖ ≤ (∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖) * x⁻¹ := by
  have ha := summable_norm_zeroCoef_hinf hZ1 hZ2 hStir
  have hbound (ρ : NontrivialZeros) :
      ‖zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖ ≤ ‖zeroCoef ρ‖ * x⁻¹ := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith [ρ.2.2.2])
  have hmajor := ha.mul_right x⁻¹
  have habs : Summable (fun ρ : NontrivialZeros =>
      ‖zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmajor
  calc ‖zeroSum x‖ ≤ ∑' ρ : NontrivialZeros,
        ‖zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖ * x⁻¹ := habs.tsum_le_tsum hbound hmajor
    _ = _ := tsum_mul_right

theorem norm_V_le (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → ‖V x‖ ≤ K * x ^ (1 / 2 : ℝ) := by
  let b : ℝ := -(1 / 2)
  let g : ℝ → ℂ := fun y => Gamma (b + y * I) * negLogDerivZeta (b + y * I)
  refine ⟨(1 / (2 * Real.pi)) * ∫ y, ‖g y‖, by positivity, ?_⟩
  intro x hx
  have hn (y : ℝ) : ‖kernelL x (b + y * I)‖ = x ^ (1 / 2 : ℝ) * ‖g y‖ := by
    simp only [kernelL, norm_mul, g]
    rw [norm_cpow_eq_rpow_re_of_pos hx]
    simp [b]
  have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  calc ‖V x‖
      = ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ *
          ‖∫ y : ℝ, kernelL x (b + y * I)‖ := by
        simp only [V, VerticalIntegral', VerticalIntegral, norm_smul, b]
        ring
    _ ≤ 1 / (2 * Real.pi) * ∫ y : ℝ, ‖kernelL x (b + y * I)‖ := by
        rw [hI]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by
        rw [integral_congr_ae (Eventually.of_forall hn), integral_const_mul]
        ring

theorem hL_explicit_hinf (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    {x : ℝ} (hx : 0 < x) : (hL x : ℂ) = -zeroSum x + c0 + V x := by
  have hFL := FillA.FL_eq_verticalIntegral'_aux (c := 2) (by norm_num) hx
  have hshift := verticalIntegral'_kernelL_regularized hZ1 hZ2 hZ3 hStir hx
  simp only [hL]
  push_cast
  rw [hFL, hshift]
  unfold V
  ring

lemma regularized_error_bound (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖(c0 + V x) ^ 2 - 2 * zeroSum x * V x‖ ≤ D * x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hb⟩ := norm_V_le hZ1 hZ2 hZ3 hStir
  let S := ∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨(‖c0‖ + K) ^ 2 + 2 * S * K, by positivity, ?_⟩
  intro x hx
  have hxhalf : x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx.1.le hx.2 (by norm_num)
  have hxinv : 1 ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 (by norm_num)
  have hv : ‖V x‖ ≤ K := (hb x hx.1).trans (by nlinarith)
  have hc : ‖c0 + V x‖ ≤ ‖c0‖ + K := (norm_add_le _ _).trans (by linarith)
  have hz : ‖zeroSum x‖ ≤ S * x ^ (-1 : ℝ) := by
    simpa only [Real.rpow_neg_one] using norm_zeroSum_le_hinf hZ1 hZ2 hStir hx
  have hprod : x ^ (-1 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hx.1]
    norm_num
  calc ‖(c0 + V x) ^ 2 - 2 * zeroSum x * V x‖
      ≤ ‖c0 + V x‖ ^ 2 + 2 * ‖zeroSum x‖ * ‖V x‖ := by
        have h := norm_sub_le ((c0 + V x) ^ (2 : ℕ)) (2 * zeroSum x * V x)
        rw [Complex.norm_pow, norm_mul, norm_mul, norm_ofNat] at h
        exact h
    _ ≤ (‖c0‖ + K) ^ 2 + 2 * (S * x ^ (-1 : ℝ)) * (K * x ^ (1 / 2 : ℝ)) := by
        gcongr
        · exact mul_nonneg (by norm_num) (mul_nonneg hS (Real.rpow_nonneg hx.1.le _))
        · exact hb x hx.1
    _ = (‖c0‖ + K) ^ 2 + 2 * S * K * x ^ (-(1 / 2 : ℝ)) := by
        rw [← hprod]
        ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hxinv (sq_nonneg (‖c0‖ + K))]

lemma V_aestronglyMeasurable (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) :
    AEStronglyMeasurable V (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hh : AEStronglyMeasurable (fun x => (hL x : ℂ)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (FillA.continuousOn_hL'.mono Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc
  apply ((hh.add C_zeroSum_meas).sub aestronglyMeasurable_const).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have h := hL_explicit_hinf hZ1 hZ2 hZ3 hStir hx.1
  dsimp
  linear_combination h

lemma regularized_error_meas (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) :
    AEStronglyMeasurable (fun x => (c0 + V x) ^ 2 - 2 * zeroSum x * V x)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hv := V_aestronglyMeasurable hZ1 hZ2 hZ3 hStir
  exact ((hv.const_add c0).pow 2).sub ((C_zeroSum_meas.const_mul 2).mul hv)

theorem differentiableOn_A (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) :
    DifferentiableOn ℂ A (halfPlane (1 / 2)) := by
  obtain ⟨D, -, hD⟩ := regularized_error_bound hZ1 hZ2 hZ3 hStir
  have hi := TIdentity.differentiableOn_integral_Ioc_cpow
    (regularized_error_meas hZ1 hZ2 hZ3 hStir) hD
  have ht : Differentiable ℂ (fun s : ℂ => E2L s - 2 * e1L (s - 1)) :=
    FillA.differentiable_E2L'.sub ((FillA.differentiable_e1L'.comp
      (differentiable_id.sub_const 1)).const_mul 2)
  exact ht.differentiableOn.add hi

theorem phi2_reg_identity (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip) :
    EqOn Phi2cHInf Phi2 (halfPlane 2) := by
  intro s hs
  have hs' : 2 < s.re := hs
  obtain ⟨hZ, hZI⟩ := integral_zeroSum_hinf hZ1 hZ2 hStir (s := s) (by linarith)
  obtain ⟨hZZ, hZZI⟩ := integral_zeroSum_sq_hinf hZ1 hZ2 hStir hs'
  obtain ⟨D, -, hD⟩ := regularized_error_bound hZ1 hZ2 hZ3 hStir
  have hE := C_integrableOn_mellin (regularized_error_meas hZ1 hZ2 hZ3 hStir)
    hD (s := s) (by linarith)
  have hR : RrL s = C s - 2 * c0 * L s +
      ∫ x in Ioc (0 : ℝ) 1, ((c0 + V x) ^ 2 - 2 * zeroSum x * V x) * (x : ℂ) ^ (s - 1) := by
    unfold RrL
    calc
      (∫ x in Ioc (0 : ℝ) 1, ((hL x ^ 2 : ℝ) : ℂ) * (x : ℂ) ^ (s - 1)) =
        ∫ x in Ioc (0 : ℝ) 1,
          (zeroSum x ^ 2 * (x : ℂ) ^ (s - 1) -
            (2 * c0) * (zeroSum x * (x : ℂ) ^ (s - 1))) +
          ((c0 + V x) ^ 2 - 2 * zeroSum x * V x) * (x : ℂ) ^ (s - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        push_cast
        rw [hL_explicit_hinf hZ1 hZ2 hZ3 hStir hx.1]
        ring
      _ = _ := by
        have hsub : IntegrableOn (fun x : ℝ => zeroSum x ^ 2 * (x : ℂ) ^ (s - 1) -
            (2 * c0) * (zeroSum x * (x : ℂ) ^ (s - 1))) (Ioc (0 : ℝ) 1) :=
          hZZ.sub (hZ.const_mul (2 * c0))
        rw [integral_add hsub hE,
          integral_sub hZZ (hZ.const_mul (2 * c0)), integral_const_mul, hZI, hZZI]
  rw [FillA.phi2_identity' hs']
  unfold Phi2cHInf M0 A Hphi2
  rw [hR]
  ring

end GoldbachBoundaries.Phi2HInf
