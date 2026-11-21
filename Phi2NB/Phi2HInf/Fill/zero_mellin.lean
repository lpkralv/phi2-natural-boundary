import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.zero_mellin`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

lemma summable_norm_cpow_family {ι : Type*} (a p : ι → ℂ) {r : ℝ}
    (ha : Summable (fun i => ‖a i‖)) (hp : ∀ i, (p i).re ≤ r)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    Summable (fun i => ‖a i * (x : ℂ) ^ (-p i)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (ha.mul_right (x ^ (-r)))
  intro i
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (neg_le_neg (hp i))) (norm_nonneg _)

lemma integral_cpow_family {ι : Type*} [Countable ι] (a p : ι → ℂ) {r : ℝ}
    (ha : Summable (fun i => ‖a i‖)) (hp : ∀ i, (p i).re ≤ r)
    {s : ℂ} (hs : r < s.re) :
    IntegrableOn (fun x : ℝ => (∑' i, a i * (x : ℂ) ^ (-p i)) * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, (∑' i, a i * (x : ℂ) ^ (-p i)) * (x : ℂ) ^ (s - 1)) =
        ∑' i, a i / (s - p i) := by
  let f (i : ι) (x : ℝ) := a i * (x : ℂ) ^ (s - 1 - p i)
  have hexp (i : ι) : -1 < (s - 1 - p i).re := by
    simp only [sub_re, one_re]
    linarith [hp i]
  have hint (i : ι) : IntegrableOn (f i) (Ioc 0 1) :=
    (TIdentity.integrableOn_Ioc_cpow_of_neg_one_lt (hexp i)).const_mul (a i)
  have hbound (i : ι) (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      ‖f i x‖ ≤ ‖a i‖ * x ^ (s.re - 1 - r) := by
    dsimp [f]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, sub_re, sub_re, one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
      (by linarith [hp i])) (norm_nonneg _)
  have hi := C_integrableOn_rpow (r := s.re - 1 - r) (by linarith)
  have hsum : Summable (fun i => ∫ x in Ioc (0 : ℝ) 1, ‖f i x‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
      (ha.mul_right (∫ x in Ioc (0 : ℝ) 1, x ^ (s.re - 1 - r)))
    intro i
    rw [← integral_const_mul]
    exact integral_mono_ae (hint i).norm (hi.const_mul _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hbound i x hx)
  have hmain : IntegrableOn
      (fun x : ℝ => (∑' i, a i * (x : ℂ) ^ (-p i)) * (x : ℂ) ^ (s - 1)) (Ioc 0 1) := by
    apply C_integrableOn_mellin (a := r) (C := ∑' i, ‖a i‖)
      (AEStronglyMeasurable.tsum (fun i => (C_cpow_meas (-p i)).const_mul (a i))) _ hs
    intro x hx
    have hb (i : ι) : ‖a i * (x : ℂ) ^ (-p i)‖ ≤ ‖a i‖ * x ^ (-r) := by
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (neg_le_neg (hp i))) (norm_nonneg _)
    calc ‖∑' i, a i * (x : ℂ) ^ (-p i)‖ ≤ ∑' i, ‖a i * (x : ℂ) ^ (-p i)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_cpow_family a p ha hp hx)
      _ ≤ ∑' i, ‖a i‖ * x ^ (-r) :=
        (summable_norm_cpow_family a p ha hp hx).tsum_le_tsum hb (ha.mul_right _)
      _ = _ := tsum_mul_right
  refine ⟨hmain, ?_⟩
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      (∑' i, a i * (x : ℂ) ^ (-p i)) * (x : ℂ) ^ (s - 1) = ∑' i, f i x := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro i
    dsimp [f]
    rw [show s - 1 - p i = -p i + (s - 1) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc heq,
    ← integral_tsum_of_summable_integral_norm hint hsum]
  apply tsum_congr
  intro i
  dsimp [f]
  rw [integral_const_mul, TIdentity.integral_Ioc_cpow_of_neg_one_lt (hexp i)]
  congr 1
  simp only [show s - 1 - p i + 1 = s - p i by ring, div_eq_mul_inv, one_mul]

lemma integral_zeroSum_hinf (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => zeroSum x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, zeroSum x * (x : ℂ) ^ (s - 1)) = L s := by
  letI := C_countable_zeros
  exact integral_cpow_family (fun ρ : NontrivialZeros => zeroCoef ρ) (fun ρ => ρ)
    (summable_norm_zeroCoef_hinf hZ1 hZ2 hStir) (fun ρ => ρ.2.2.2.le) hs

lemma integral_zeroSum_sq_hinf (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ => zeroSum x ^ 2 * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, zeroSum x ^ 2 * (x : ℂ) ^ (s - 1)) = C s := by
  letI := C_countable_zeros
  have ha := summable_norm_zeroCoef_hinf hZ1 hZ2 hStir
  let a (p : NontrivialZeros × NontrivialZeros) := zeroCoef p.1 * zeroCoef p.2
  let p (q : NontrivialZeros × NontrivialZeros) : ℂ := q.1 + q.2
  have hp (q : NontrivialZeros × NontrivialZeros) : (p q).re ≤ 2 := by
    dsimp [p]
    linarith [q.1.2.2.2, q.2.2.2.2]
  have h := integral_cpow_family a p
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ) (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hp hs
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : zeroSum x ^ 2 = ∑' q, a q * (x : ℂ) ^ (-p q) := by
    have hz := summable_norm_cpow_family (fun ρ : NontrivialZeros => zeroCoef ρ) (fun ρ => (ρ : ℂ))
      ha (fun ρ => ρ.2.2.2.le) hx
    rw [pow_two, zeroSum, tsum_mul_tsum_of_summable_norm hz hz]
    apply tsum_congr
    intro q
    dsimp [a, p]
    rw [neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    ring
  refine ⟨h.1.congr_fun (fun x hx => by rw [heq x hx]) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [heq x hx]), h.2]
  apply tsum_congr
  intro q
  simp only [a, p, sub_add_eq_sub_sub]

end GoldbachBoundaries.Phi2HInf
