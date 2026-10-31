import Phi2NB.Phi2.Proof.M3Base
import Phi2NB.Phi2.Fill.CCommon
import Phi2NB.Phi2.Fill.norm_zeroSum_le

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The Mellin transform of `Z²` over `(0, 1]` is the Cauchy transform** (RH, (RiemannVonMangoldt)): for `Re s > 1`,
`∫_0^1 Z(t)² t^{s-1} dt = ∑_{(ρ,ρ')} a_ρ a_ρ' / (s - ρ - ρ')`, the integrand integrable. Expand `Z²` as the
Cauchy product over `NontrivialZeros × NontrivialZeros` (`tsum_mul_tsum_of_summable_norm`), exchange sum and
integral (dominated convergence, majorant `|a_ρ a_ρ'| t^{σ-2}`, integrable on `(0,1]` for `σ > 1`), and integrate
`t^{s-1-ρ-ρ'}` (`TIdentity.integral_Ioc_cpow_of_neg_one_lt`). Uses: `summable_norm_pair`, `norm_zeroSum_le`. -/
theorem integral_zeroSum_sq (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => zeroSum t ^ 2 * (t : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, zeroSum t ^ 2 * (t : ℂ) ^ (s - 1) = cauchyT s := by
  letI := C_countable_zeros
  let A (p : NontrivialZeros × NontrivialZeros) : ℂ := zeroCoef p.1 * zeroCoef p.2
  let r (p : NontrivialZeros × NontrivialZeros) : ℂ := s - 1 - p.1 - p.2
  let F (p : NontrivialZeros × NontrivialZeros) (t : ℝ) : ℂ := A p * (t : ℂ) ^ r p
  have hr (p : NontrivialZeros × NontrivialZeros) : (r p).re = s.re - 2 := by
    dsimp [r]
    rw [sigmaFinite_re_eq_half hRH p.1.2, sigmaFinite_re_eq_half hRH p.2.2]
    ring
  have hint (p : NontrivialZeros × NontrivialZeros) : IntegrableOn (F p) (Ioc 0 1) :=
    (TIdentity.integrableOn_Ioc_cpow_of_neg_one_lt (by rw [hr]; linarith)).const_mul (A p)
  have hn (p : NontrivialZeros × NontrivialZeros) (t : ℝ) (ht : 0 < t) :
      ‖F p t‖ = ‖A p‖ * t ^ (s.re - 2) := by
    change ‖A p * (t : ℂ) ^ r p‖ = _
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, hr]
  have hsum : Summable (fun p => ∫ t in Ioc (0 : ℝ) 1, ‖F p t‖) := by
    have ha : Summable (fun p => ‖A p‖) := summable_norm_pair hRH hRvM
    convert ha.mul_right (∫ t in Ioc (0 : ℝ) 1, t ^ (s.re - 2)) using 1
    funext p
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => hn p t ht.1)
  have hp (t : ℝ) (ht : 0 < t) : zeroSum t ^ 2 * (t : ℂ) ^ (s - 1) = ∑' p, F p t := by
    have ha : Summable (fun ρ : NontrivialZeros => ‖zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))‖) :=
      ((norm_zeroSum_le hRH hRvM).choose_spec.2 t ht).1.norm
    rw [pow_two, zeroSum, tsum_mul_tsum_of_summable_norm ha ha, ← tsum_mul_right]
    apply tsum_congr
    intro p
    have htne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    dsimp [F, A, r]
    rw [show s - 1 - (p.1 : ℂ) - p.2 = -(p.1 : ℂ) + -(p.2 : ℂ) + (s - 1) by ring,
      cpow_add _ _ htne, cpow_add _ _ htne]
    ring
  have hmain : IntegrableOn (fun t : ℝ => zeroSum t ^ 2 * (t : ℂ) ^ (s - 1)) (Ioc 0 1) := by
    obtain ⟨S, hS, hSb⟩ := norm_zeroSum_le hRH hRvM
    apply C_integrableOn_mellin (a := 1) (C := S ^ 2) (C_zeroSum_meas.pow 2) _ hs
    intro t ht
    change ‖zeroSum t ^ 2‖ ≤ _
    rw [norm_pow]
    calc ‖zeroSum t‖ ^ 2 ≤ (S * t ^ (-(1 / 2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hSb t ht.1).2 2
      _ = S ^ 2 * t ^ (-(1 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul ht.1.le]
        norm_num
  refine ⟨hmain, ?_⟩
  calc (∫ t in Ioc (0 : ℝ) 1, zeroSum t ^ 2 * (t : ℂ) ^ (s - 1)) =
        ∫ t in Ioc (0 : ℝ) 1, ∑' p, F p t :=
      setIntegral_congr_fun measurableSet_Ioc (fun t ht => hp t ht.1)
    _ = ∑' p, ∫ t in Ioc (0 : ℝ) 1, F p t :=
      (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = cauchyT s := by
      apply tsum_congr
      intro p
      change (∫ t in Ioc (0 : ℝ) 1, A p * (t : ℂ) ^ r p) = _
      rw [integral_const_mul, TIdentity.integral_Ioc_cpow_of_neg_one_lt (by rw [hr]; linarith)]
      change A p * (1 / (r p + 1)) = A p / (s - p.1 - p.2)
      rw [show r p + 1 = s - p.1 - p.2 by dsimp [r]; ring]
      ring

end GoldbachBoundaries.Phi2Proof
