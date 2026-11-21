import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.Bsup_facts
import Phi2NB.HInfSupport.Paper2.M1.Fill.Bsup_lt_one_of_Hinf
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.r_cutoff
import Phi2NB.Phi2HInf.Proof.RDefs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.r_remainder`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof PhiRProof

theorem QR_eq_Pr_add_Rr (E : Finset NontrivialZeros) {r : ℕ} (hr : 2 ≤ r)
    {x : ℝ} (hx : 0 < x) : (QR r x : ℂ) = PrFun E r x + RrFun E r x := by
  have hbin (k : ℕ) (hk : k ∈ Finset.Ico 3 (r + 1)) :
      (hL x : ℂ) ^ k = exceptionalE E x ^ k + (k : ℂ) * exceptionalE E x ^ (k - 1) * residualG E x +
        ∑ j ∈ Finset.Ico 2 (k + 1), (k.choose j : ℂ) * exceptionalE E x ^ (k - j) * residualG E x ^ j := by
    have hk2 : 2 ≤ k + 1 := by have := (Finset.mem_Ico.mp hk).1; omega
    have hh := add_pow (residualG E x) (exceptionalE E x) k
    rw [← Finset.sum_range_add_sum_Ico _ hk2] at hh
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, one_mul,
      mul_one, Nat.sub_zero, pow_one] at hh
    have he : residualG E x + exceptionalE E x = (hL x : ℂ) := by dsimp [residualG]; ring
    rw [he] at hh
    rw [hh]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j hj
      ring
  rw [QR_eq_sum hr hx]
  push_cast
  unfold PrFun RrFun
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hbin k hk]
  ring

lemma r_remainder_exponent (hH : Hinf) (hZ1 : Z1) {p j : ℕ}
    (hj : 2 ≤ j) (hpj : 3 ≤ p + j) :
    1 + rMargin ≤ (p : ℝ) * (1 - Bsup) + (j : ℝ) * (1 - rCutoff) := by
  have hB := M1.Bsup_facts hZ1
  have hB1 := M1.Bsup_lt_one_of_Hinf hH
  have hb1 := (rCutoff_bounds hH hZ1).2.1
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  by_cases hp : p = 0
  · subst p
    have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
    have ht := mul_nonneg (sub_nonneg.mpr hj3) (sub_nonneg.mpr hb1.le)
    dsimp [rCutoff, rMargin] at *
    push_cast
    nlinarith [hB.2.1]
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
    have ht := mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hB1.le)
    have ht' := mul_nonneg (sub_nonneg.mpr hj') (sub_nonneg.mpr hb1.le)
    dsimp [rCutoff, rMargin] at *
    nlinarith

lemma RrFun_meas (E : Finset NontrivialZeros) (r : ℕ) :
    AEStronglyMeasurable (RrFun E r) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have he : AEStronglyMeasurable (exceptionalE E) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    E.aestronglyMeasurable_fun_sum (fun ρ _ => (C_cpow_meas (-(ρ : ℂ))).const_mul _)
  have hh : AEStronglyMeasurable (fun x => (hL x : ℂ)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      (Phi2Proof.FillA.continuousOn_hL'.mono Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc
  have hg : AEStronglyMeasurable (residualG E) (volume.restrict (Ioc (0 : ℝ) 1)) := hh.sub he
  apply Finset.aestronglyMeasurable_fun_sum
  intro k hk
  have hx : AEStronglyMeasurable (fun x : ℝ => (1 / (x : ℂ)) ^ (r - k))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    simpa only [one_div, Pi.inv_apply] using
      (Complex.continuous_ofReal.measurable.inv.pow_const (r - k)).aestronglyMeasurable
  exact (hx.const_mul _).mul ((Finset.Ico 2 (k + 1)).aestronglyMeasurable_fun_sum
    (fun j _ => ((he.pow (k - j)).const_mul _).mul (hg.pow j)))

theorem norm_Rr_le (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    {E : Finset NontrivialZeros} (hE : ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re)
    {r : ℕ} (hr : 2 ≤ r) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖RrFun E r x‖ ≤ U * x ^ (-rAbscissa r) := by
  obtain ⟨L, hL, hEL⟩ := norm_E_le hZ1 E
  obtain ⟨K, hK, hgK⟩ := norm_g_le hH hZ1 hZ2 hZ3 hStir hE
  let u (k j : ℕ) : ℝ := (r.choose k : ℝ) * (k.choose j : ℝ) * L ^ (k - j) * K ^ j
  refine ⟨∑ k ∈ Finset.Ico 3 (r + 1), ∑ j ∈ Finset.Ico 2 (k + 1), u k j,
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => by dsimp [u]; positivity)), ?_⟩
  intro x hx
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico 3 (r + 1)) (j : ℕ) (hj : j ∈ Finset.Ico 2 (k + 1)) :
      ‖(r.choose k : ℂ) * (1 / (x : ℂ)) ^ (r - k) *
        ((k.choose j : ℂ) * exceptionalE E x ^ (k - j) * residualG E x ^ j)‖ ≤
          u k j * x ^ (-rAbscissa r) := by
    have hjk : j ≤ k := by have := (Finset.mem_Ico.mp hj).2; omega
    have hkr : k ≤ r := by have := (Finset.mem_Ico.mp hk).2; omega
    have hexp := r_remainder_exponent hH hZ1 (p := k - j)
      (Finset.mem_Ico.mp hj).1 (by have := (Finset.mem_Ico.mp hk).1; omega)
    rw [Nat.cast_sub hjk] at hexp
    have hpow : (1 / x) ^ (r - k) * (x ^ (-Bsup)) ^ (k - j) * (x ^ (-rCutoff)) ^ j =
        x ^ (-((r : ℝ) - k) - Bsup * (k - j) - rCutoff * j) := by
      rw [one_div, inv_pow, ← Real.rpow_natCast x (r - k), ← Real.rpow_neg hx.1.le,
        ← Real.rpow_natCast (x ^ (-Bsup)) (k - j), ← Real.rpow_mul hx.1.le,
        ← Real.rpow_natCast (x ^ (-rCutoff)) j, ← Real.rpow_mul hx.1.le,
        ← Real.rpow_add hx.1, ← Real.rpow_add hx.1, Nat.cast_sub hkr, Nat.cast_sub hjk]
      congr 1
      ring
    have hxpow : x ^ (-((r : ℝ) - k) - Bsup * (k - j) - rCutoff * j) ≤ x ^ (-rAbscissa r) := by
      apply Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
      dsimp [rAbscissa]
      nlinarith
    simp only [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
    calc
      _ ≤ (r.choose k : ℝ) * (1 / x) ^ (r - k) *
          ((k.choose j : ℝ) * (L * x ^ (-Bsup)) ^ (k - j) * (K * x ^ (-rCutoff)) ^ j) := by
        gcongr
        · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (one_div_nonneg.mpr hx.1.le) _)
        · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg hL (Real.rpow_nonneg hx.1.le _)) _)
        · exact hEL x hx
        · exact hgK x hx
      _ = u k j * x ^ (-((r : ℝ) - k) - Bsup * (k - j) - rCutoff * j) := by
        rw [mul_pow, mul_pow, ← hpow]
        dsimp [u]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hxpow (by dsimp [u]; positivity)
  unfold RrFun
  simp_rw [Finset.mul_sum]
  calc _ ≤ ∑ k ∈ Finset.Ico 3 (r + 1),
        ‖∑ j ∈ Finset.Ico 2 (k + 1), (r.choose k : ℂ) * (1 / (x : ℂ)) ^ (r - k) *
          ((k.choose j : ℂ) * exceptionalE E x ^ (k - j) * residualG E x ^ j)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico 3 (r + 1), ∑ j ∈ Finset.Ico 2 (k + 1),
        u k j * x ^ (-rAbscissa r) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => hterm k hk j hj))
    _ = _ := by simp_rw [Finset.sum_mul]

theorem differentiableOn_Hr (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros}
    (hE : ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re) {r : ℕ} (hr : 2 ≤ r) :
    DifferentiableOn ℂ (Hr E r) (halfPlane (rAbscissa r)) := by
  obtain ⟨U, -, hU⟩ := norm_Rr_le hH hZ1 hZ2 hZ3 hStir hE hr
  exact TIdentity.differentiableOn_integral_Ioc_cpow (RrFun_meas E r) hU

end GoldbachBoundaries.Phi2HInf
