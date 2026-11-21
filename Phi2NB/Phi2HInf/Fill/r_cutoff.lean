import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.Bsup_facts
import Phi2NB.HInfSupport.Paper2.M1.Fill.Bsup_lt_one_of_Hinf
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Fill.zero_mellin
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M1Regularization
import Phi2NB.Phi2HInf.Proof.RDefs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.r_cutoff`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof PhiRProof

theorem rCutoff_bounds (hH : Hinf) (hZ1 : Z1) :
    1 / 2 < rCutoff ∧ rCutoff < 1 ∧ 0 < rMargin ∧ rMargin ≤ 1 / 4 := by
  have hb := M1.Bsup_facts hZ1
  have hB := M1.Bsup_lt_one_of_Hinf hH
  dsimp [rCutoff, rMargin]
  constructor
  · linarith
  constructor
  · linarith [hb.2.1]
  constructor <;> linarith [hb.2.1]

theorem exists_cutoff (hH : Hinf) :
    ∃ E : Finset NontrivialZeros, ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re := by
  classical
  have hd : 0 < (1 - Bsup) / 6 := by linarith [M1.Bsup_lt_one_of_Hinf hH]
  have hfin : {ρ : NontrivialZeros | rCutoff < (ρ : ℂ).re}.Finite :=
    (hH ((1 - Bsup) / 6) hd).preimage Subtype.val_injective.injOn |>.subset
      (fun ρ hρ => ⟨ρ.2, hρ⟩)
  exact ⟨hfin.toFinset, fun ρ => hfin.mem_toFinset⟩

theorem norm_E_le (hZ1 : Z1) (E : Finset NontrivialZeros) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖exceptionalE E x‖ ≤ L * x ^ (-Bsup) := by
  refine ⟨∑ ρ ∈ E, ‖zeroCoef ρ‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro x hx
  unfold exceptionalE
  calc
    ‖∑ ρ ∈ E, -zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖ ≤
        ∑ ρ ∈ E, ‖-zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ E, ‖zeroCoef ρ‖ * x ^ (-Bsup) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
        (neg_le_neg ((M1.Bsup_facts hZ1).1 ρ ρ.2))) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

set_option maxHeartbeats 800000 in
theorem norm_g_le (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    {E : Finset NontrivialZeros} (hE : ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖residualG E x‖ ≤ K * x ^ (-rCutoff) := by
  classical
  have ha := summable_norm_zeroCoef_hinf hZ1 hZ2 hStir
  obtain ⟨K, hK, hV⟩ := norm_V_le hZ1 hZ2 hZ3 hStir
  let S : ℝ := ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E}, ‖zeroCoef ρ.1‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hb : 0 < rCutoff := by linarith [(rCutoff_bounds hH hZ1).1]
  refine ⟨S + ‖c0‖ + K, by positivity, ?_⟩
  intro x hx
  have hpow : 1 ≤ x ^ (-rCutoff) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 (by linarith)
  have hrem : Summable (fun ρ : {ρ : NontrivialZeros // ρ ∉ E} =>
      ‖zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ))‖) :=
    summable_norm_cpow_family (ι := {ρ : NontrivialZeros // ρ ∉ E})
      (fun ρ => zeroCoef ρ.1) (fun ρ => (ρ.1 : ℂ)) (r := rCutoff)
      (ha.subtype (fun ρ : NontrivialZeros => ρ ∉ E)) (fun ρ => le_of_not_gt (fun h => ρ.2 ((hE ρ.1).2 h))) hx
  have hrembound : ‖∑' ρ : {ρ : NontrivialZeros // ρ ∉ E},
      zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ))‖ ≤ S * x ^ (-rCutoff) := by
    calc _ ≤ ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E},
          ‖zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ))‖ := norm_tsum_le_tsum_norm hrem
      _ ≤ ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E}, ‖zeroCoef ρ.1‖ * x ^ (-rCutoff) := by
        apply hrem.tsum_le_tsum _ ((ha.subtype (fun ρ : NontrivialZeros => ρ ∉ E)).mul_right _)
        intro ρ
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
          (by have := le_of_not_gt (fun h => ρ.2 ((hE ρ.1).2 h)); linarith)) (norm_nonneg _)
      _ = _ := tsum_mul_right
  have hsum := (summable_norm_cpow_family (fun ρ : NontrivialZeros => zeroCoef ρ)
    (fun ρ => (ρ : ℂ)) (r := 1) ha (fun ρ => ρ.2.2.2.le) hx).of_norm.sum_add_tsum_subtype_compl E
  have heq : residualG E x =
      -(∑' ρ : {ρ : NontrivialZeros // ρ ∉ E}, zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ))) + c0 + V x := by
    rw [residualG, hL_explicit_hinf hZ1 hZ2 hZ3 hStir hx.1]
    unfold zeroSum exceptionalE
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [← hsum]
    ring
  have hv : ‖V x‖ ≤ K := (hV x hx.1).trans (by
    have := Real.rpow_le_one hx.1.le hx.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith)
  rw [heq]
  calc _ ≤ ‖-(∑' ρ : {ρ : NontrivialZeros // ρ ∉ E},
        zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ))) + c0‖ + ‖V x‖ := norm_add_le _ _
    _ ≤ S * x ^ (-rCutoff) + ‖c0‖ + K := by
      have hh := norm_add_le (-(∑' ρ : {ρ : NontrivialZeros // ρ ∉ E},
        zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ)))) c0
      rw [norm_neg] at hh
      linarith
    _ ≤ _ := by nlinarith [norm_nonneg c0]

end GoldbachBoundaries.Phi2HInf
