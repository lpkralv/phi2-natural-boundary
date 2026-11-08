import Phi2NB.PhiR.Proof.Defs
import Phi2NB.Phi2.Fill.ACommon
import Mathlib.Data.Nat.Choose.Cast

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillA

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- Remove the three low-degree terms of the binomial expansion. -/
private theorem QR_eq_sum_bound {r : ℕ} (hr : 2 ≤ r) {t : ℝ} (ht : 0 < t) :
    QR r t = ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℝ) * (1 / t) ^ (r - k) * hL t ^ k := by
  have he : FL t = hL t + 1 / t := by dsimp [hL]; ring
  have hsum := add_pow (hL t) (1 / t) r
  rw [← Finset.sum_range_add_sum_Ico _ (show 3 ≤ r + 1 by omega)] at hsum
  have htail : (∑ k ∈ Finset.Ico 3 (r + 1), hL t ^ k * (1 / t) ^ (r - k) * (r.choose k : ℝ)) =
      ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℝ) * (1 / t) ^ (r - k) * hL t ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [htail] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, one_mul,
    mul_one, Nat.sub_zero, pow_one, Nat.cast_choose_two] at hsum
  have hp1 : (1 / t) ^ (r - 1) = (1 / t) ^ (r - 2) * (1 / t) := by
    rw [← pow_succ]; congr 1; omega
  have hp0 : (1 / t) ^ r = (1 / t) ^ (r - 2) * (1 / t) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [← he] at hsum
  unfold QR cC cB cA
  simp only [div_eq_mul_inv, ← inv_pow]
  simp only [one_div] at hsum hp1 hp0
  rw [he, hp1, hp0] at hsum ⊢
  simp only [one_div, one_mul] at *
  rw [hsum]
  ring

/-- Bound each binomial term by the exponent of its cubic term. -/
theorem norm_QR_le' (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1) :
    ContinuousOn (QR r) (Ioi 0) ∧
      ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, |QR r t| ≤ C * t ^ (-((r : ℝ) - 3 + 3 * b)) := by
  obtain ⟨C, hC⟩ := Phi2Proof.FillA.norm_hL_le' hRH hb hb1
  have hF := Phi2Proof.FillA.FL_continuousOn_and_le_exp.1
  have hcont : ContinuousOn (QR r) (Ioi 0) := by
    unfold QR
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · exact (hF.pow r).sub ((continuousOn_const.mul (hF.pow 2)).div
          (continuousOn_id.pow (r - 2)) (fun t ht => pow_ne_zero _ (ne_of_gt ht)))
      · exact (continuousOn_const.mul hF).div (continuousOn_id.pow (r - 1))
          (fun t ht => pow_ne_zero _ (ne_of_gt ht))
    · exact continuousOn_const.div (continuousOn_id.pow r)
        (fun t ht => pow_ne_zero _ (ne_of_gt ht))
  refine ⟨hcont, ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℝ) * max C 0 ^ k, ?_⟩
  intro t ht
  rw [QR_eq_sum_bound hr ht.1, Finset.sum_mul]
  calc
    |∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℝ) * (1 / t) ^ (r - k) * hL t ^ k|
      ≤ ∑ k ∈ Finset.Ico 3 (r + 1), |(r.choose k : ℝ) * (1 / t) ^ (r - k) * hL t ^ k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hk3 : 3 ≤ k := (Finset.mem_Ico.mp hk).1
      have hkr : k ≤ r := by have := (Finset.mem_Ico.mp hk).2; omega
      have hpow : (1 / t) ^ (r - k) * (t ^ (-b)) ^ k =
          t ^ (-((r : ℝ) - (k : ℝ)) - b * k) := by
        rw [one_div, inv_pow, ← Real.rpow_natCast t (r - k), ← Real.rpow_neg ht.1.le,
          ← Real.rpow_natCast (t ^ (-b)) k, ← Real.rpow_mul ht.1.le, ← Real.rpow_add ht.1]
        rw [Nat.cast_sub hkr]
        congr 1
        ring
      have hexp : t ^ (-((r : ℝ) - (k : ℝ)) - b * k) ≤
          t ^ (-((r : ℝ) - 3 + 3 * b)) := by
        apply Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
        have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
        nlinarith
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (pow_nonneg (one_div_nonneg.mpr ht.1.le) _), abs_pow]
      calc
        (r.choose k : ℝ) * (1 / t) ^ (r - k) * |hL t| ^ k
          ≤ (r.choose k : ℝ) * (1 / t) ^ (r - k) * (max C 0 * t ^ (-b)) ^ k := by
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_left₀ (abs_nonneg _) ((hC t ht.1).trans
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.1.le _))) _
            · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (one_div_nonneg.mpr ht.1.le) _)
        _ = (r.choose k : ℝ) * max C 0 ^ k * t ^ (-((r : ℝ) - (k : ℝ)) - b * k) := by
            rw [mul_pow, ← hpow]
            ring
        _ ≤ (r.choose k : ℝ) * max C 0 ^ k * t ^ (-((r : ℝ) - 3 + 3 * b)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)

end GoldbachBoundaries.PhiRProof.FillA
