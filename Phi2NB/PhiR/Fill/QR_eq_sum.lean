import Phi2NB.PhiR.Proof.Defs
import Phi2NB.Phi2.Fill.ACommon
import Mathlib.Data.Nat.Choose.Cast

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillA

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- Remove the three low-degree terms of the binomial expansion. -/
theorem QR_eq_sum' {r : ℕ} (hr : 2 ≤ r) {t : ℝ} (ht : 0 < t) :
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

end GoldbachBoundaries.PhiRProof.FillA
