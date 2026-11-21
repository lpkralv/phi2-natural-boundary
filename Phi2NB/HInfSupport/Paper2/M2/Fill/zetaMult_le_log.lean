import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.sum_zetaMult_window_le

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M2.Fill.zetaMult_le_log`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Set
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem zetaMult_le_log_fullZ2 (hZ1 : Z1) (hZ2 : Z2) :
    ∃ C : ℝ, ∀ ρ ∈ NontrivialZeros, (zetaMult ρ : ℝ) ≤ C * Real.log (|ρ.im| + 3) := by
  classical
  obtain ⟨C, hC⟩ := _root_.GoldbachBoundaries.Paper2.M1.sum_zetaMult_window_le_fullZ2 hZ1 hZ2
  refine ⟨C, fun ρ hρ => ?_⟩
  obtain ⟨hf, hb⟩ := hC ρ.im
  rw [finsum_mem_eq_finite_toFinset_sum _ hf] at hb
  exact (Finset.single_le_sum (fun r _ => Nat.cast_nonneg (zetaMult r))
    (hf.mem_toFinset.mpr ⟨hρ, by simp⟩)).trans hb
end GoldbachBoundaries.Paper2.M2
