import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.sum_zetaMult_window_le

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem norm_negLogDerivZeta_le_of_sep_fullZ2 (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ C : ℝ, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ ∈ NontrivialZeros, |ρ.im - z.im| ≤ 1 → δ ≤ ‖z - ρ‖) →
        ‖negLogDerivZeta z‖ ≤ C / δ * Real.log (|z.im| + 3) := by
  obtain ⟨C₃, hC₃⟩ := hZ3
  obtain ⟨C, hC⟩ := _root_.GoldbachBoundaries.Paper2.M1.sum_zetaMult_window_le_fullZ2 hZ1 hZ2
  refine ⟨max C₃ 0 + max C 0, fun z hz1 hz2 hzim hz0 δ hδ hδ1 hsep => ?_⟩
  set W := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1} with hWdef
  obtain ⟨hWfin, hWsum⟩ := hC z.im
  have hZ := hC₃ z hz1 hz2 hzim hz0
  set S := ∑ᶠ ρ ∈ W, (zetaMult ρ : ℂ) / (z - ρ) with hSdef
  have hlog0 : 0 ≤ Real.log |z.im| := Real.log_nonneg (by linarith)
  have hloglt : Real.log |z.im| ≤ Real.log (|z.im| + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL0 : 0 ≤ Real.log (|z.im| + 3) := le_trans hlog0 hloglt
  
  have hS : ‖S‖ ≤ (∑ᶠ ρ ∈ W, (zetaMult ρ : ℝ)) / δ := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hWfin, finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [Set.Finite.mem_toFinset] at hρ
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep ρ hρ.1 hρ.2)
  have hinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hA : ‖negLogDerivZeta z‖ ≤ C₃ * Real.log |z.im| + ‖S‖ := by
    rw [negLogDerivZeta, norm_neg]
    calc ‖deriv riemannZeta z / riemannZeta z‖
        = ‖(deriv riemannZeta z / riemannZeta z - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ ‖deriv riemannZeta z / riemannZeta z - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := by gcongr
  have h1 : C₃ * Real.log |z.im| ≤ max C₃ 0 / δ * Real.log (|z.im| + 3) := by
    calc C₃ * Real.log |z.im| ≤ max C₃ 0 * Real.log |z.im| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
      _ ≤ max C₃ 0 * Real.log (|z.im| + 3) :=
          mul_le_mul_of_nonneg_left hloglt (le_max_right _ _)
      _ = max C₃ 0 * 1 * Real.log (|z.im| + 3) := by ring
      _ ≤ max C₃ 0 * (1 / δ) * Real.log (|z.im| + 3) := by
          gcongr
      _ = _ := by ring
  have h2 : (∑ᶠ ρ ∈ W, (zetaMult ρ : ℝ)) / δ ≤ max C 0 / δ * Real.log (|z.im| + 3) := by
    rw [div_mul_eq_mul_div]
    gcongr
    exact hWsum.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hL0)
  calc ‖negLogDerivZeta z‖ ≤ C₃ * Real.log |z.im| + ‖S‖ := hA
    _ ≤ max C₃ 0 / δ * Real.log (|z.im| + 3) + max C 0 / δ * Real.log (|z.im| + 3) := by
        linarith
    _ = _ := by ring

end GoldbachBoundaries.Paper2.M5
