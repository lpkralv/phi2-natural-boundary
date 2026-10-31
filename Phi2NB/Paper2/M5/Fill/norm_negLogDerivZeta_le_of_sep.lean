import Phi2NB.Paper2.Defs
import Phi2NB.Defs
import Phi2NB.ZetaRealNonvanishing
import Phi2NB.SigmaFinite
import Phi2NB.SigmaMeromorphic
import Phi2NB.TIdentity.Assembly
import Phi2NB.Density
import Phi2NB.TBoundary
import Mathlib.MeasureTheory.Group.Prod
import Phi2NB.TIdentity.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.Module.Cardinality
import Phi2NB.Paper2.M1.Fill.BCommon
import Phi2NB.TIdentity.G8d_ContourShift
import Phi2NB.Paper2.M1.Fill.sum_zetaMult_window_le
import Phi2NB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles
import Phi2NB.Paper2.M2.Fill.ncard_zeros_im_Icc_le
import Phi2NB.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.Paper2.M2.Fill.ACommon
import PrimeNumberTheoremAnd.Consequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Phi2NB.Paper2.M4b.Fill.BCommon
import Phi2NB.Paper2.M4b.Fill.isBigO_mul_sub_residue
import Phi2NB.Paper2.M5.Fill.order_residue_of_codiscrete_line

/-! `-ζ'/ζ` away from the zeros of a window: `norm_negLogDerivZeta_le_of_sep`. (LogDerivZetaLocal) at `z`; each window term
`m(ρ)/(z - ρ)` has norm `≤ m(ρ)/δ`; `sum_zetaMult_window_le` bounds the window's total multiplicity. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`A = -ζ'/ζ` away from the zeros of a window** ((ZeroSymmetry), (RiemannVonMangoldt), (LogDerivZetaLocal)). -/
theorem norm_negLogDerivZeta_le_of_sep (hZ1 : ZeroSymmetry) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) :
    ∃ C : ℝ, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ ∈ NontrivialZeros, |ρ.im - z.im| ≤ 1 → δ ≤ ‖z - ρ‖) →
        ‖negLogDerivZeta z‖ ≤ C / δ * Real.log (|z.im| + 3) := by
  obtain ⟨C₃, hC₃⟩ := hLD
  obtain ⟨C, hC⟩ := sum_zetaMult_window_le hZ1 hRvM
  refine ⟨max C₃ 0 + max C 0, fun z hz1 hz2 hzim hz0 δ hδ hδ1 hsep => ?_⟩
  set W := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1} with hWdef
  obtain ⟨hWfin, hWsum⟩ := hC z.im
  have hZ := hC₃ z hz1 hz2 hzim hz0
  set S := ∑ᶠ ρ ∈ W, (zetaMult ρ : ℂ) / (z - ρ) with hSdef
  have hlog0 : 0 ≤ Real.log |z.im| := Real.log_nonneg (by linarith)
  have hloglt : Real.log |z.im| ≤ Real.log (|z.im| + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL0 : 0 ≤ Real.log (|z.im| + 3) := le_trans hlog0 hloglt
  -- the window sum
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
