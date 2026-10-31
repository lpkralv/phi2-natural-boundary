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
import Phi2NB.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep

/-!
# Two small bounds

`1 ≤ log(a + 3)` for `a ≥ 0`, and the bound `norm_negLogDerivZeta_le_of_sep` for `-ζ'/ζ` near a window of zeros,
with its constant taken non-negative.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `1 ≤ log(a + 3)` for `a ≥ 0`. -/
lemma one_le_log_add_three {a : ℝ} (ha : 0 ≤ a) : 1 ≤ Real.log (a + 3) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- `norm_negLogDerivZeta_le_of_sep` with a non-negative constant. -/
lemma exists_sep_bound_nonneg (hZ1 : ZeroSymmetry) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 → ∀ δ : ℝ, 0 < δ →
      δ ≤ 1 → (∀ ρ ∈ NontrivialZeros, |ρ.im - z.im| ≤ 1 → δ ≤ ‖z - ρ‖) →
        ‖negLogDerivZeta z‖ ≤ K / δ * Real.log (|z.im| + 3) := by
  obtain ⟨Ks, hKs⟩ := norm_negLogDerivZeta_le_of_sep hZ1 hRvM hLD
  refine ⟨max Ks 0, le_max_right _ _, fun z h1 h2 h3 h4 δ hδ hδ1 hsep => ?_⟩
  refine (hKs z h1 h2 h3 h4 δ hδ hδ1 hsep).trans ?_
  have : 0 ≤ Real.log (|z.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  gcongr
  exact le_max_left _ _

end GoldbachBoundaries.Paper2.M5
