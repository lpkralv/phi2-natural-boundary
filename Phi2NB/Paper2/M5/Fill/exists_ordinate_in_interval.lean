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
import Phi2NB.Paper2.M5.Fill.exists_sep_height
import Phi2NB.Paper2.M5.Fill.QCommon
import Phi2NB.Paper2.M5.Fill.rectangleIntegral'_eq_sum_of_simplePoles_rect
import Phi2NB.Paper2.M5.Fill.summable_zeros_inv_sq

/-!
# An ordinate in every interval far out

Littlewood's theorem (`LittlewoodGap`) puts an ordinate in every interval of length `ℓ` far out: `log log log t → ∞`, so
eventually `a / log log log t < ℓ/2`, and the theorem applied at the centre `t + ℓ/2` of `(t, t + ℓ)` gives the ordinate.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem exists_ordinate_in_interval (hL : LittlewoodGap) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ Y₀ : ℝ, ∀ t : ℝ, Y₀ ≤ t → ∃ ρ ∈ NontrivialZeros, t < ρ.im ∧ ρ.im < t + ℓ := by
  obtain ⟨a, ha⟩ := hL
  have hlog3 : Tendsto (fun t : ℝ => Real.log (Real.log (Real.log t))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hdiv : Tendsto (fun t : ℝ => a / Real.log (Real.log (Real.log t))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog3
  have hsmall : ∀ᶠ t in atTop, a / Real.log (Real.log (Real.log t)) < ℓ / 2 :=
    hdiv.eventually (gt_mem_nhds (by linarith))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (ha.and hsmall)
  refine ⟨Y, fun t ht => ?_⟩
  obtain ⟨⟨ρ, hρ, hlt⟩, hs⟩ := hY (t + ℓ / 2) (by linarith)
  have h := lt_trans hlt hs
  rw [abs_lt] at h
  exact ⟨ρ, hρ, by linarith [h.1], by linarith [h.2]⟩

end GoldbachBoundaries.Paper2.M5
