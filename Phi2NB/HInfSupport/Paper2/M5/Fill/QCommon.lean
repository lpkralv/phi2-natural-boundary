import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M5.Fill.QCommon`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

lemma exists_sep_bound_nonneg_fullZ2 (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 → ∀ δ : ℝ, 0 < δ →
      δ ≤ 1 → (∀ ρ ∈ NontrivialZeros, |ρ.im - z.im| ≤ 1 → δ ≤ ‖z - ρ‖) →
        ‖negLogDerivZeta z‖ ≤ K / δ * Real.log (|z.im| + 3) := by
  obtain ⟨Ks, hKs⟩ := _root_.GoldbachBoundaries.Paper2.M5.norm_negLogDerivZeta_le_of_sep_fullZ2 hZ1 hZ2 hZ3
  refine ⟨max Ks 0, le_max_right _ _, fun z h1 h2 h3 h4 δ hδ hδ1 hsep => ?_⟩
  refine (hKs z h1 h2 h3 h4 δ hδ hδ1 hsep).trans ?_
  have : 0 ≤ Real.log (|z.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  gcongr
  exact le_max_left _ _

end GoldbachBoundaries.Paper2.M5
