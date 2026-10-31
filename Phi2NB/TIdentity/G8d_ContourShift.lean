import Phi2NB.TIdentity.G7d_QcontBound
import Phi2NB.TIdentity.Basic

/-!
# Differentiability facts for the contour shift

`Γ` is differentiable on `Re z > 0`, and `z ↦ t^{-z}` is entire for `t > 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- `Γ` is differentiable on `Re z > 0`. -/
theorem differentiableAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gamma z :=
  differentiableAt_Gamma _ fun m h => by
    rw [h] at hz
    simp at hz
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `z ↦ t^{-z}` is entire for `t > 0`. -/
theorem differentiableAt_ofReal_cpow_neg {t : ℝ} (ht : 0 < t) (z : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => (t : ℂ) ^ (-z)) z :=
  differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast ht.ne'))

end TIdentity

end GoldbachBoundaries
