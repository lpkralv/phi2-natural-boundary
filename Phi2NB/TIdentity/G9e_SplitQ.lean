import Phi2NB.TIdentity.Basic

/-!
# Powers of `t` on `(0, 1]`

`t^r` is integrable on `(0, 1]` with `∫_0^1 t^r dt = 1/(r+1)` for `Re r > -1`, and `t^(w+1) = t^w t` for `t > 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-- `t ↦ t^r` is integrable on `(0, 1]` for `Re r > -1`. -/
theorem integrableOn_Ioc_cpow_of_neg_one_lt {r : ℂ} (hr : -1 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ r) (Ioc (0 : ℝ) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_cpow' hr)

/-- `∫_0^1 t^r dt = 1/(r+1)` for `Re r > -1`. -/
theorem integral_Ioc_cpow_of_neg_one_lt {r : ℂ} (hr : -1 < r.re) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ r = 1 / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr)]
  simp [Complex.zero_cpow hr1]

/-- For `t > 0`, `t^(w+1) = t^w * t`. -/
theorem ofReal_cpow_add_one {t : ℝ} (ht : 0 < t) (w : ℂ) :
    (t : ℂ) ^ (w + 1) = (t : ℂ) ^ w * t := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]

end TIdentity

end GoldbachBoundaries
