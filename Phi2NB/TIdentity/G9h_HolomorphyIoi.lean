import Phi2NB.TIdentity.Basic
import Mathlib.Analysis.MellinTransform

/-!
# A Mellin integral over `(1, ∞)` of an exponentially decaying function is entire

Via `mellin_differentiableAt_of_isBigO_rpow` applied to the indicator of `(1, ∞)`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries.TIdentity

/-- **A Mellin integral over `(1, ∞)` of an exponentially decaying function is entire** (general).

Proof sketch. `mellin_differentiableAt_of_isBigO_rpow` applied to `f = indicator (Ioi 1) g`, which is `O(x^{-A})`
at `∞` for every `A` (exponential decay) and `0` near `0⁺` (so `O(x^{-B})` for `B < Re s`). -/
theorem differentiable_integral_Ioi_cpow {g : ℝ → ℂ} {C : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (1 : ℝ))))
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖g t‖ ≤ C * Real.exp (-t)) :
    Differentiable ℂ (fun s : ℂ => ∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (s - 1)) := by
  let f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator g
  have hfmeas : AEStronglyMeasurable f volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2 hg
  have hcont : Continuous (fun t : ℝ => C * Real.exp (-t)) := by fun_prop
  have hlocal : LocallyIntegrableOn f (Ioi 0) := by
    refine (hcont.locallyIntegrable.locallyIntegrableOn (Ioi 0)).mono hfmeas ?_
    exact Eventually.of_forall fun t => by
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · simpa only [f, indicator_of_mem ht] using
          (hbound t ht).trans (Real.le_norm_self (C * Real.exp (-t)))
      · simp only [f, indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
  have htop : f =O[atTop] (fun t : ℝ => Real.exp (-(1 : ℝ) * t)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simpa only [f, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), neg_one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le] using hbound t ht
  have hbot (b : ℝ) : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [f, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt_of_gt ht)]
  have heq : (fun s : ℂ => ∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (s - 1)) = mellin f := by
    funext s
    rw [mellin]
    simp_rw [f, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)),
      smul_eq_mul, mul_comm]
  rw [heq]
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0 : ℝ) < 1)
    hlocal htop (hbot (s.re - 1)) (by linarith)

end GoldbachBoundaries.TIdentity
