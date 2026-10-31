import Phi2NB.TIdentity.Basic
import Mathlib.Analysis.MellinTransform

/-!
# Holomorphy of a Mellin integral over `(0, 1]`

Via `mellin_differentiableAt_of_isBigO_rpow` applied to the indicator of `(0, 1]`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries.TIdentity

/-- **Holomorphy of a Mellin integral over `(0, 1]`** (general). If `|g(t)| ≤ C t^{-a}` on `(0, 1]`, then
`s ↦ ∫_0^1 g(t) t^{s-1} dt` is holomorphic on `Re s > a`.

Proof sketch. Apply `mellin_differentiableAt_of_isBigO_rpow` (Mathlib, `MellinTransform.lean`) to
`f = indicator (Ioc 0 1) g`: it is `0` near `∞` (so `O(x^{-A})` for `A > Re s`), `O(x^{-a})` near
`0⁺`, and locally integrable on `(0, ∞)` (bounded on compacts of `(0, 1]`, zero beyond). Then
`mellin f s = ∫_{Ioc 0 1} t^{s-1} • g t` (`setIntegral_indicator`), which is the integral here up to
commuting the product. -/
theorem differentiableOn_integral_Ioc_cpow {g : ℝ → ℂ} {a C : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1)))
    (hbound : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g t‖ ≤ C * t ^ (-a)) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioc (0 : ℝ) 1, g t * (t : ℂ) ^ (s - 1)) (halfPlane a) := by
  let f : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator g
  have hfmeas : AEStronglyMeasurable f volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2 hg
  have hcont : ContinuousOn (fun t : ℝ => C * t ^ (-a)) (Ioi 0) := by
    refine continuousOn_const.mul ?_
    exact continuousOn_of_forall_continuousAt fun t ht =>
      Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))
  have hlocal : LocallyIntegrableOn f (Ioi 0) := by
    refine (hcont.locallyIntegrableOn measurableSet_Ioi).mono hfmeas ?_
    exact Eventually.of_forall fun t => by
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · simpa only [f, indicator_of_mem ht] using
          (hbound t ht).trans (Real.le_norm_self (C * t ^ (-a)))
      · simp only [f, indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-a)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht0 ht1
    simpa only [f, indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1.le⟩),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)] using hbound t ⟨ht0, ht1.le⟩
  have htop (A : ℝ) : f =O[atTop] (fun t : ℝ => t ^ (-A)) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simp [f, indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => not_le_of_gt ht h.2)]
  have heq : (fun s : ℂ => ∫ t in Ioc (0 : ℝ) 1, g t * (t : ℂ) ^ (s - 1)) = mellin f := by
    funext s
    rw [mellin]
    simp_rw [f, ← indicator_smul, setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self, smul_eq_mul, mul_comm]
  rw [heq]
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow hlocal (htop (s.re + 1))
    (lt_add_one _) hbot hs).differentiableWithinAt

end GoldbachBoundaries.TIdentity
