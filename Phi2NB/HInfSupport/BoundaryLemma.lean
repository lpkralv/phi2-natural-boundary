import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.BoundaryLemma`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

theorem noMeromorphicExtensionAt_of_poles_accumulate {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U)
    (hacc : z₀ ∈ closure ({a ∈ U | meromorphicOrderAt F a < 0} \ {z₀})) :
    NoMeromorphicExtensionAt F U z₀ := by
  rintro r hr ⟨f, hf, hfF⟩
  have hev : ∀ᶠ y in 𝓝[≠] z₀, AnalyticAt ℂ f y ∧ y ∈ ball z₀ r :=
    (hf z₀ (mem_ball_self hr)).eventually_analyticAt.and
      (nhdsWithin_le_nhds (ball_mem_nhds z₀ hr))
  obtain ⟨a, ⟨haA, haB⟩, haU, hord⟩ :=
    (hev.and_frequently (mem_closure_ne_iff_frequently_within.mp hacc)).exists
  have hEq : f =ᶠ[𝓝[≠] a] F :=
    eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hfF
      ((isOpen_ball.inter hU).mem_nhds ⟨haB, haU⟩)
  have hnonneg := haA.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hEq] at hnonneg
  exact (not_lt.mpr hnonneg) hord

theorem noMeromorphicExtensionAt_of_poles_in_every_ball {F : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U)
    (hacc : ∀ ε > 0, ∃ a ∈ U, a ≠ z₀ ∧ a ∈ ball z₀ ε ∧ meromorphicOrderAt F a < 0) :
    NoMeromorphicExtensionAt F U z₀ := by
  refine noMeromorphicExtensionAt_of_poles_accumulate hU (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  obtain ⟨a, haU, hne, hab, hord⟩ := hacc ε hε
  exact ⟨a, ⟨⟨haU, hord⟩, hne⟩, by rw [dist_comm]; exact hab⟩

end GoldbachBoundaries
