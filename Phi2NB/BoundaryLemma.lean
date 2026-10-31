import Phi2NB.Defs

/-!
# Agreement off a discrete set and agreement near a point

If two functions agree off a discrete subset of a set `S`, they agree on a punctured neighbourhood of every point
`a` of which `S` is a neighbourhood. This is the step that transfers pole orders between two functions that agree
off a discrete set.
-/

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- Agreement off a discrete subset of `S` gives agreement on a punctured neighbourhood of every
point `a` of which `S` is a neighbourhood. -/
lemma eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin {f F : ℂ → ℂ} {S : Set ℂ} {a : ℂ}
    (h : f =ᶠ[codiscreteWithin S] F) (ha : S ∈ 𝓝 a) : f =ᶠ[𝓝[≠] a] F := by
  have hd := (mem_codiscreteWithin.mp h) a (mem_of_mem_nhds ha)
  rw [disjoint_principal_right] at hd
  filter_upwards [hd, nhdsWithin_le_nhds ha] with y hy hyS
  by_contra hne
  exact hy ⟨hyS, hne⟩

end GoldbachBoundaries
