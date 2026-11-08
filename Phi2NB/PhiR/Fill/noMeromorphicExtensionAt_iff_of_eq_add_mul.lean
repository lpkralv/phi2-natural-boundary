import Phi2NB.PhiR.Proof.Defs

/-! `noMeromorphicExtensionAt_iff_of_eq_add_mul` (step M3). `F = D + f·H` with `D` meromorphic and `f` analytic
non-zero near `z₀` ⟹ `F` extends across `z₀` iff `H` does. -/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.PhiRProof.FillC

open GoldbachBoundaries

/-- **Adding a meromorphic function and multiplying by a non-vanishing analytic one** (no number theory). -/
theorem noMeromorphicExtensionAt_iff_of_eq_add_mul' {F D f H : ℂ → ℂ} {U W : Set ℂ} {z₀ : ℂ}
    (hW : IsOpen W) (hz₀ : z₀ ∈ W) (hD : MeromorphicOn D W) (hf : AnalyticOnNhd ℂ f W)
    (hf0 : ∀ s ∈ W, f s ≠ 0) (hF : F =ᶠ[codiscreteWithin U] fun s => D s + f s * H s) :
    NoMeromorphicExtensionAt F U z₀ ↔ NoMeromorphicExtensionAt H U z₀ := by
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW z₀ hz₀
  -- the disc of radius `min r ε` lies in `W` and in the disc of radius `r`
  have hsmall : ∀ r : ℝ, ball z₀ (min r ε) ⊆ W := fun r =>
    (ball_subset_ball (min_le_right _ _)).trans hεW
  have hsub : ∀ r : ℝ, ball z₀ (min r ε) ∩ U ⊆ ball z₀ r ∩ U := fun r =>
    inter_subset_inter_left _ (ball_subset_ball (min_le_left _ _))
  have hFr : ∀ r : ℝ, F =ᶠ[codiscreteWithin (ball z₀ (min r ε) ∩ U)] fun s => D s + f s * H s := fun r =>
    hF.filter_mono (Filter.codiscreteWithin_mono inter_subset_right)
  constructor
  · -- an extension `g` of `H` gives the extension `D + f g` of `F`
    intro hNo r hr ⟨g, hg, hgH⟩
    have hr' : 0 < min r ε := lt_min hr hε
    refine hNo (min r ε) hr' ⟨fun s => D s + f s * g s, ?_, ?_⟩
    · intro x hx
      exact (hD x (hsmall r hx)).add ((hf x (hsmall r hx)).meromorphicAt.mul
        (hg x (ball_subset_ball (min_le_left _ _) hx)))
    · have hgH' := hgH.filter_mono (Filter.codiscreteWithin_mono (hsub r))
      filter_upwards [hgH', hFr r] with s h1 h2
      rw [h2, h1]
  · -- an extension `g` of `F` gives the extension `(g - D)/f` of `H`
    intro hNo r hr ⟨g, hg, hgF⟩
    have hr' : 0 < min r ε := lt_min hr hε
    refine hNo (min r ε) hr' ⟨fun s => (g s - D s) / f s, ?_, ?_⟩
    · intro x hx
      exact ((hg x (ball_subset_ball (min_le_left _ _) hx)).sub (hD x (hsmall r hx))).div
        (hf x (hsmall r hx)).meromorphicAt
    · have hgF' := hgF.filter_mono (Filter.codiscreteWithin_mono (hsub r))
      filter_upwards [hgF', hFr r, Filter.self_mem_codiscreteWithin (ball z₀ (min r ε) ∩ U)] with
        s h1 h2 h3
      have hfs : f s ≠ 0 := hf0 s (hsmall r h3.1)
      rw [h1, h2]
      field_simp
      ring

end GoldbachBoundaries.PhiRProof.FillC
