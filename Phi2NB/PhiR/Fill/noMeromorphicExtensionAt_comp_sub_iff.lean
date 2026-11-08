import Phi2NB.PhiR.Proof.Defs

/-! `noMeromorphicExtensionAt_comp_sub_iff` (step M3). Translation invariance of `NoMeromorphicExtensionAt`. -/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.PhiRProof.FillC

open GoldbachBoundaries

/-- Translating `codiscreteWithin`: if `S ∈ codiscreteWithin A` then `(· - c)⁻¹' S ∈ codiscreteWithin ((· - c)⁻¹' A)`. -/
theorem preimage_sub_mem_codiscreteWithin {A S : Set ℂ} (c : ℂ) (hS : S ∈ codiscreteWithin A) :
    (fun s => s - c) ⁻¹' S ∈ codiscreteWithin ((fun s => s - c) ⁻¹' A) := by
  rw [mem_codiscreteWithin] at hS ⊢
  intro x hx
  have h := hS (x - c) hx
  rw [disjoint_principal_right] at h ⊢
  have hmap : Filter.map (Homeomorph.subRight c) (𝓝[≠] x) = 𝓝[≠] (x - c) :=
    (Homeomorph.subRight c).map_punctured_nhds_eq x
  rw [← hmap, Filter.mem_map] at h
  refine Filter.mem_of_superset h ?_
  intro y hy
  simpa using hy

/-- One direction of the translation: an extension of `H` across `z₀` gives one of `H(· - c)` across `z₀ + c`. -/
theorem exists_ext_comp_sub {H : ℂ → ℂ} {U : Set ℂ} {z₀ c : ℂ} {r : ℝ}
    (h : ∃ f : ℂ → ℂ, MeromorphicOn f (ball z₀ r) ∧ f =ᶠ[codiscreteWithin (ball z₀ r ∩ U)] H) :
    ∃ f : ℂ → ℂ, MeromorphicOn f (ball (z₀ + c) r) ∧
      f =ᶠ[codiscreteWithin (ball (z₀ + c) r ∩ (fun s => s - c) ⁻¹' U)] fun s => H (s - c) := by
  obtain ⟨f, hf, hfH⟩ := h
  have hball : (fun s : ℂ => s - c) ⁻¹' ball z₀ r = ball (z₀ + c) r := by
    ext s
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    rw [show s - c - z₀ = s - (z₀ + c) by ring]
  refine ⟨fun s => f (s - c), ?_, ?_⟩
  · intro x hx
    have hx' : x - c ∈ ball z₀ r := by rw [← hball] at hx; exact hx
    exact MeromorphicAt.comp_analyticAt (f := f) (g := fun s : ℂ => s - c) (hf _ hx') (by fun_prop)
  · have := preimage_sub_mem_codiscreteWithin c hfH
    rw [preimage_inter, hball] at this
    exact this

/-- **Translation** (no number theory): `H` has no meromorphic extension across `z₀` from `U` iff
`s ↦ H(s - c)` has none across `z₀ + c` from the translate `{s : s - c ∈ U}`. -/
theorem noMeromorphicExtensionAt_comp_sub_iff' {H : ℂ → ℂ} {U : Set ℂ} {z₀ c : ℂ} :
    NoMeromorphicExtensionAt (fun s => H (s - c)) ((fun s => s - c) ⁻¹' U) (z₀ + c) ↔
      NoMeromorphicExtensionAt H U z₀ := by
  constructor
  · intro h r hr hex
    exact h r hr (exists_ext_comp_sub hex)
  · intro h r hr hex
    apply h r hr
    have h2 := exists_ext_comp_sub (c := -c) hex
    have e1 : z₀ + c + -c = z₀ := by ring
    have e2 : (fun s : ℂ => s - -c) ⁻¹' ((fun s : ℂ => s - c) ⁻¹' U) = U := by
      ext s; simp
    have e3 : (fun s : ℂ => H (s - -c - c)) = H := by
      funext s; congr 1; ring
    rw [e1, e2] at h2
    simp only [e3] at h2
    exact h2

end GoldbachBoundaries.PhiRProof.FillC
