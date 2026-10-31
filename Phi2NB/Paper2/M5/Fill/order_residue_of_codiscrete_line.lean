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

/-! A simple pole on the line `σ = 1` from a radial limit. Let `F` be holomorphic on `ℍ`, `Re s₀ = 1`, and let `f`
be meromorphic on a disc `B(s₀, r)` and equal to `F` off a discrete subset of `B(s₀, r) ∩ ℍ`. If
`η F(s₀ + η) → c ≠ 0` as `η ↓ 0`, then `f` has a simple pole at `s₀` with residue `c`. The order is read off along
the horizontal ray from `s₀` into `ℍ`, on which `f = F` near `s₀`. -/
noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M5
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem order_residue_of_codiscrete_line {F f : ℂ → ℂ} (hF : DifferentiableOn ℂ F HH) {s₀ : ℂ}
    (hs₀ : s₀.re = 1) {r : ℝ} (hr : 0 < r) (hf : MeromorphicOn f (ball s₀ r))
    (hfF : f =ᶠ[codiscreteWithin (ball s₀ r ∩ HH)] F) {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (fun η : ℝ => (η : ℂ) * F (s₀ + η)) (𝓝[>] 0) (𝓝 c)) :
    meromorphicOrderAt f s₀ = -1 ∧ HasResidue f s₀ c := by
  have hf0 : MeromorphicAt f s₀ := hf s₀ (mem_ball_self hr)
  obtain ⟨ρ, hρ, hρan⟩ : ∃ ρ > 0, ∀ z ∈ ball s₀ ρ, z ≠ s₀ → AnalyticAt ℂ f z := by
    have h := hf0.eventually_analyticAt
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h
    obtain ⟨ρ, hρ, h⟩ := h
    exact ⟨ρ, hρ, fun z hz hne => h z hz hne⟩
  have hι : Tendsto (fun η : ℝ => s₀ + η) (𝓝[>] 0) (𝓝[≠] s₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_const_nhds.add
        (Complex.continuous_ofReal.tendsto 0)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      simp only [mem_compl_iff, mem_singleton_iff]
      intro heq
      have : (η : ℂ) = 0 := add_left_cancel (heq.trans (add_zero s₀).symm)
      exact (ne_of_gt hη) (Complex.ofReal_eq_zero.mp this)
  have hlimf : Tendsto (fun η : ℝ => (η : ℂ) * f (s₀ + η)) (𝓝[>] 0) (𝓝 c) := by
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hρ hr)] with η hη
    have hdist : dist (s₀ + (η : ℂ)) s₀ = η := by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη.1]
    have hzρ : s₀ + (η : ℂ) ∈ ball s₀ ρ := by
      rw [mem_ball, hdist]; exact hη.2.trans_le (min_le_left _ _)
    have hzr : s₀ + (η : ℂ) ∈ ball s₀ r := by
      rw [mem_ball, hdist]; exact hη.2.trans_le (min_le_right _ _)
    have hzH : s₀ + (η : ℂ) ∈ HH := by
      show 1 < (s₀ + (η : ℂ)).re
      simp only [Complex.add_re, Complex.ofReal_re, hs₀]
      linarith [hη.1]
    have hzne : s₀ + (η : ℂ) ≠ s₀ := by
      intro heq
      have := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.ofReal_re] at this
      linarith [hη.1]
    have heq := eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hfF
      ((isOpen_ball.inter (isOpen_halfPlane 1)).mem_nhds ⟨hzr, hzH⟩)
    have hval : f (s₀ + η) = F (s₀ + η) := tendsto_nhds_unique_of_eventuallyEq
      ((hρan _ hzρ hzne).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hF.analyticAt ((isOpen_halfPlane 1).mem_nhds hzH)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds) heq
    rw [hval]
  set g : ℂ → ℂ := fun z => (z - s₀) * f z with hgdef
  have hlin : MeromorphicAt (fun z : ℂ => z - s₀) s₀ := by fun_prop
  have hg : MeromorphicAt g s₀ := hlin.mul hf0
  have hgc : Tendsto (g ∘ fun η : ℝ => s₀ + η) (𝓝[>] 0) (𝓝 c) := by
    simpa [Function.comp_def, hgdef] using hlimf
  have hnn : 0 ≤ meromorphicOrderAt g s₀ := by
    by_contra hneg
    have hcob := (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hneg)).comp hι
    exact hgc.not_tendsto (disjoint_nhds_cobounded c) hcob
  obtain ⟨L, hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hg hnn
  have hLc : L = c := tendsto_nhds_unique (hL.comp hι) hgc
  subst hLc
  have hres : HasResidue f s₀ L := hL
  have hg0 : meromorphicOrderAt g s₀ = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hg).1 ⟨L, hc, hL⟩
  refine ⟨?_, hres⟩
  have hmul : meromorphicOrderAt g s₀ = 1 + meromorphicOrderAt f s₀ := by
    rw [hgdef, fun_meromorphicOrderAt_mul hlin hf0, meromorphicOrderAt_id_sub_const]
  rw [hg0] at hmul
  cases hfo : meromorphicOrderAt f s₀ with
  | top => rw [hfo] at hmul; simp at hmul
  | coe n =>
    rw [hfo] at hmul
    have : (0 : ℤ) = 1 + n := by exact_mod_cast hmul
    have hn : n = -1 := by omega
    simp [hn]

end GoldbachBoundaries.Paper2.M5
