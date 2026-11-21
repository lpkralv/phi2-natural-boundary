import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Statements

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Classical`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem phi2_hinf_natural_boundary_classical (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : EqOn F Phi2 (halfPlane 2))
    (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball (1 + τ * I) ε) ∧
      ∀ s ∈ ball (1 + τ * I) ε ∩ HH, AnalyticAt ℂ F s → g s = F s := by
  rintro ⟨g, hg, hgF⟩
  have hcod : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 := by
    filter_upwards [self_mem_codiscreteWithin (halfPlane 2)] with s hs using hFΦ hs
  have hline : (1 + τ * I : ℂ) ∈ lineOne := by
    show (1 + τ * I : ℂ).re = 1
    simp
  refine (phi2_hinf_natural_boundary hH hZ1 hZ2 hZ3 hL hStir).2 F hF hcod (1 + τ * I) hline ε hε
    ⟨g, hg, ?_⟩
  have h1 := hF.eventually_codiscreteWithin_analyticAt
  have h2 : ∀ᶠ s in codiscreteWithin (ball (1 + τ * I) ε ∩ HH), AnalyticAt ℂ F s :=
    Filter.codiscreteWithin_mono inter_subset_right h1
  filter_upwards [h2, self_mem_codiscreteWithin (ball (1 + τ * I) ε ∩ HH)] with s hs hsm
    using hgF s hsm hs

theorem phiR_hinf_natural_boundary_classical (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : EqOn F (PhiR r) (halfPlane r))
    (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      ∀ s ∈ ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1), AnalyticAt ℂ F s → g s = F s := by
  rintro ⟨g, hg, hgF⟩
  have hcod : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r := by
    filter_upwards [self_mem_codiscreteWithin (halfPlane r)] with s hs using hFΦ hs
  have hline : ((r : ℂ) - 1 + τ * I) ∈ lineAt ((r : ℝ) - 1) := by
    show ((r : ℂ) - 1 + τ * I).re = (r : ℝ) - 1
    simp
  refine (phiR_hinf_natural_boundary hH hZ1 hZ2 hZ3 hL hStir hr).2 F hF hcod _ hline ε hε ⟨g, hg, ?_⟩
  have h1 := hF.eventually_codiscreteWithin_analyticAt
  have h2 : ∀ᶠ s in codiscreteWithin (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1)),
      AnalyticAt ℂ F s :=
    Filter.codiscreteWithin_mono inter_subset_right h1
  filter_upwards [h2, self_mem_codiscreteWithin (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1))]
    with s hs hsm using hgF s hsm hs

end GoldbachBoundaries.Phi2HInf
