import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.phi2_hinf_continuation
import Phi2NB.Phi2HInf.Fill.r_boundary
import Phi2NB.Phi2HInf.Fill.r_cutoff
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M5Boundary
import Phi2NB.Phi2HInf.Proof.RDefs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Statements`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem phi2_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne) := by
  exact ⟨⟨Phi2cHInf, phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir⟩,
    phi2_hinf_boundary hH hZ1 hZ2 hZ3 hL hStir⟩

theorem phiR_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) := by
  obtain ⟨E, hE⟩ := exists_cutoff hH
  exact ⟨⟨PhiRcHInf E r, phiR_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE hr⟩,
    phiR_hinf_boundary hH hZ1 hZ2 hZ3 hL hStir hr⟩

end GoldbachBoundaries.Phi2HInf
