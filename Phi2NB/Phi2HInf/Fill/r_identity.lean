import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.r_cutoff
import Phi2NB.Phi2HInf.Fill.r_finite_mellin
import Phi2NB.Phi2HInf.Fill.r_remainder
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M1Regularization
import Phi2NB.Phi2HInf.Proof.RDefs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.r_identity`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof PhiRProof

theorem phiR_reg_identity (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros}
    (hE : ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re) {r : ℕ} (hr : 2 ≤ r) :
    EqOn (PhiRcHInf E r) (PhiR r) (halfPlane r) := by
  intro s hs
  have hs' : (r : ℝ) < s.re := hs
  obtain ⟨U, -, hU⟩ := norm_Rr_le hH hZ1 hZ2 hZ3 hStir hE hr
  have hmargin := (rCutoff_bounds hH hZ1).2.2.1
  have hR := C_integrableOn_mellin (RrFun_meas E r) hU (s := s)
    (by dsimp [rAbscissa]; linarith)
  have hP := mellin_Pr E hr hs'
  have hJ : JR r s = Pr E r s + Hr E r s := by
    unfold JR
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
      rw [QR_eq_Pr_add_Rr E hr hx.1, add_mul])]
    rw [integral_add hP.1 hR, ← hP.2]
    rfl
  have hsplit := Gamma_mul_PhiR_split hr hs'
  have hw : 2 < (s - r + 2).re := by simp; linarith
  have h2 := phi2_reg_identity hZ1 hZ2 hZ3 hStir hw
  rw [← h2, KR, hJ] at hsplit
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    linarith)
  have heq : PhiR r s = (Gamma s)⁻¹ * (Gamma s * PhiR r s) := by field_simp
  rw [heq, hsplit]
  unfold PhiRcHInf phiRRestHInf Mr phiRCoef
  ring

end GoldbachBoundaries.Phi2HInf
