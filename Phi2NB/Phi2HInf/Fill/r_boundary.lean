import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.phi2_hinf_continuation
import Phi2NB.Phi2HInf.Fill.r_cutoff
import Phi2NB.Phi2HInf.Fill.r_finite_mellin
import Phi2NB.Phi2HInf.Fill.r_identity
import Phi2NB.Phi2HInf.Fill.r_remainder
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M5Boundary
import Phi2NB.Phi2HInf.Proof.RDefs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.r_boundary`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof PhiRProof

lemma meromorphicOn_phiRRestHInf (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros}
    (hE : ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (phiRRestHInf E r) (halfPlane (rAbscissa r)) := by
  intro s hs
  have hh := (differentiableOn_Hr hH hZ1 hZ2 hZ3 hStir hE hr).analyticAt
    ((isOpen_halfPlane _).mem_nhds hs)
  exact (meromorphicOn_Mr_hinf E hr s (mem_univ _)).add
    (hh.meromorphicAt.mul (analyticAt_inv_Gamma s).meromorphicAt)

theorem phiR_hinf_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros}
    (hE : ∀ ρ : NontrivialZeros, ρ ∈ E ↔ rCutoff < (ρ : ℂ).re) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (PhiRcHInf E r) (halfPlane ((r : ℝ) - 1)) ∧
      EqOn (PhiRcHInf E r) (PhiR r) (halfPlane r) := by
  refine ⟨?_, phiR_reg_identity hH hZ1 hZ2 hZ3 hStir hE hr⟩
  intro s hs
  have hs' : (r : ℝ) - 1 < s.re := hs
  have hP2 : MeromorphicAt (fun z : ℂ => Phi2cHInf (z - r + 2)) s := by
    apply MeromorphicAt.comp_analyticAt (f := Phi2cHInf) (g := fun z : ℂ => z - r + 2) _ (by fun_prop)
    apply (phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir).1
    show 1 < (s - r + 2).re
    simp; linarith
  have hR := meromorphicOn_phiRRestHInf hH hZ1 hZ2 hZ3 hStir hE hr s
    (show rAbscissa r < s.re by
      dsimp [rAbscissa]
      linarith [(rCutoff_bounds hH hZ1).2.2.1])
  exact ((analyticAt_phiRCoef (by linarith)).meromorphicAt.mul hP2).add hR

theorem phiR_hinf_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r) :
    IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)) := by
  obtain ⟨E, hE⟩ := exists_cutoff hH
  obtain ⟨hmero, heq⟩ := phiR_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE hr
  intro z₀ hz₀
  have hz₀' : z₀.re = (r : ℝ) - 1 := hz₀
  let c : ℝ := (r : ℝ) - 2
  have hagree : F =ᶠ[codiscreteWithin (halfPlane ((r : ℝ) - 1))]
      fun s => phiRRestHInf E r s + phiRCoef r s * Phi2cHInf (s - (c : ℂ)) := by
    have h1 : F =ᶠ[codiscreteWithin (halfPlane ((r : ℝ) - 1))] PhiRcHInf E r :=
      eventuallyEq_codiscreteWithin_of_nhdsNE fun a ha =>
        eventuallyEq_nhdsNE_of_agree_halfPlane (by linarith) hF hmero heq hFΦ ha
    filter_upwards [h1] with s hs
    rw [hs, PhiRcHInf]
    have ht : s - (r : ℂ) + 2 = s - (c : ℂ) := by dsimp [c]; push_cast; ring
    rw [ht, add_comm]
  have hW : z₀ ∈ halfPlane (rAbscissa r) := by
    show rAbscissa r < z₀.re
    dsimp [rAbscissa]
    linarith [(rCutoff_bounds hH hZ1).2.2.1]
  have hcoef {s : ℂ} (hs : s ∈ halfPlane (rAbscissa r)) : (r : ℝ) - 2 < s.re := by
    have hs' : (r : ℝ) - 1 - rMargin < s.re := hs
    linarith [(rCutoff_bounds hH hZ1).2.2.2]
  rw [noMeromorphicExtensionAt_iff_of_eq_add_mul (isOpen_halfPlane _) hW
    (meromorphicOn_phiRRestHInf hH hZ1 hZ2 hZ3 hStir hE hr)
    (fun s hs => analyticAt_phiRCoef (hcoef hs))
    (fun s hs => phiRCoef_ne_zero hr (hcoef hs)) hagree]
  have hpre : (fun s : ℂ => s - (c : ℂ)) ⁻¹' HH = halfPlane ((r : ℝ) - 1) := by
    rw [preimage_sub_halfPlane]
    dsimp [c]
    congr 1
    ring
  have htrans := noMeromorphicExtensionAt_comp_sub_iff (H := Phi2cHInf) (U := HH)
    (z₀ := z₀ - (c : ℂ)) (c := (c : ℂ))
  rw [sub_add_cancel, hpre] at htrans
  apply htrans.mpr
  obtain ⟨hm2, he2⟩ := phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir
  have hb2 := phi2_hinf_boundary hH hZ1 hZ2 hZ3 hL hStir Phi2cHInf hm2
    (by filter_upwards [self_mem_codiscreteWithin (halfPlane 2)] with s hs using he2 hs)
  apply hb2
  show (z₀ - (c : ℂ)).re = 1
  simp only [sub_re, ofReal_re]
  dsimp [c]
  linarith

end GoldbachBoundaries.Phi2HInf
