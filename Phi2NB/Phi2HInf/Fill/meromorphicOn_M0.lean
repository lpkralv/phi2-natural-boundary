import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.cauchy_meromorphic
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.meromorphicOn_M0`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem meromorphicOn_M0 (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    MeromorphicOn M0 univ := by
  intro s _
  have hL := meromorphicOn_L hZ1 hZ2 hStir s (mem_univ _)
  have hΓ := (differentiable_one_div_Gamma.analyticAt s).meromorphicAt
  have hm := (Phi2Proof.meromorphicOn_phi2Main s (mem_univ _)).sub
    (((analyticAt_const.meromorphicAt : MeromorphicAt (fun _ : ℂ => 2 * c0) s).mul hL).mul hΓ)
  convert hm using 1
  ext z
  simp only [M0, Pi.sub_apply, Pi.mul_apply, div_eq_mul_inv]

end GoldbachBoundaries.Phi2HInf
