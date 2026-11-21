import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.critical_basic
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.differentiableOn_criticalC`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem differentiableOn_criticalC (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    DifferentiableOn ℂ criticalC HH := by
  intro s hs
  change 1 < s.re at hs
  let d := (s.re - 1) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let F (p : CriticalZero × CriticalZero) (z : ℂ) :=
    zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2) /
      (z - criticalVal p.1 - criticalVal p.2)
  have hden (p : CriticalZero × CriticalZero) (z : ℂ) (hz : z ∈ halfPlane (1 + d)) :
      d ≤ ‖z - criticalVal p.1 - criticalVal p.2‖ := by
    have hr : (z - criticalVal p.1 - criticalVal p.2).re = z.re - 1 := by
      simp only [sub_re]
      rw [show (criticalVal p.1).re = 1 / 2 from p.1.2,
        show (criticalVal p.2).re = 1 / 2 from p.2.2]
      ring
    have hh := Complex.re_le_norm (z - criticalVal p.1 - criticalVal p.2)
    rw [hr] at hh
    change 1 + d < z.re at hz
    linarith
  have hdiff : DifferentiableOn ℂ (fun z => ∑' p, F p z) (halfPlane (1 + d)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((summable_norm_critical_pair hZ1 hZ2 hStir).div_const d)
    · intro p z hz
      exact (differentiableWithinAt_const _).div
        ((differentiableWithinAt_id.sub_const _).sub_const _)
        (norm_pos_iff.mp (hd.trans_le (hden p z hz)))
    · exact isOpen_halfPlane _
    · intro p z hz
      dsimp [F]
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hden p z hz)
  exact (hdiff.differentiableAt ((isOpen_halfPlane _).mem_nhds
    (show s ∈ halfPlane (1 + d) by change 1 + d < s.re; dsimp [d]; linarith))).differentiableWithinAt

end GoldbachBoundaries.Phi2HInf
