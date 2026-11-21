import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M1.Fill.half_le_Binf`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem half_le_Binf (hZ1 : Z1) : 1 / 2 ≤ Binf := by
  rw [Binf_eq_iInf]
  refine le_ciInf fun t => ?_
  obtain ⟨ρ, hρ, h⟩ := exists_nontrivialZero_im_gt |t|
  have ht : t ≤ |ρ.im| := (le_abs_self t).trans (h.le.trans (le_abs_self _))
  have h1 := (hZ1 ρ hρ).2.1
  have ht' : t ≤ |(1 - conj ρ).im| := by simpa using ht
  rcases le_total (1 / 2) ρ.re with hr | hr
  · exact hr.trans (re_le_binfFam hρ ht)
  · refine le_trans ?_ (re_le_binfFam h1 ht')
    simp only [sub_re, one_re, conj_re]
    linarith

end GoldbachBoundaries.Paper2.M1
