import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M1.Fill.finite_zeros_re_gt`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem finite_zeros_re_gt (δ : ℝ) (hδ : 0 < δ) :
    {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}.Finite := by
  obtain ⟨t, ht⟩ := exists_binfFam_lt hδ
  refine (finite_zeros_abs_im_le t).subset ?_
  rintro ρ ⟨hρ, hre⟩
  refine ⟨hρ, ?_⟩
  by_contra h
  push Not at h
  have := re_le_binfFam hρ h.le
  linarith

end GoldbachBoundaries.Paper2.M1
