import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M1.Fill.Bsup_lt_one_of_Hinf`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem Bsup_lt_one_of_Hinf (hH : Hinf) : Bsup < 1 := by
  set S := {ρ | ρ ∈ NontrivialZeros ∧ 1 / 2 + 1 / 4 < ρ.re} with hSdef
  have hS : S.Finite := hH (1 / 4) (by norm_num)
  set b := max (3 / 4 : ℝ) (sSup (re '' S)) with hbdef
  have hb : b < 1 := by
    rcases (re '' S).eq_empty_or_nonempty with h | h
    · rw [hbdef, h, Real.sSup_empty]
      norm_num
    · obtain ⟨ρ, hρ, hρe⟩ := h.csSup_mem (hS.image _)
      refine max_lt (by norm_num) ?_
      rw [← hρe]
      exact hρ.1.2.2
  obtain ⟨ρ₀, hρ₀⟩ := nontrivialZeros_nonempty
  refine lt_of_le_of_lt (csSup_le ⟨_, ρ₀, hρ₀, rfl⟩ ?_) hb
  rintro _ ⟨ρ, hρ, rfl⟩
  by_cases h : 1 / 2 + 1 / 4 < ρ.re
  · exact (le_csSup (hS.image _).bddAbove ⟨ρ, ⟨hρ, h⟩, rfl⟩).trans (le_max_right _ _)
  · push Not at h
    exact le_trans (by linarith) (le_max_left _ _)

end GoldbachBoundaries.Paper2.M1
