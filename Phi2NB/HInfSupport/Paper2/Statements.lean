import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Skeleton
import Phi2NB.HInfSupport.Statements

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.Statements`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

theorem hinf_of_RH (hRH : RiemannHypothesis) : Hinf := by
  intro δ hδ
  convert Set.finite_empty
  ext ρ
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hρ
  rw [re_eq_half_of_mem_nontrivialZeros hRH hρ]
  linarith

theorem lem_B_i (hZ1 : Z1) :
    1 / 2 ≤ Binf ∧ Binf ≤ Bsup ∧ Bsup ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}.Finite := by
  exact M1.lem_B_i_proof hZ1

theorem lem_B_iii (hH : Hinf) : Bsup < 1 := by
  exact M1.lem_B_iii_proof hH

end GoldbachBoundaries.Paper2
