import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.Binf_le_Bsup_le_one
import Phi2NB.HInfSupport.Paper2.M1.Fill.Bsup_attained
import Phi2NB.HInfSupport.Paper2.M1.Fill.Bsup_lt_one_of_Hinf
import Phi2NB.HInfSupport.Paper2.M1.Fill.finite_zeros_re_gt
import Phi2NB.HInfSupport.Paper2.M1.Fill.half_le_Binf

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M1.Skeleton`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem lem_B_i_proof (hZ1 : Z1) :
    1 / 2 ≤ Binf ∧ Binf ≤ Bsup ∧ Bsup ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}.Finite := by
  exact ⟨half_le_Binf hZ1, Binf_le_Bsup_le_one.1, Binf_le_Bsup_le_one.2,
    fun δ hδ => finite_zeros_re_gt δ hδ⟩

theorem lem_B_iii_proof (hH : Hinf) : Bsup < 1 := by
  exact Bsup_lt_one_of_Hinf hH

theorem lem_B_iv_proof (hZ1 : Z1) (h : Binf < Bsup) :
    1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty := by
  obtain ⟨h1, h2, h3⟩ := Bsup_attained h
  exact ⟨by linarith [half_le_Binf hZ1], h1, h2, h3⟩

end GoldbachBoundaries.Paper2.M1
