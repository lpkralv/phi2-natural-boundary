import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2.Proof.M2Explicit`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem Z1_of_RH (hRH : RiemannHypothesis) : Z1 := by
  intro ρ hρ
  have hc : conj ρ ∈ NontrivialZeros := conj_mem_nontrivialZeros hρ
  have hre : ρ.re = 1 / 2 := sigmaFinite_re_eq_half hRH hρ
  have h1 : 1 - conj ρ = ρ := by
    apply Complex.ext
    · simp [hre]; norm_num
    · simp
  refine ⟨⟨hc, zetaMult_conj hρ⟩, ?_, ?_⟩
  · rw [h1]; exact hρ
  · rw [h1]

end GoldbachBoundaries.Phi2Proof
