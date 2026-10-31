import Phi2NB.Phi2.Proof.M3Base

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`|∑_ρ a_ρ t^{-ρ}| ≤ S t^{-1/2}`** (RH, (RiemannVonMangoldt)), with the series absolutely convergent for every `t > 0`
(`|t^{-ρ}| = t^{-1/2}` on the critical line). Uses: `summable_norm_zeroCoef`, `sigmaFinite_re_eq_half`. -/
theorem norm_zeroSum_le (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t : ℝ, 0 < t →
      Summable (fun ρ : NontrivialZeros => zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))) ∧
        ‖zeroSum t‖ ≤ S * t ^ (-(1 / 2 : ℝ)) := by
  have ha := summable_norm_zeroCoef hRH hRvM
  refine ⟨∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro t ht
  have hn (ρ : NontrivialZeros) :
      ‖zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))‖ = ‖zeroCoef ρ‖ * t ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, neg_re,
      sigmaFinite_re_eq_half hRH ρ.2]
  have habs : Summable (fun ρ : NontrivialZeros =>
      ‖zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))‖) := by
    simpa only [hn] using ha.mul_right (t ^ (-(1 / 2 : ℝ)))
  refine ⟨habs.of_norm, ?_⟩
  calc ‖zeroSum t‖ ≤ ∑' ρ : NontrivialZeros,
        ‖zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))‖ := norm_tsum_le_tsum_norm habs
    _ = _ := by simp only [hn, tsum_mul_right]

end GoldbachBoundaries.Phi2Proof
