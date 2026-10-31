import Phi2NB.Phi2.Proof.M3Radial
import Phi2NB.Phi2.Fill.norm_bKer
import Phi2NB.Phi2.Fill.norm_bKer_le
import Phi2NB.Phi2.Fill.bKer_cone
import Phi2NB.Phi2.Fill.sum_bKer_ne_zero
import Phi2NB.Phi2.Fill.pairAtom_eq_two_tsum
import Phi2NB.Phi2.Fill.Aidx_bin_le
import Phi2NB.Phi2.Fill.pairAtom_neg
import Phi2NB.Phi2.Fill.pairAtom_ne_zero_of_large
import Phi2NB.TBoundary

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The exceptional sums are finitely many** (no hypotheses): the sums `τ = γ + γ'` with `|τ| ≤ Y` and one ordinate of
modulus `≤ H`. The other ordinate then has modulus `≤ H + Y`, and only finitely many zeros have
`|γ| ≤ H + Y` (`M1.finite_zeros_abs_im_le`). -/
theorem finite_exceptional (H Y : ℝ) :
    {τ : ℝ | |τ| ≤ Y ∧ ∃ p : pairIdx τ, |(p.1.1 : ℂ).im| ≤ H ∨ |(p.1.2 : ℂ).im| ≤ H}.Finite := by
  let S : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ |H| + |Y|}
  have hS : S.Finite := M1.finite_zeros_abs_im_le (|H| + |Y|)
  refine ((hS.prod hS).image (fun p : ℂ × ℂ => p.1.im + p.2.im)).subset ?_
  rintro τ ⟨hτ, p, hp⟩
  have him : (p.1.1 : ℂ).im + (p.1.2 : ℂ).im = τ := by
    have := congrArg Complex.im p.2
    simpa using this
  have hbounds : |(p.1.1 : ℂ).im| ≤ |H| + |Y| ∧ |(p.1.2 : ℂ).im| ≤ |H| + |Y| := by
    rcases hp with h | h
    · constructor
      · linarith [le_abs_self H, abs_nonneg Y]
      · have he : (p.1.2 : ℂ).im = τ - (p.1.1 : ℂ).im := by linarith
        rw [he]
        have := abs_sub τ (p.1.1 : ℂ).im
        linarith [le_abs_self H, le_abs_self Y]
    · constructor
      · have he : (p.1.1 : ℂ).im = τ - (p.1.2 : ℂ).im := by linarith
        rw [he]
        have := abs_sub τ (p.1.2 : ℂ).im
        linarith [le_abs_self H, le_abs_self Y]
      · linarith [le_abs_self H, abs_nonneg Y]
  exact ⟨((p.1.1 : ℂ), (p.1.2 : ℂ)), ⟨⟨p.1.1.2, hbounds.1⟩, ⟨p.1.2.2, hbounds.2⟩⟩, him⟩

end GoldbachBoundaries.Phi2Proof
