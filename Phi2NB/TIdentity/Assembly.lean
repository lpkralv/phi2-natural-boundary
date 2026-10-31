import Phi2NB.TIdentity.G7d_QcontBound
import Phi2NB.TIdentity.G8d_ContourShift
import Phi2NB.TIdentity.Basic
import Phi2NB.TIdentity.G9e_SplitQ
import Phi2NB.TIdentity.G9g_HolomorphyIoc
import Phi2NB.TIdentity.G9h_HolomorphyIoi

/-!
# Two residue facts

The residue of a product of a function with a residue and a function continuous at the point, and the residue
`1/Γ(2) = 1` of `1/(Γ(s)(s - 2))` at `s = 2`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

end TIdentity

open TIdentity

/-- Product of a function with a residue and a function continuous at the point. -/
theorem HasResidue.mul_continuousAt' {f g : ℂ → ℂ} {a c : ℂ} (hf : HasResidue f a c)
    (hg : ContinuousAt g a) : HasResidue (fun z => f z * g z) a (c * g a) := by
  unfold HasResidue at *
  exact (hf.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)).congr fun z => by ring

/-- The residue of `1/(Γ(s)(s - 2))` at `s = 2` is `1/Γ(2) = 1`. -/
theorem hasResidue_one_div_Gamma_mul_sub_two :
    HasResidue (fun s => 1 / (Gamma s * (s - 2))) 2 1 := by
  have hG2 : Gamma 2 = 1 := by
    have h := Gamma_add_one 1 one_ne_zero
    rw [Gamma_one, mul_one, one_add_one_eq_two] at h
    exact h
  have hc : Tendsto (fun s => (Gamma s)⁻¹) (𝓝[≠] (2 : ℂ)) (𝓝 1) := by
    have := (differentiable_one_div_Gamma.continuous.tendsto (2 : ℂ)).mono_left
      (nhdsWithin_le_nhds (s := {(2 : ℂ)}ᶜ))
    simpa [hG2] using this
  unfold HasResidue
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 2 ≠ 0 := sub_ne_zero.mpr hs
  rw [one_div, mul_inv, ← mul_assoc, mul_comm (s - 2), mul_assoc, mul_inv_cancel₀ hs', mul_one]

end GoldbachBoundaries
