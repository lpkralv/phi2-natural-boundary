import Phi2NB.Phi2.Proof.M2Explicit

/-!
# Absolute summability over pairs of zeros

`summable_norm_pair` is used by `integral_zeroSum_sq`, `tendsto_eta_cauchyT` and `pairAtom_eq_two_tsum`, so it sits
here, before them; `M3Radial` imports those files.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`∑_{(ρ,ρ')} |a_ρ a_ρ'| < ∞`** (RH, (RiemannVonMangoldt)): the product of two absolutely summable families, from
`summable_norm_zeroCoef` and Mathlib's `Summable.mul_norm`. -/
theorem summable_norm_pair (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) :
    Summable (fun p : NontrivialZeros × NontrivialZeros => ‖zeroCoef p.1 * zeroCoef p.2‖) :=
  Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef (ρ : ℂ))
    (g := fun ρ : NontrivialZeros => zeroCoef (ρ : ℂ)) (summable_norm_zeroCoef hRH hRvM)
    (summable_norm_zeroCoef hRH hRvM)

end GoldbachBoundaries.Phi2Proof
