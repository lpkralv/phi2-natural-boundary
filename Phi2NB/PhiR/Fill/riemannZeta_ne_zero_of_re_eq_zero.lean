import Phi2NB.PhiR.Fill.BCommon

/-!
# `riemannZeta_ne_zero_of_re_eq_zero` (step M5)

`ζ(iτ) ≠ 0` for real `τ ≠ 0`, no RH. The proof is `fillB_zeta_ne_zero_imI` in `BCommon.lean` (Mathlib's functional
equation `riemannZeta_one_sub` at `s = 1 - iτ`), kept there because `analyticAt_phiRRest_line` and
`tendsto_eta_Phi2c` use it too.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillB

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- **`ζ(iτ) ≠ 0` for real `τ ≠ 0`** (no RH). Statement of `PhiRProof.riemannZeta_ne_zero_of_re_eq_zero`,
verbatim. -/
theorem riemannZeta_ne_zero_of_re_eq_zero' {τ : ℝ} (hτ : τ ≠ 0) : riemannZeta (τ * I) ≠ 0 :=
  fillB_zeta_ne_zero_imI hτ

end GoldbachBoundaries.PhiRProof.FillB
