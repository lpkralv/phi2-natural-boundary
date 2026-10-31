import Phi2NB.Phi2.Fill.ACommon

/-! `hL(t) = O(t^{-b})` under RH; the proofs are `FillA.continuousOn_hL'` and `FillA.norm_hL_le'` in `Phi2/Fill/ACommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **`hL(t) = O(t^{-b})`** (RH), `1/2 < b < 1`, all `t > 0`, and `hL` is continuous on `(0, ∞)`. Mellin inversion
(`FL_eq_verticalIntegral'`), the shift of the line to `Re w = b` past the pole at `1`
(`verticalIntegral'_kernelL_shift`), and the trivial estimate of the integral on `Re w = b`, where `Γψ` is
integrable under RH. -/
theorem norm_hL_le (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1) :
    ContinuousOn hL (Ioi 0) ∧ ∃ C : ℝ, ∀ t : ℝ, 0 < t → |hL t| ≤ C * t ^ (-b) :=
  ⟨FillA.continuousOn_hL', FillA.norm_hL_le' hRH hb hb1⟩

end GoldbachBoundaries.Phi2Proof
