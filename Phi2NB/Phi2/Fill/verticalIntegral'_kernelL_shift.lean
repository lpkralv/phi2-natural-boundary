import Phi2NB.Phi2.Fill.ACommon

/-! The first contour shift; the proof is `FillA.verticalIntegral'_kernelL_shift'` in `Phi2/Fill/ACommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **First contour shift** (RH): for `1/2 < b < 1 < c` and `t > 0`, moving the line from `c` to `b` crosses only the
pole `w = 1`, residue `1/t`. Uses the bound `TIdentity.norm_negLogDerivZeta_le_log` for `ψ` on vertical lines (RH)
and `hasResidue_negLogDerivZeta_one`. -/
theorem verticalIntegral'_kernelL_shift (hRH : RiemannHypothesis) {b c t : ℝ} (hb : 1 / 2 < b)
    (hb1 : b < 1) (hc : 1 < c) (ht : 0 < t) :
    VerticalIntegral' (kernelL t) c = 1 / (t : ℂ) + VerticalIntegral' (kernelL t) b :=
  FillA.verticalIntegral'_kernelL_shift' hRH hb hb1 hc ht

end GoldbachBoundaries.Phi2Proof
