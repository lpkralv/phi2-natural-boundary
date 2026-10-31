import Phi2NB.Phi2.Fill.ACommon

/-! Mellin inversion for `FL`; the proof is `FillA.FL_eq_verticalIntegral'_aux` in `Phi2/Fill/ACommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **Mellin inversion for `FL`** (no RH): `FL(t) = (2πi)⁻¹ ∫_{(c)} t^{-w} Γ(w) ψ(w) dw` for `c > 1`, `t > 0`. -/
theorem FL_eq_verticalIntegral' {c t : ℝ} (hc : 1 < c) (ht : 0 < t) :
    (FL t : ℂ) = VerticalIntegral' (kernelL t) c :=
  FillA.FL_eq_verticalIntegral'_aux hc ht

end GoldbachBoundaries.Phi2Proof
