import Phi2NB.Phi2.Fill.ACommon

/-! `e₁` and `E₂` are entire; the proofs are `FillA.differentiable_e1L'` and `FillA.differentiable_E2L'` in `Phi2/Fill/ACommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- `e₁` and `E₂` are entire (`FL` decays like `e^{-t}`, `FL_continuousOn_and_le_exp`). -/
theorem differentiable_e1L_E2L : Differentiable ℂ e1L ∧ Differentiable ℂ E2L :=
  ⟨FillA.differentiable_e1L', FillA.differentiable_E2L'⟩

end GoldbachBoundaries.Phi2Proof
