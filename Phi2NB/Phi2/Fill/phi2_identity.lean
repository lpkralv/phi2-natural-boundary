import Phi2NB.Phi2.Fill.ACommon

/-! The `Φ₂` identity; the proof is `FillA.phi2_identity'` in `Phi2/Fill/ACommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **The `Φ₂` identity** (no RH): `Φ₂ = phi2Main + Hphi2` on `σ > 2`. Eliminate `m₁(s-1)` between the split of
`Γψ` at `s - 1` and the split of `ΓΦ₂` (both at `t = 1`), and divide by `Γ(s) = (s-1)Γ(s-1)`. -/
theorem phi2_identity {s : ℂ} (hs : 2 < s.re) : Phi2 s = phi2Main s + Hphi2 s :=
  FillA.phi2_identity' hs

end GoldbachBoundaries.Phi2Proof
