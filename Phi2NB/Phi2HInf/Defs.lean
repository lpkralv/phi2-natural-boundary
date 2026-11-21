import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Defs`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Phi2HInf

def StirlingStrip : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∃ C T₀ : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, x₁ ≤ z.re → z.re ≤ x₂ → T₀ ≤ |z.im| →
      ‖Complex.Gamma z -
          Complex.exp ((z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * (Real.pi : ℂ)))‖ ≤
        C / |z.im| *
          ‖Complex.exp ((z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * (Real.pi : ℂ)))‖

end GoldbachBoundaries.Phi2HInf
