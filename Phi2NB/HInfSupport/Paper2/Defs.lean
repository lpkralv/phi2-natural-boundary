import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.Defs`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

def Bsup : ℝ := sSup (re '' NontrivialZeros)

def Binf : ℝ := ⨅ t : ℝ, sSup (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|})

def Z1 : Prop :=
  ∀ ρ ∈ NontrivialZeros,
    (conj ρ ∈ NontrivialZeros ∧ zetaMult (conj ρ) = zetaMult ρ) ∧
      (1 - conj ρ ∈ NontrivialZeros ∧ zetaMult (1 - conj ρ) = zetaMult ρ)

def Z2 : Prop :=
  (∃ C : ℝ, ∀ᶠ t in atTop,
      |Nzero t - (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi))| ≤
        C * Real.log t) ∧
    ∃ C₁ : ℝ, ∀ t : ℝ, 0 ≤ t → Nzero (t + 1) - Nzero t ≤ C₁ * Real.log (t + 3)

def Z3 : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 →
    ‖deriv riemannZeta z / riemannZeta z -
        ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1}, (zetaMult ρ : ℂ) / (z - ρ)‖ ≤
      C * Real.log |z.im|

def ZLittlewood : Prop :=
  ∃ a : ℝ, ∀ᶠ t in atTop, ∃ ρ ∈ NontrivialZeros,
    |ρ.im - t| < a / Real.log (Real.log (Real.log t))

namespace Aff

end Aff

end GoldbachBoundaries.Paper2
