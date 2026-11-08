import Phi2NB.Phi2.Defs
import Phi2NB.Paper2.Defs

/-!
# Comparison with a stronger form of the premises

The four definitions in `PhiRSource` below state a stronger form of the premises: `Z2`, `Z3`, `ZLittlewood` and an
independent copy of `Phi2`. `Nzero` is the same finite sum as in the release. The release's `RiemannVonMangoldt` is
only the second conjunct of `Z2`; it does not include the asymptotic for `Nzero`. The extension to `Φ_r` (Section 7
of the paper) uses that local count through the existing `Phi2` proofs. It never constructs the stronger `Z2` from
the weaker premise. The other comparisons are definitional. The stronger form is the one the extension was
first written against; no theorem of the release uses this file.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.PhiRSource

open GoldbachBoundaries.Paper2

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

def Phi2 (s : ℂ) : ℂ :=
  ∑' mn : ℕ × ℕ, ((ArithmeticFunction.vonMangoldt mn.1 : ℝ) : ℂ) *
    ((ArithmeticFunction.vonMangoldt mn.2 : ℝ) : ℂ) * (((mn.1 + mn.2 : ℕ) : ℂ)) ^ (-s)

/-- The release keeps exactly the local-count conjunct of the stronger premise `Z2`. -/
theorem riemannVonMangoldt_of_Z2 (h : Z2) : RiemannVonMangoldt := h.2

/-- The local logarithmic-derivative premises have identical bodies. -/
theorem Z3_iff_logDerivZetaLocal : Z3 ↔ LogDerivZetaLocal := Iff.rfl

/-- Littlewood's gap premises have identical bodies. -/
theorem ZLittlewood_iff_littlewoodGap : ZLittlewood ↔ LittlewoodGap := Iff.rfl

/-- Both definitions give the same ordered-pair series, including its junk values. -/
theorem Phi2_eq_release : Phi2 = GoldbachBoundaries.Phi2 := rfl

end GoldbachBoundaries.PhiRSource
