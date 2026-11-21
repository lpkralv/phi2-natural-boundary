import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.ZetaNoZeroIoo`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Set

namespace GoldbachBoundaries.Phi2HInf

def ZetaNoZeroIoo : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0

theorem zetaNoZeroIoo : ZetaNoZeroIoo := fun _ h0 h1 => riemannZeta_ne_zero_of_mem_Ioo ⟨h0, h1⟩

end GoldbachBoundaries.Phi2HInf
