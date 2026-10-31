import Phi2NB.TIdentity.G7c_LogDerivZetaBound

/-!
# `-ζ'/ζ` on `Re w ≥ σ₀ > 1`

`‖A(w)‖ ≤ ∑_m ‖Λ(m) m^{-σ₀}‖` for `A = -ζ'/ζ` and `Re w ≥ σ₀ > 1`, by termwise comparison of the absolutely
convergent L-series.
-/

noncomputable section

open Complex Set Metric ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GoldbachBoundaries

namespace TIdentity

/-- `‖A(w)‖ ≤ ∑_m ‖Λ(m) m^{-σ₀}‖` on `Re w ≥ σ₀ > 1`. -/
lemma norm_negLogDerivZeta_le_of_re {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {w : ℂ} (hw : σ₀ ≤ w.re) :
    ‖negLogDerivZeta w‖ ≤ ∑' n, ‖term ↗Λ (σ₀ : ℂ) n‖ := by
  rw [negLogDerivZeta_eq_LSeries (by linarith), LSeries]
  have hs : LSeriesSummable ↗Λ (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ₀)
  exact tsum_of_norm_bounded (summable_norm_iff.mpr hs).hasSum
    (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hw) n)

end TIdentity
end GoldbachBoundaries
