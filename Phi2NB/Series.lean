import Phi2NB.Defs

/-!
# Absolute convergence of the von Mangoldt series

`∑_m Λ(m) m^{-x}` converges for real `x > 1`.
-/

noncomputable section

open Complex Filter Topology Set ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GoldbachBoundaries

lemma summable_vonMangoldt_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun m : ℕ => Λ m * (m : ℝ) ^ (-x)) := by
  have h : Summable (term (fun n => (Λ n : ℂ)) (x : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hx)
  refine (summable_norm_iff.mpr h).congr fun m => ?_
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp only [norm_term_eq, hm, ↓reduceIte]
    rw [ofReal_re, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg m), div_eq_mul_inv]

end GoldbachBoundaries
