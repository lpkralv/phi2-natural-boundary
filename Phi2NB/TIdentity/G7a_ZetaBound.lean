import Phi2NB.TIdentity.Basic
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

/-!
# `ζ(σ + it) = O(|t|)` on `σ ≥ 1/2`, `|t| ≥ 2`

Uses PNT+'s Abel-summation continuation (`riemannZeta_eq_zetaAbelContinuationFormula`,
`norm_zetaAbelContinuationFormula_le`, file
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaAbelContinuation.lean`):
`‖ζ s‖ ≤ 1 + 1/‖s - 1‖ + ‖s‖ / Re s`. With `Re s ≥ 1/2` and `|Im s| ≥ 2`:
`1/‖s-1‖ ≤ 1/2` and `‖s‖/Re s ≤ (Re s + |Im s|)/Re s ≤ 1 + 2|Im s|`, so
`‖ζ s‖ ≤ 5/2 + 2|Im s| ≤ 4 |Im s|`.
-/

noncomputable section

open Complex

namespace GoldbachBoundaries

namespace TIdentity

/-- **`ζ(σ + it) = O(|t|)` on `σ ≥ 1/2`, `|t| ≥ 2`**, with constant `4` (unconditional; Titchmarsh §4.11 gives
`O(|t|^{1/2})`). Proof: PNT+'s Abel-summation continuation, as in the module docstring. -/
theorem norm_riemannZeta_le_mul_abs_im :
    ∃ C : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re → 2 ≤ |z.im| → ‖riemannZeta z‖ ≤ C * |z.im| := by
  refine ⟨4, fun z hre him => ?_⟩
  have hz1 : z ≠ 1 := by
    rintro rfl; simp at him; norm_num at him
  have hdom : z ∈ zetaAbelContinuationDomain :=
    mem_zetaAbelContinuationDomain_of_re hz1
      (by rw [zetaAbelContinuationReLower]; linarith)
  rw [riemannZeta_eq_zetaAbelContinuationFormula z hdom]
  refine (norm_zetaAbelContinuationFormula_le z hdom).trans ?_
  have hre0 : 0 < z.re := by linarith
  -- `1/‖z - 1‖ ≤ 1/2`
  have h1 : ‖1 / (z - 1)‖ ≤ 1 / 2 := by
    have : 2 ≤ ‖z - 1‖ := by
      have := Complex.abs_im_le_norm (z - 1)
      simp only [sub_im, one_im, sub_zero] at this
      linarith
    rw [norm_div, norm_one]
    exact (one_div_le_one_div_of_le (by norm_num) this)
  -- `‖z‖ / Re z ≤ 1 + 2 |Im z|`
  have h2 : ‖z‖ / z.re ≤ 1 + 2 * |z.im| := by
    rw [div_le_iff₀ hre0]
    have hn : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hre0] at hn
    nlinarith [abs_nonneg z.im]
  linarith
