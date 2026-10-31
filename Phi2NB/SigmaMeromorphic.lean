import Phi2NB.Defs
import Phi2NB.Series
import Phi2NB.LogDerivZeta
import Phi2NB.ResidueAPI
import Phi2NB.ZetaRealNonvanishing

/-!
# Two facts about `-ζ'/ζ`

* Under RH, a zero of `ζ` with positive real part has real part `1/2` (`sigmaMero_re_eq_half`).
* *Bound on `Re w ≥ 2`* (`norm_negLogDerivZeta_le`): with `A = -ζ'/ζ` (`negLogDerivZeta`) and
  `C = ∑_m Λ(m) m^{-2}`, `|A(w)| ≤ C · 4 · 2^{-Re w}` for `Re w ≥ 2`, by comparing the von Mangoldt L-series termwise
  (`m^{-x} ≤ m^{-2} · 4 · 2^{-x}` for `m, x ≥ 2`).
-/

noncomputable section

open Complex Filter Topology Set Metric ArithmeticFunction LSeries
open scoped LSeries.notation

namespace GoldbachBoundaries

/-! ## RH puts zeros in the right half-plane on the critical line -/

/-- Under Mathlib's `RiemannHypothesis`, a zero with positive real part has real part `1/2`. (The same fact as
`sigmaFinite_re_eq_half`, for a zero given by `ζ s = 0` and `0 < Re s`.) -/
theorem sigmaMero_re_eq_half (hRH : RiemannHypothesis) {s : ℂ} (hz : riemannZeta s = 0)
    (hre : 0 < s.re) : s.re = 1 / 2 := by
  refine hRH s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hz

/-! ## A bound for `A = -ζ'/ζ` on `Re w ≥ 2` -/

/-- `C = ∑_m Λ(m) m^{-2}`. -/
def vmConst : ℝ := ∑' m : ℕ, Λ m * (m : ℝ) ^ (-(2 : ℝ))

lemma vmConst_nonneg : 0 ≤ vmConst :=
  tsum_nonneg fun _ => mul_nonneg vonMangoldt_nonneg (by positivity)

/-- `A(w)` is the von Mangoldt L-series on `Re w > 1`. -/
lemma negLogDerivZeta_eq_LSeries {w : ℂ} (hw : 1 < w.re) : negLogDerivZeta w = L ↗Λ w := by
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw, negLogDerivZeta, neg_div]

/-- For `m ≥ 2`, `x ≥ 2`: `m^{-x} ≤ m^{-2} · 4 · 2^{-x}`. -/
lemma rpow_neg_le_of_two_le {m : ℝ} (hm : 2 ≤ m) {x : ℝ} (hx : 2 ≤ x) :
    m ^ (-x) ≤ m ^ (-(2 : ℝ)) * (4 * (2 : ℝ) ^ (-x)) := by
  have hm0 : 0 < m := by linarith
  have h1 : m ^ (-x) = m ^ (-(2 : ℝ)) * m ^ (-(x - 2)) := by
    rw [← Real.rpow_add hm0]; ring_nf
  have h2 : m ^ (-(x - 2)) ≤ (2 : ℝ) ^ (-(x - 2)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hm (by linarith)
  have h3 : (2 : ℝ) ^ (-(x - 2)) = 4 * (2 : ℝ) ^ (-x) := by
    rw [show -(x - 2) = (2 : ℝ) + (-x) by ring, Real.rpow_add (by norm_num)]
    norm_num
  rw [h1, ← h3]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Tail bound.** For `Re w ≥ 2`, `‖A(w)‖ ≤ C · (4 · 2^{-Re w})`. -/
theorem norm_negLogDerivZeta_le {w : ℂ} (hw : 2 ≤ w.re) :
    ‖negLogDerivZeta w‖ ≤ vmConst * (4 * (2 : ℝ) ^ (-w.re)) := by
  rw [negLogDerivZeta_eq_LSeries (by linarith), LSeries]
  refine tsum_of_norm_bounded
    ((summable_vonMangoldt_rpow (by norm_num : (1 : ℝ) < 2)).hasSum.mul_right _) fun m => ?_
  rw [norm_term_eq]
  split_ifs with hm
  · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (by positivity)) (by positivity)
  · rcases lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this
      simp
    · have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h
      simp only [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg m), mul_assoc]
      exact mul_le_mul_of_nonneg_left (rpow_neg_le_of_two_le hm' hw) vonMangoldt_nonneg

end GoldbachBoundaries
