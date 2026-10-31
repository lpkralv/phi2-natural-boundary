import Phi2NB.Phi2.Proof.M3Radial

/-! The modulus of `b_τ`: `norm_bKer`. `Γ(1/2 - ix) = conj Γ(1/2 + ix)` (`Complex.Gamma_conj`) and the
reflection formula `Γ(z)Γ(1-z) = π/sin πz` at `z = 1/2 + ix` (`sin(π/2 + iπx) = cosh πx`) give
`|Γ(1/2 + ix)|² = π/cosh πx`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma Gamma_half_sub_eq_conj (x : ℝ) :
    Gamma (1 / 2 - (x : ℂ) * I) = conj (Gamma (1 / 2 + (x : ℂ) * I)) := by
  rw [← Complex.Gamma_conj]
  congr 1
  apply Complex.ext <;> simp

/-- `|Γ(1/2 + ix)|² = π/cosh πx`. -/
private lemma norm_Gamma_half_sq (x : ℝ) :
    ‖Gamma (1 / 2 + (x : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * x) := by
  have h2 := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + (x : ℂ) * I)
  have h1 : (1 : ℂ) - (1 / 2 + (x : ℂ) * I) = 1 / 2 - (x : ℂ) * I := by ring
  rw [h1, Gamma_half_sub_eq_conj, Complex.mul_conj] at h2
  have hs : Complex.sin (Real.pi * (1 / 2 + (x : ℂ) * I)) = Real.cosh (Real.pi * x) := by
    have : (Real.pi : ℂ) * (1 / 2 + (x : ℂ) * I) = (Real.pi : ℂ) / 2 + ((Real.pi * x : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
      Complex.ofReal_cosh]
    ring
  rw [hs, Complex.normSq_eq_norm_sq] at h2
  exact_mod_cast h2

/-- **The modulus of `b_τ`** (no hypotheses): `|b_τ(u)| = π/√(cosh(πu) cosh(π(u+τ)))`, from Mathlib's
`Complex.Gamma_mul_Gamma_one_sub` and `Complex.Gamma_conj`. -/
theorem norm_bKer (τ u : ℝ) :
    ‖bKer τ u‖ = Real.pi / Real.sqrt (Real.cosh (Real.pi * u) * Real.cosh (Real.pi * (u + τ))) := by
  have hA : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  have hB : 0 < Real.cosh (Real.pi * (u + τ)) := Real.cosh_pos _
  have hsq : ‖bKer τ u‖ ^ 2 =
      (Real.pi / Real.sqrt (Real.cosh (Real.pi * u) * Real.cosh (Real.pi * (u + τ)))) ^ 2 := by
    rw [bKer, norm_mul, mul_pow, Gamma_half_sub_eq_conj, Complex.norm_conj, norm_Gamma_half_sq,
      norm_Gamma_half_sq, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

end GoldbachBoundaries.Phi2Proof
