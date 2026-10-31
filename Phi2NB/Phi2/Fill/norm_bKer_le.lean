import Phi2NB.Phi2.Proof.M3Radial
import Phi2NB.Phi2.Fill.norm_bKer

/-! Decay of `|b_τ|`: `norm_bKer_le`, from `norm_bKer`: for `0 ≤ a ≤ b`,
`cosh a ≤ e^a = e^b e^{-(b-a)} ≤ 2 e^{-(b-a)} cosh b`, applied at `a = πu₀, b = πu` and `a = π(u₀+τ), b = π(u+τ)`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `cosh a ≤ 2 e^{-(b-a)} cosh b` for `0 ≤ a ≤ b`. -/
private lemma cosh_le_two_exp_mul_cosh {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) :
    Real.cosh a ≤ 2 * Real.exp (-(b - a)) * Real.cosh b := by
  have h1 : Real.cosh a ≤ Real.exp a := by
    rw [Real.cosh_eq]
    have : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h2 : Real.exp b ≤ 2 * Real.cosh b := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-b)]
  have h3 : Real.exp a = Real.exp (-(b - a)) * Real.exp b := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.cosh a ≤ Real.exp (-(b - a)) * Real.exp b := h3 ▸ h1
    _ ≤ Real.exp (-(b - a)) * (2 * Real.cosh b) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring

/-- **Decay of the modulus**: for `0 ≤ τ`, `0 ≤ u₀ ≤ u`, `|b_τ(u)| ≤ 2 e^{-π(u-u₀)} |b_τ(u₀)|`
(from `cosh a ≤ e^a`, `cosh b ≥ e^b/2` for `0 ≤ a ≤ b`). Uses `norm_bKer`. -/
theorem norm_bKer_le {τ u₀ u : ℝ} (hτ : 0 ≤ τ) (hu₀ : 0 ≤ u₀) (h : u₀ ≤ u) :
    ‖bKer τ u‖ ≤ 2 * Real.exp (-(Real.pi * (u - u₀))) * ‖bKer τ u₀‖ := by
  rw [norm_bKer, norm_bKer]
  set A := Real.cosh (Real.pi * u)
  set B := Real.cosh (Real.pi * (u + τ))
  set A₀ := Real.cosh (Real.pi * u₀)
  set B₀ := Real.cosh (Real.pi * (u₀ + τ))
  set E := Real.exp (-(Real.pi * (u - u₀)))
  have hA : 0 < A := Real.cosh_pos _
  have hB : 0 < B := Real.cosh_pos _
  have hA₀ : 0 < A₀ := Real.cosh_pos _
  have hB₀ : 0 < B₀ := Real.cosh_pos _
  have hE : 0 < E := Real.exp_pos _
  have hpi := Real.pi_pos
  have h1 : A₀ ≤ 2 * E * A := by
    have := cosh_le_two_exp_mul_cosh (a := Real.pi * u₀) (b := Real.pi * u) (by positivity)
      (mul_le_mul_of_nonneg_left h hpi.le)
    have e : Real.pi * u - Real.pi * u₀ = Real.pi * (u - u₀) := by ring
    rwa [e] at this
  have h2 : B₀ ≤ 2 * E * B := by
    have := cosh_le_two_exp_mul_cosh (a := Real.pi * (u₀ + τ)) (b := Real.pi * (u + τ)) (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) hpi.le)
    have e : Real.pi * (u + τ) - Real.pi * (u₀ + τ) = Real.pi * (u - u₀) := by ring
    rwa [e] at this
  have hprod : A₀ * B₀ ≤ (2 * E) ^ 2 * (A * B) := by
    calc A₀ * B₀ ≤ (2 * E * A) * (2 * E * B) := mul_le_mul h1 h2 hB₀.le (by positivity)
      _ = _ := by ring
  have hS : Real.sqrt (A₀ * B₀) ≤ 2 * E * Real.sqrt (A * B) := by
    calc Real.sqrt (A₀ * B₀) ≤ Real.sqrt ((2 * E) ^ 2 * (A * B)) := Real.sqrt_le_sqrt hprod
      _ = 2 * E * Real.sqrt (A * B) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hS0 : 0 < Real.sqrt (A₀ * B₀) := Real.sqrt_pos.mpr (by positivity)
  have hS1 : 0 < Real.sqrt (A * B) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hS1]
  calc Real.pi = Real.pi / Real.sqrt (A₀ * B₀) * Real.sqrt (A₀ * B₀) := by field_simp
    _ ≤ Real.pi / Real.sqrt (A₀ * B₀) * (2 * E * Real.sqrt (A * B)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

end GoldbachBoundaries.Phi2Proof
