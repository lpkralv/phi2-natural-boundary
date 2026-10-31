import Phi2NB.Defs

/-!
# Under RH, the non-trivial zeros lie on the critical line

The form of Mathlib's `RiemannHypothesis` used for members of `NontrivialZeros`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- Under RH a non-trivial zero lies on the critical line. -/
lemma sigmaFinite_re_eq_half (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ρ.re = 1 / 2 := by
  refine hRH ρ hρ.1 ?_ ?_
  · rintro ⟨n, rfl⟩
    have h := hρ.2.1
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hρ.1

end GoldbachBoundaries
