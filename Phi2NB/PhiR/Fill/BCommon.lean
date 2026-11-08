import Phi2NB.PhiR.Proof.M1Mellin

/-!
# Shared helpers for the lemmas of steps M2 and M5

* `fillB_zeta_ne_zero_imI`: `ζ(iτ) ≠ 0` for real `τ ≠ 0` (functional equation at `1 - iτ`).
* `fillB_analyticAt_Gamma_of_im_ne_zero`: `Γ` is analytic off the real axis.
* `fillB_analyticAt_negLogDerivZeta_shift`: `ψ(s - r + 1)` is analytic on `σ > r - 1` off `phiRPoles r` (no RH).
* `fillB_mem_HH_diff_phi2Poles`: `s - r + 2 ∈ ℍ ∖ phi2Poles` for such `s`.
* `fillB_cC_add_cB_add_cA`, `fillB_two_cC_add_cB`: the coefficient identities `C + B + A = 1`, `2C + B = r`.
* `fillB_Gamma_natCast`: `Γ(r) = (r - 1)!` for `r ≥ 1`.
* `fillB_analyticAt_inv_Gamma`, `fillB_analyticAt_Gamma_of_re_pos`, `fillB_analyticAt_phiRCoef`: copies of the real
  proofs `analyticAt_inv_Gamma`, `analyticAt_Gamma_of_re_pos`, `analyticAt_phiRCoef` of `Proof/M2Continuation.lean`.
  This file imports `Proof/M1Mellin.lean`, not `Proof/M2Continuation.lean`, so that `M2Continuation` and `M5Radial` can
  import these lemmas without an import cycle.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillB

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- `1/Γ` is analytic everywhere. (Copy of `analyticAt_inv_Gamma`.) -/
theorem fillB_analyticAt_inv_Gamma (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => (Gamma z)⁻¹) s :=
  (differentiable_one_div_Gamma.analyticAt s).congr (Filter.Eventually.of_forall fun z => by simp)

/-- `Γ` is analytic at every `s` with `Re s > 0`. (Copy of `analyticAt_Gamma_of_re_pos`.) -/
theorem fillB_analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz => by
    refine (Complex.differentiableAt_Gamma z fun m h => ?_).differentiableWithinAt
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    have hz' : 0 < z.re := hz
    linarith
  exact hd.analyticAt (hU.mem_nhds hs)

/-- `f₄` is analytic on `σ > r - 2`. (Copy of `analyticAt_phiRCoef`.) -/
theorem fillB_analyticAt_phiRCoef {r : ℕ} {s : ℂ} (hs : (r : ℝ) - 2 < s.re) :
    AnalyticAt ℂ (phiRCoef r) s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => Gamma (z - r + 2)) s := by
    refine AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - r + 2) ?_ (by fun_prop)
    exact fillB_analyticAt_Gamma_of_re_pos (by simp; linarith)
  exact (analyticAt_const.mul h1).mul (fillB_analyticAt_inv_Gamma s)

/-- `ζ(iτ) ≠ 0` for real `τ ≠ 0`: `riemannZeta_one_sub` at `s = 1 - iτ`, where `ζ(s) ≠ 0` (`Re s = 1`),
`Γ(s) ≠ 0`, `(2π)^{-s} ≠ 0` and `cos(πs/2) ≠ 0` (`πs/2` is not an odd multiple of `π/2`, as `Im s = -τ ≠ 0`). -/
theorem fillB_zeta_ne_zero_imI {τ : ℝ} (hτ : τ ≠ 0) : riemannZeta (τ * I) ≠ 0 := by
  set s : ℂ := 1 - τ * I with hsdef
  have hsre : s.re = 1 := by simp [hsdef]
  have hsim : s.im = -τ := by simp [hsdef]
  have hs1 : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hs' : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hsim] at this
    simp at this
    exact hτ this
  have hfe := riemannZeta_one_sub hs1 hs'
  have h1s : 1 - s = τ * I := by rw [hsdef]; ring
  rw [h1s] at hfe
  rw [hfe]
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre])
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    intro h
    rw [cpow_eq_zero_iff] at h
    exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) h.1
  have hcos : cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp [hsdef, Real.pi_ne_zero] at this
    exact hτ this
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hG) hcos) hz

/-- `Γ` is analytic at every point off the real axis. -/
theorem fillB_analyticAt_Gamma_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : AnalyticAt ℂ Gamma z := by
  have hU : IsOpen {w : ℂ | w.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  have hd : DifferentiableOn ℂ Gamma {w : ℂ | w.im ≠ 0} := fun w hw => by
    refine (Complex.differentiableAt_Gamma w fun m h => ?_).differentiableWithinAt
    have := congrArg Complex.im h
    simp at this
    exact hw this
  exact hd.analyticAt (hU.mem_nhds hz)

/-- `ψ(s - r + 1)` is analytic at every `s` with `Re s > r - 1` off `phiRPoles r` (no RH): `s - r + 1 ≠ 1` since
`s ≠ r`, and `ζ(s - r + 1) ≠ 0`, since a zero with real part in `(0, 1)` is a non-trivial zero `ρ` and then
`s = r - 1 + ρ`, while `ζ ≠ 0` on `Re ≥ 1`. -/
theorem fillB_analyticAt_negLogDerivZeta_shift {r : ℕ} {s : ℂ} (hs : (r : ℝ) - 1 < s.re)
    (hP : s ∉ phiRPoles r) : AnalyticAt ℂ (fun z : ℂ => negLogDerivZeta (z - r + 1)) s := by
  have h1 : s - r + 1 ≠ 1 := fun h =>
    hP (Or.inl (by rw [mem_singleton_iff]; linear_combination h))
  have hz : riemannZeta (s - r + 1) ≠ 0 := by
    intro hz
    by_cases hre : 1 ≤ (s - r + 1).re
    · exact riemannZeta_ne_zero_of_one_le_re hre hz
    · refine hP (Or.inr ⟨s - r + 1, ⟨hz, ?_, ?_⟩, by ring⟩)
      · simp; linarith
      · linarith [not_le.mp hre]
  exact AnalyticAt.comp (g := negLogDerivZeta) (f := fun z : ℂ => z - r + 1)
    (analyticAt_negLogDerivZeta h1 hz) (by fun_prop)

/-- For `Re s > r - 1` off `phiRPoles r`, `s - r + 2 ∈ ℍ ∖ phi2Poles`. -/
theorem fillB_mem_HH_diff_phi2Poles {r : ℕ} {s : ℂ} (hs : (r : ℝ) - 1 < s.re)
    (hP : s ∉ phiRPoles r) : s - r + 2 ∈ HH \ phi2Poles := by
  refine ⟨?_, ?_⟩
  · show 1 < (s - r + 2).re
    simp; linarith
  · rintro (h | ⟨ρ, hρ, h⟩)
    · rw [mem_singleton_iff] at h
      exact hP (Or.inl (by rw [mem_singleton_iff]; linear_combination h))
    · exact hP (Or.inr ⟨ρ, hρ, by linear_combination h⟩)

/-- `C(r,2) + B_r + A_r = 1`. -/
theorem fillB_cC_add_cB_add_cA (r : ℕ) : (cC r : ℂ) + (cB r : ℂ) + (cA r : ℂ) = 1 := by
  have : cC r + cB r + cA r = 1 := by simp only [cC, cB, cA]; ring
  exact_mod_cast this

/-- `2 C(r,2) + B_r = r`. -/
theorem fillB_two_cC_add_cB (r : ℕ) : 2 * (cC r : ℂ) + (cB r : ℂ) = r := by
  have : 2 * cC r + cB r = r := by simp only [cC, cB]; ring
  exact_mod_cast this

/-- `Γ(r) = (r - 1)!` for `r ≥ 1`. -/
theorem fillB_Gamma_natCast {r : ℕ} (hr : 1 ≤ r) : Gamma (r : ℂ) = ((r - 1).factorial : ℂ) := by
  have h := Complex.Gamma_nat_eq_factorial (r - 1)
  have hc : ((r - 1 : ℕ) : ℂ) + 1 = (r : ℂ) := by
    rw [Nat.cast_sub hr]; push_cast; ring
  rw [hc] at h
  exact h

end GoldbachBoundaries.PhiRProof.FillB
