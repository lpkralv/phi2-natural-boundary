import Phi2NB.PhiR.Proof.M1Mellin

/-! `PhiR_eq_explicit` (step M4). Identity (22) on `σ > r`, from `Gamma_mul_PhiR_split` divided by `Γ(s)`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillC

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- `Γ(s - j) P_j(s) = Γ(s)` for `Re s > j` (the proof of `Gamma_sub_mul_polyP` in `Proof/M4Reduction.lean`, repeated here so that
this file does not import `M4Reduction`, which imports it). -/
theorem Gamma_sub_mul_polyP_aux (j : ℕ) {s : ℂ} (hs : (j : ℝ) < s.re) : Gamma (s - j) * polyP j s = Gamma s := by
  induction j with
  | zero => simp [polyP]
  | succ j ih =>
    have hs' : (j : ℝ) < s.re := by push_cast at hs; linarith
    have hne : s - ((j + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      push_cast at hs
      linarith
    have hΓ : Gamma (s - (j : ℂ)) = (s - ((j + 1 : ℕ) : ℂ)) * Gamma (s - ((j + 1 : ℕ) : ℂ)) := by
      have h := Complex.Gamma_add_one (s - ((j + 1 : ℕ) : ℂ)) hne
      rw [show s - ((j + 1 : ℕ) : ℂ) + 1 = s - (j : ℂ) by push_cast; ring] at h
      exact h
    rw [polyP, Finset.prod_Icc_succ_top (by omega), ← polyP]
    calc Gamma (s - ((j + 1 : ℕ) : ℂ)) * (polyP j s * (s - ((j + 1 : ℕ) : ℂ)))
        = Gamma (s - (j : ℂ)) * polyP j s := by rw [hΓ]; ring
      _ = Gamma s := ih hs'

/-- `Γ(s - r + k) P_{r-k}(s) = Γ(s)` for `k ≤ r`, `Re s > r - k`, in the cast form used in `Proof/M4Reduction.lean`. -/
theorem Gamma_shift_mul_polyP {r k : ℕ} (hk : k ≤ r) {s : ℂ} (hs : (r : ℝ) - k < s.re) :
    Gamma (s - r + k) * polyP (r - k) s = Gamma s := by
  have hc : (((r - k : ℕ) : ℝ)) = (r : ℝ) - k := by rw [Nat.cast_sub hk]
  have h := Gamma_sub_mul_polyP_aux (r - k) (s := s) (by rw [hc]; exact hs)
  have hc' : s - (((r - k : ℕ) : ℂ)) = s - r + k := by rw [Nat.cast_sub hk]; ring
  rwa [hc'] at h

/-- **Identity (22) of the paper on `σ > r`** (no RH): the classical form of `Gamma_mul_PhiR_split`. -/
theorem PhiR_eq_explicit' {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
      (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
        (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
      ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + RRraw r s := by
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have h1 := Gamma_shift_mul_polyP (r := r) (k := 1) (by omega) (s := s) (by push_cast; linarith)
  have h2 := Gamma_shift_mul_polyP (r := r) (k := 2) (by omega) (s := s) (by push_cast; linarith)
  push_cast at h1 h2
  have hP1 : polyP (r - 1) s ≠ 0 := fun h => hΓ (by rw [← h1, h, mul_zero])
  have hP2 : polyP (r - 2) s ≠ 0 := fun h => hΓ (by rw [← h2, h, mul_zero])
  have hsr : s - (r : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hfact : ((r - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hζ : riemannZeta (s - r + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hsplit := Gamma_mul_PhiR_split hr hs
  -- `Γ(s - r + 2) = Γ(s)/P_{r-2}(s)`, `Γ(s - r + 1) = Γ(s)/P_{r-1}(s)`
  have hG2 : Gamma (s - r + 2) = Gamma s / polyP (r - 2) s := by
    rw [← h2]; field_simp
  have hG1 : Gamma (s - r + 1) = Gamma s / polyP (r - 1) s := by
    rw [← h1]; field_simp
  rw [hG2, hG1] at hsplit
  have hΦ : PhiR r s = (Gamma s)⁻¹ * (Gamma s * PhiR r s) := by field_simp
  rw [hΦ, hsplit, RRraw, negLogDerivZeta, Nat.cast_choose_two]
  simp only [cC, cB, cA]
  push_cast
  field_simp
  ring

end GoldbachBoundaries.PhiRProof.FillC
