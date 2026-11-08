import Phi2NB.PhiR.Proof.M1Mellin

/-! `RR_bounded_halfStrip` (step M4). Half-strip bounds for the remainder of identity (22).

On `a ≤ σ ≤ r + 2` the closed rectangle is compact and inside `σ > r - 3/2`, where `R` is continuous. On `σ ≥ r + 2`,
`R = RRraw r = Φ_r - (three terms)` (the identity of `PhiR_eq_explicit`), and every Dirichlet series there is bounded by its absolute
series at the left edge (`Φ_r` at `r + 2`, `ζ` and `ζ'/ζ` at `3`, `Φ₂` at `4`), while `|1/P_j(s)| ≤ 1`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillC

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- `Γ(s - j) P_j(s) = Γ(s)` for `Re s > j` (the proof of `Gamma_sub_mul_polyP` in `Proof/M4Reduction.lean`, repeated here so that
this file does not import `M4Reduction`, which imports it). -/
private theorem Gamma_sub_mul_polyP_rb (j : ℕ) {s : ℂ} (hs : (j : ℝ) < s.re) : Gamma (s - j) * polyP j s = Gamma s := by
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
private theorem Gamma_shift_mul_polyP_rb {r k : ℕ} (hk : k ≤ r) {s : ℂ} (hs : (r : ℝ) - k < s.re) :
    Gamma (s - r + k) * polyP (r - k) s = Gamma s := by
  have hc : (((r - k : ℕ) : ℝ)) = (r : ℝ) - k := by rw [Nat.cast_sub hk]
  have h := Gamma_sub_mul_polyP_rb (r - k) (s := s) (by rw [hc]; exact hs)
  have hc' : s - (((r - k : ℕ) : ℂ)) = s - r + k := by rw [Nat.cast_sub hk]; ring
  rwa [hc'] at h

/-- The identity of `PhiR_eq_explicit` (a private copy of `PhiR_eq_explicit'`). -/
private theorem phiR_identity_rb {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
      (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
        (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
      ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + RRraw r s := by
  have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have h1 := Gamma_shift_mul_polyP_rb (r := r) (k := 1) (by omega) (s := s) (by push_cast; linarith)
  have h2 := Gamma_shift_mul_polyP_rb (r := r) (k := 2) (by omega) (s := s) (by push_cast; linarith)
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

/-- A Dirichlet-type series `∑ c_k n_k^{-s}` is bounded on `Re s ≥ b > 0` by its absolute series at `b`. -/
theorem norm_tsum_cpow_le {ι : Type*} (c : ι → ℂ) (n : ι → ℕ) {b : ℝ} (hb : 0 < b)
    (hsum : Summable fun k => ‖c k * ((n k : ℕ) : ℂ) ^ (-(b : ℂ))‖) {s : ℂ} (hs : b ≤ s.re) :
    ‖∑' k, c k * ((n k : ℕ) : ℂ) ^ (-s)‖ ≤ ∑' k, ‖c k * ((n k : ℕ) : ℂ) ^ (-(b : ℂ))‖ := by
  refine tsum_of_norm_bounded hsum.hasSum fun k => ?_
  rw [norm_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rcases Nat.eq_zero_or_pos (n k) with h0 | hpos
  · have hs0 : -s ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [h0, Nat.cast_zero, zero_cpow hs0, norm_zero]
    exact norm_nonneg _
  · rw [norm_natCast_cpow_of_pos hpos, norm_natCast_cpow_of_pos hpos]
    refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) ?_
    simp only [neg_re, ofReal_re]
    linarith

/-- An L-series is bounded on `Re s ≥ Re b` by its absolute series at `b`. -/
theorem norm_LSeries_le (f : ℕ → ℂ) {b : ℂ} (hb : LSeriesSummable f b) {s : ℂ} (hs : b.re ≤ s.re) :
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f b n‖ :=
  tsum_of_norm_bounded (summable_norm_iff.mpr hb).hasSum fun n => LSeries.norm_term_le_of_re_le_re f hs n

/-- `|P_j(s)| ≥ 1` when `Re s ≥ j + 1`. -/
theorem one_le_norm_polyP {j : ℕ} {s : ℂ} (hs : (j : ℝ) + 1 ≤ s.re) : 1 ≤ ‖polyP j s‖ := by
  rw [polyP, norm_prod]
  refine Finset.one_le_prod₀ fun l hl => ?_
  have hl' : (l : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hl).2
  have h := Complex.abs_re_le_norm (s - (l : ℂ))
  have hre : (s - (l : ℂ)).re = s.re - l := by simp
  rw [hre] at h
  linarith [le_abs_self (s.re - l)]

/-- `|x / P_j(s)| ≤ |x|` when `Re s ≥ j + 1`. -/
theorem norm_div_polyP_le (x : ℂ) {j : ℕ} {s : ℂ} (hs : (j : ℝ) + 1 ≤ s.re) : ‖x / polyP j s‖ ≤ ‖x‖ := by
  rw [norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_polyP hs)

/-- **Half-strip bounds for the remainder** (the last clause of Proposition 7.2; no further RH use). -/
theorem RR_bounded_halfStrip' {r : ℕ} (hr : 2 ≤ r) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)))
    (hRR : ∀ s ∈ halfPlane ((r : ℝ) - 3 / 2), s ≠ (r : ℂ) → R s = RRraw r s) {a : ℝ}
    (ha : (r : ℝ) - 3 / 2 < a) (T : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  set b : ℝ := (r : ℝ) + 2 with hbdef
  -- the compact part `a ≤ σ ≤ b`
  have hK : IsCompact (Icc a b ×ℂ Icc T (T + 1)) := isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : Icc a b ×ℂ Icc T (T + 1) ⊆ halfPlane ((r : ℝ) - 3 / 2) := by
    intro s hs
    have := (Complex.mem_reProdIm.mp hs).1.1
    show (r : ℝ) - 3 / 2 < s.re
    linarith
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn (hR.continuousOn.mono hKsub)
  -- the Dirichlet-series constants
  set cΦ : (Fin r → ℕ) → ℂ := fun k => ∏ i, ((ArithmeticFunction.vonMangoldt (k i) : ℝ) : ℂ) with hcΦ
  set nΦ : (Fin r → ℕ) → ℕ := fun k => ∑ i, k i with hnΦ
  set c2 : ℕ × ℕ → ℂ := fun mn => ((ArithmeticFunction.vonMangoldt mn.1 : ℝ) : ℂ) *
    ((ArithmeticFunction.vonMangoldt mn.2 : ℝ) : ℂ) with hc2
  set n2 : ℕ × ℕ → ℕ := fun mn => mn.1 + mn.2 with hn2
  have hsumΦ : Summable fun k => ‖cΦ k * ((nΦ k : ℕ) : ℂ) ^ (-((b : ℝ) : ℂ))‖ :=
    (mellin_FL_pow (r := r) (by omega) (s := ((b : ℝ) : ℂ)) (by simp [hbdef])).1
  have hsum2 : Summable fun k => ‖c2 k * ((n2 k : ℕ) : ℂ) ^ (-(((4 : ℝ)) : ℂ))‖ := by
    have h := (FillA.mellin_FL_sq' (s := (((4 : ℝ)) : ℂ)) (by norm_num)).1
    exact h
  set MΦ : ℝ := ∑' k, ‖cΦ k * ((nΦ k : ℕ) : ℂ) ^ (-((b : ℝ) : ℂ))‖
  set M2 : ℝ := ∑' k, ‖c2 k * ((n2 k : ℕ) : ℂ) ^ (-(((4 : ℝ)) : ℂ))‖
  set Mζ : ℝ := ∑' n, ‖LSeries.term 1 (3 : ℂ) n‖
  set ML : ℝ := ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (3 : ℂ) n‖
  set A' : ℂ := ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ)
  set B' : ℂ := (r : ℂ) * ((r : ℂ) - 2)
  set C' : ℂ := ((r.choose 2 : ℕ) : ℂ)
  refine ⟨max C1 (MΦ + ‖A'‖ * Mζ + ‖B'‖ * ML + ‖C'‖ * M2), fun s hsa hT1 hT2 => ?_⟩
  by_cases hsb : s.re ≤ b
  · exact (hC1 s (Complex.mem_reProdIm.mpr ⟨⟨hsa, hsb⟩, ⟨hT1, hT2⟩⟩)).trans (le_max_left _ _)
  have hsb : b < s.re := not_le.mp hsb
  refine le_trans ?_ (le_max_right _ _)
  have hsr : (r : ℝ) < s.re := by linarith
  have hsH : s ∈ halfPlane ((r : ℝ) - 3 / 2) := by show _ < s.re; linarith
  have hsne : s ≠ (r : ℂ) := by
    intro h
    rw [h] at hsr
    simp at hsr
  rw [hRR s hsH hsne]
  have hE := phiR_identity_rb hr hsr
  set w : ℂ := s - r + 1 with hw
  have hwre : w.re = s.re - r + 1 := by simp [hw]
  have hw3 : (3 : ℂ).re ≤ w.re := by simp only [hwre]; norm_num; linarith
  have hRRe : RRraw r s = PhiR r s - A' * riemannZeta w -
      B' / polyP (r - 1) s * (deriv riemannZeta w / riemannZeta w) -
      C' / polyP (r - 2) s * Phi2 (s - r + 2) := by
    rw [hE]; ring
  rw [hRRe]
  -- `Φ_r`
  have hΦ : ‖PhiR r s‖ ≤ MΦ := by
    have h := norm_tsum_cpow_le cΦ nΦ (b := b) (by linarith) hsumΦ (s := s) hsb.le
    exact h
  -- `ζ`
  have hζ : ‖riemannZeta w‖ ≤ Mζ := by
    rw [← LSeries_one_eq_riemannZeta (by linarith [hw3, show (3 : ℂ).re = 3 by norm_num])]
    exact norm_LSeries_le 1 (LSeriesSummable_one_iff.mpr (by norm_num)) hw3
  -- `ζ'/ζ`
  have hL : ‖deriv riemannZeta w / riemannZeta w‖ ≤ ML := by
    have h1 : 1 < w.re := by linarith [hw3, show (3 : ℂ).re = 3 by norm_num]
    have heq : deriv riemannZeta w / riemannZeta w = -negLogDerivZeta w := by
      rw [negLogDerivZeta, neg_neg]
    rw [heq, norm_neg, negLogDerivZeta_eq_LSeries h1]
    exact norm_LSeries_le _ (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)) hw3
  -- `Φ₂`
  have h2 : ‖Phi2 (s - r + 2)‖ ≤ M2 := by
    have hre : (4 : ℝ) ≤ (s - r + 2).re := by simp; linarith
    have h := norm_tsum_cpow_le c2 n2 (b := 4) (by norm_num) hsum2 (s := s - r + 2) hre
    exact h
  -- `1/P_j`
  have hP1 : ‖B' / polyP (r - 1) s‖ ≤ ‖B'‖ :=
    norm_div_polyP_le _ (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
  have hP2 : ‖C' / polyP (r - 2) s‖ ≤ ‖C'‖ :=
    norm_div_polyP_le _ (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
  have t1 : ‖A' * riemannZeta w‖ ≤ ‖A'‖ * Mζ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
  have t2 : ‖B' / polyP (r - 1) s * (deriv riemannZeta w / riemannZeta w)‖ ≤ ‖B'‖ * ML := by
    rw [norm_mul]; exact mul_le_mul hP1 hL (norm_nonneg _) (norm_nonneg _)
  have t3 : ‖C' / polyP (r - 2) s * Phi2 (s - r + 2)‖ ≤ ‖C'‖ * M2 := by
    rw [norm_mul]; exact mul_le_mul hP2 h2 (norm_nonneg _) (norm_nonneg _)
  have n1 := norm_sub_le (PhiR r s - A' * riemannZeta w -
      B' / polyP (r - 1) s * (deriv riemannZeta w / riemannZeta w)) (C' / polyP (r - 2) s * Phi2 (s - r + 2))
  have n2' := norm_sub_le (PhiR r s - A' * riemannZeta w)
      (B' / polyP (r - 1) s * (deriv riemannZeta w / riemannZeta w))
  have n3 := norm_sub_le (PhiR r s) (A' * riemannZeta w)
  linarith

end GoldbachBoundaries.PhiRProof.FillC
