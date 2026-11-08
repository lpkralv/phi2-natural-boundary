import Phi2NB.PhiR.Proof.Defs
import Phi2NB.Phi2.Proof.M1Continuation
import Phi2NB.PhiR.Fill.mellin_FL_pow
import Phi2NB.PhiR.Fill.QR_eq_sum
import Phi2NB.PhiR.Fill.norm_QR_le
import Phi2NB.PhiR.Fill.differentiable_ER
import Phi2NB.PhiR.Fill.Gamma_mul_PhiR_split

/-!
# Step M1: the Mellin identity for `Φ_r` (identity (21) of the paper, with the expansion (23))

For `r ≥ 2` and `σ > r` (no RH),
`Γ(s)Φ_r(s) = C(r,2) Γ(s-r+2)Φ₂(s-r+2) + B_r Γ(s-r+1)ψ(s-r+1) + A_r/(s-r) + K_r(s)`
(`Gamma_mul_PhiR_split`), hence `Φ_r = PhiRc r` on `σ > r` (`PhiR_eq_PhiRc`). Under RH, `K_r` is holomorphic on
`σ > r - 3/2` (`differentiableOn_KR`), because `Q_r(t) = ∑_{k ≥ 3} C(r,k) t^{-(r-k)} hL(t)^k` and
`|hL(t)| ≤ C t^{-b}` for every `b ∈ (1/2, 1)` (`Phi2Proof.norm_hL_le`).

RH enters only through `norm_QR_le` (via `norm_hL_le`). Lemmas proved in `Fill/`: `mellin_FL_pow`, `QR_eq_sum`, `norm_QR_le`,
`differentiable_ER`, `Gamma_mul_PhiR_split`. Proved in this file: `differentiableOn_JR`, `differentiableOn_KR`,
`PhiR_eq_PhiRc`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- **Mellin transform of `FL^r`** (no RH): for `r ≥ 1` and `Re s > r` the `r`-fold series `Φ_r(s)` converges
absolutely and `∫_0^∞ FL(t)^r t^{s-1} dt = Γ(s) Φ_r(s)`.
Proof: the generalization of `Phi2Proof.mellin_FL_sq` (`FillA.mellin_FL_sq'`) from `ℕ × ℕ` to `Fin r → ℕ`.
`HasSum (k ↦ ∏ Λ(k_i) e^{-(∑ k_i) t}) (FL t ^ r)` by induction on `r` through `Fin.consEquiv` and
`HasSum.mul` (nonnegative terms); absolute convergence from `(∑ k_i)^σ ≥ ∏ k_i^{σ/r}` and
`∑ Λ(n) n^{-σ/r} < ∞`; then `TIdentity.mellin_convergent_and_hasSum_of_exp` with the index type `Fin r → ℕ`
restricted to tuples with all `k_i ≠ 0`. -/
theorem mellin_FL_pow {r : ℕ} (hr : 1 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Summable (fun k : Fin r → ℕ => ‖(∏ i, ((ArithmeticFunction.vonMangoldt (k i) : ℝ) : ℂ)) *
      (((∑ i, k i : ℕ) : ℂ)) ^ (-s)‖) ∧
      ∫ t in Ioi (0 : ℝ), ((FL t ^ r : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) = Gamma s * PhiR r s :=
  FillA.mellin_FL_pow' hr hs

/-- **The binomial identity** (expansion (23) of the paper), no RH: for `r ≥ 2` and `t > 0`,
`Q_r(t) = ∑_{k=3}^r C(r,k) t^{-(r-k)} hL(t)^k`.
Proof: `FL = 1/t + hL`, `add_pow`, split off the terms `k = 0, 1, 2` (`Finset.sum_range_succ`), and check
`cC + cB + cA = 1`, `2cC + cB = r`, `cC = C(r,2)` (`ring`/`field_simp` on the casts; `r ≥ 2` for `Nat.cast_sub`). -/
theorem QR_eq_sum {r : ℕ} (hr : 2 ≤ r) {t : ℝ} (ht : 0 < t) :
    QR r t = ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℝ) * (1 / t) ^ (r - k) * hL t ^ k :=
  FillA.QR_eq_sum' hr ht

/-- **`Q_r(t) = O(t^{-(r - 3 + 3b)})` on `(0, 1]`** (RH), for every `b ∈ (1/2, 1)`; and `Q_r` is continuous on
`(0, ∞)`. (The bound on `Q_r` in the proof of Proposition 7.2, with `t^{-b}` as `norm_hL_le` gives it; with
`b ↓ 1/2` the exponent tends to `r - 3/2`.)
Proof: `QR_eq_sum`, `Phi2Proof.norm_hL_le`, and `t^{-(r-k)} t^{-kb} = t^{-r + k(1-b)} ≤ t^{-r + 3(1-b)}` for `k ≥ 3`,
`0 < t ≤ 1`; continuity from `FL_basic`. -/
theorem norm_QR_le (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1) :
    ContinuousOn (QR r) (Ioi 0) ∧
      ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, |QR r t| ≤ C * t ^ (-((r : ℝ) - 3 + 3 * b)) :=
  FillA.norm_QR_le' hRH hr hb hb1

/-- **`E_r` is entire** (no RH), `r ≥ 1`.
Proof: `FL_basic` gives `0 ≤ FL t ≤ C e^{-t}` on `t ≥ 1`, so `FL^r ≤ max C 0 ^ r e^{-t}` there; then
`TIdentity.differentiable_integral_Ioi_cpow` (as `FillA.differentiable_E2L'`). -/
theorem differentiable_ER {r : ℕ} (hr : 1 ≤ r) : Differentiable ℂ (ER r) :=
  FillA.differentiable_ER' hr

/-- **The split of `Γ Φ_r`** (identity (21) of the paper), no RH: for `r ≥ 2` and `Re s > r`,
`Γ(s)Φ_r(s) = C(r,2) Γ(s-r+2)Φ₂(s-r+2) + B_r Γ(s-r+1)ψ(s-r+1) + A_r/(s-r) + K_r(s)`.
Proof: `mellin_FL_pow`; split `∫_0^∞ = ∫_0^1 + ∫_1^∞` (giving `E_r`); on `(0,1]` substitute the definition of
`Q_r` and integrate term by term (each term is integrable for `σ > r`: `FL²` against `t^{(s-r+2)-1}` by
`mellin_FL_sq`, `FL` against `t^{(s-r+1)-1}` by `mellin_FL`, `t^{s-r-1}` by `TIdentity.integral_Ioc_cpow_of_neg_one_lt`);
then `∫_0^1 FL² t^{w-1} = Γ(w)Φ₂(w) - E₂(w)` and `∫_0^1 FL t^{z-1} = Γ(z)ψ(z) - e₁(z)` (split of `mellin_FL_sq`,
`mellin_FL` at `1`). -/
theorem Gamma_mul_PhiR_split {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Gamma s * PhiR r s =
      (cC r : ℂ) * (Gamma (s - r + 2) * Phi2 (s - r + 2)) +
        (cB r : ℂ) * (Gamma (s - r + 1) * negLogDerivZeta (s - r + 1)) + (cA r : ℂ) / (s - r) + KR r s :=
  FillA.Gamma_mul_PhiR_split' hr hs

/-- **`J_r` is holomorphic on `σ > r - 3/2`** (RH; the pattern of `Phi2Proof.differentiableOn_RrL`): at
`s` pick `b ∈ (1/2, 1)` with `r - 3 + 3b < Re s` and apply `TIdentity.differentiableOn_integral_Ioc_cpow` to
`norm_QR_le`. -/
theorem differentiableOn_JR (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    DifferentiableOn ℂ (JR r) (halfPlane ((r : ℝ) - 3 / 2)) := by
  intro s hs
  have hs1 : (r : ℝ) - 3 / 2 < s.re := hs
  set b : ℝ := min ((s.re - (r : ℝ) + 3) / 3 / 2 + 1 / 4) (3 / 4) with hbdef
  have hb : 1 / 2 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h3b : (r : ℝ) - 3 + 3 * b < s.re := by
    have : b ≤ (s.re - (r : ℝ) + 3) / 3 / 2 + 1 / 4 := min_le_left _ _
    linarith
  obtain ⟨hcont, C, hC⟩ := norm_QR_le hRH hr hb hb1
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((QR r t : ℝ) : ℂ)) (volume.restrict (Ioc 0 1)) :=
    (Complex.continuous_ofReal.comp_continuousOn (hcont.mono Ioc_subset_Ioi_self)).aestronglyMeasurable
      measurableSet_Ioc
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1, ‖((QR r t : ℝ) : ℂ)‖ ≤ C * t ^ (-((r : ℝ) - 3 + 3 * b)) := by
    intro t ht
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hC t ht
  have hD := TIdentity.differentiableOn_integral_Ioc_cpow hmeas hbound
  exact (hD.differentiableAt ((isOpen_halfPlane _).mem_nhds h3b)).differentiableWithinAt

/-- **`K_r` is holomorphic on `σ > r - 3/2`** (RH): `J_r` there, `E_r`, `E₂`, `e₁` entire. -/
theorem differentiableOn_KR (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    DifferentiableOn ℂ (KR r) (halfPlane ((r : ℝ) - 3 / 2)) := by
  obtain ⟨hd1, hd2⟩ := differentiable_e1L_E2L
  have hE : Differentiable ℂ (ER r) := differentiable_ER (by omega)
  have h2 : Differentiable ℂ fun s : ℂ => (cC r : ℂ) * E2L (s - r + 2) :=
    (hd2.comp ((differentiable_id.sub_const _).add_const _)).const_mul _
  have h1 : Differentiable ℂ fun s : ℂ => (cB r : ℂ) * e1L (s - r + 1) :=
    (hd1.comp ((differentiable_id.sub_const _).add_const _)).const_mul _
  exact (((differentiableOn_JR hRH hr).add hE.differentiableOn).sub h2.differentiableOn).sub
    h1.differentiableOn

/-- **`Φ_r = PhiRc r` on `σ > r`** (no RH): divide `Gamma_mul_PhiR_split` by `Γ(s) ≠ 0`, and
`Φ₂ = Phi2c` on `σ > 2` (`Phi2Proof.phi2_identity`). -/
theorem PhiR_eq_PhiRc {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) : PhiR r s = PhiRc r s := by
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by have : (0 : ℝ) ≤ r := r.cast_nonneg; linarith)
  have hw : 2 < (s - r + 2).re := by simp; linarith
  have hsplit := Gamma_mul_PhiR_split hr hs
  have hP2 : Phi2 (s - r + 2) = Phi2c (s - r + 2) := phi2_identity hw
  rw [hP2] at hsplit
  have : PhiR r s = (Gamma s)⁻¹ * (Gamma s * PhiR r s) := by field_simp
  rw [this, hsplit, PhiRc, phiRCoef, phiRRest]
  ring

end GoldbachBoundaries.PhiRProof
