import Phi2NB.TIdentity.G7a_ZetaBound
import Phi2NB.TIdentity.G7b_LogDerivBound

/-!
# Under RH, `ζ'/ζ(x + iy) ≪_ε log |y|` on `x ≥ 1/2 + ε`, `|y| ≥ 4`

Proof. Put `ε' = min ε (1/2)`.
* `x ≥ 2`: `‖A(z)‖ ≤ 4 C_Λ 2^{-x} ≤ C_Λ` (`norm_negLogDerivZeta_le`) and `log |y| ≥ log 4 > 1`.
* `x < 2`: apply `norm_logDeriv_le_of_closedBall` to `ζ` with centre `z₀ = 3/2 + iy`,
  `R = 1 - ε'/2`, `r = 1 - ε'`. The closed disc of radius `R` lies in
  `{Re ≥ 1/2 + ε'/2, |Im| ≥ 3}`, where `ζ` is analytic (`≠ 1`) and zero-free (RH,
  `sigmaMero_re_eq_half`), and `|ζ| ≤ 4|Im| ≤ 5|y|` (`norm_riemannZeta_le_mul_abs_im`, which
  gives the constant `4`). `|ζ(3/2 + iy)| ≥ c₀ = |ζ(3)/ζ(3/2)|` (`zetaFixedLowerBound`, copied from
  PNT+ `StrongPNT.lean`, `ZetaFixedLowerBound`, Apache-2.0). With `M = 5|y|/c₀ + 2`,
  `log M ≤ log(5/c₀ + 2) + log |y|`, and the bound is `16 log M R²/(R-r)³ ≤ 128 log M / ε'³`.
-/

noncomputable section

open Complex Set Metric

namespace GoldbachBoundaries

namespace TIdentity

namespace G7c

/-! Copied from PNT+ `StrongPNT.lean` (Apache-2.0): API analogous to `HasProd.norm` and the
lower bound `ZetaFixedLowerBound`, with dot notation replaced by explicit names. -/

section
variable {α R : Type*} [SeminormedCommRing R] [NormMulClass R] [NormOneClass R]
 {f : α → R} {x : R}

lemma hasProd_nnnorm (hfx : HasProd f x) : HasProd (‖f ·‖₊) ‖x‖₊ := by
  simp only [HasProd, ← nnnorm_prod, SummationFilter.unconditional_filter] at ⊢ hfx
  exact hfx.nnnorm

theorem multipliable_nnnorm (hf : Multipliable f) : Multipliable (‖f ·‖₊) :=
  let ⟨x, hx⟩ := hf; ⟨‖x‖₊, hasProd_nnnorm hx⟩

lemma multipliable_nnnorm_tprod (hf : Multipliable f) : ‖∏' i, f i‖₊ = ∏' i, ‖f i‖₊ :=
  (hasProd_nnnorm hf.hasProd).tprod_eq.symm
end

lemma zetaFixedLowerBound (t : ℝ) :
    ‖riemannZeta (3/2 + I * t)‖₊ ≥ ‖riemannZeta 3 / riemannZeta (3 / 2)‖₊ := by
  have mp : ∀ {s : ℂ}, 1 < s.re →
      Multipliable fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹ := by
    intro s hs
    exact ⟨riemannZeta s, riemannZeta_eulerProduct_hasProd hs⟩
  have h₁ : 1 < ((3 : ℂ) / 2).re := by norm_num
  have h₂ : 1 < (3 : ℂ).re := by norm_num
  have h₃ : 1 < (3 / 2 + I * (t : ℂ)).re := by norm_num
  rw [nnnorm_div, ge_iff_le,
    div_le_iff₀ (nnnorm_pos.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))),
    ← riemannZeta_eulerProduct_tprod h₁, ← riemannZeta_eulerProduct_tprod h₂,
    ← riemannZeta_eulerProduct_tprod h₃, multipliable_nnnorm_tprod (mp h₁),
    multipliable_nnnorm_tprod (mp h₂), multipliable_nnnorm_tprod (mp h₃),
    ← (multipliable_nnnorm (mp h₃)).tprod_mul (multipliable_nnnorm (mp h₁))]
  refine (multipliable_nnnorm (mp h₂)).tprod_le_tprod (fun p ↦ ?_)
    ((multipliable_nnnorm (mp h₃)).mul (multipliable_nnnorm (mp h₁)))
  simp only [nnnorm_inv, ← mul_inv]
  have hfact : ‖1 - (p : ℂ) ^ (-3 : ℂ)‖₊ =
      ‖1 + (p : ℂ) ^ ((-3 : ℂ) / 2)‖₊ * ‖1 - (p : ℂ) ^ (-((3 : ℂ) / 2))‖₊ := by
    rw [← nnnorm_mul]; congr 1; ring_nf; rw [← Complex.cpow_nat_mul]; ring_nf
  have hne : ∀ {s : ℂ}, 1 < s.re → (1 - (p : ℂ) ^ (-s)) ≠ 0 :=
    fun hs ↦ Complex.one_sub_prime_cpow_ne_zero p.2 hs
  rw [inv_le_inv₀, hfact]
  · apply _root_.mul_le_mul_left
    rw [← norm_toNNReal, ← norm_toNNReal]
    apply Real.toNNReal_le_toNNReal
    calc ‖1 - (p : ℂ) ^ (-(3 / 2 + I * ↑t))‖
        ≤ 1 + ‖(p : ℂ) ^ (-(3 / 2 + I * ↑t))‖ := by
          rw [← Complex.norm_of_nonneg zero_le_one]; exact norm_sub_le _ _
      _ = ‖1 + (p : ℂ) ^ (-(3 : ℂ) / 2)‖ := by
          have : 0 ≤ 1 + (p : ℝ) ^ (-(3 : ℝ) / 2) :=
            by linarith [Real.rpow_nonneg (Nat.cast_nonneg' (p : ℕ)) (-3 / 2)]
          simp only [Complex.norm_natCast_cpow_of_pos (Nat.Prime.pos p.2), add_re, neg_re, mul_re,
            I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, div_ofNat_re, re_ofNat,
            neg_div', add_zero]
          rw [← Real.norm_of_nonneg this, ← Complex.norm_real, Complex.ofReal_add,
            Complex.ofReal_cpow (Nat.cast_nonneg' (p : ℕ))]
          push_cast; rfl
  · exact norm_pos_iff.mpr (hne h₂)
  · exact mul_pos (norm_pos_iff.mpr (hne h₃)) (norm_pos_iff.mpr (hne h₁))

end G7c

/-- **Under RH, `ζ'/ζ(x + iy) ≪_ε log |y|` on `x ≥ 1/2 + ε`, `|y| ≥ 4`** (the classical bound, here from
Borel–Carathéodory in derivative form).

Proof sketch. WLOG `ε ≤ 1/2`. For `2 ≤ x` use `norm_negLogDerivZeta_le` (`SigmaMeromorphic.lean`)
and `log |y| ≥ log 4 > 1`. For `x ≤ 2`, apply `norm_logDeriv_le_of_closedBall` to `f = ζ` with centre
`z₀ = 3/2 + iy`, `R = 1 - ε/2`, `r = 1 - ε`: the closed disc lies in `{Re ≥ 1/2 + ε/2, |Im| ≥ 3}`,
where `ζ` is analytic (`≠ 1`) and, by RH (`sigmaMero_re_eq_half`), zero-free;
`|ζ| ≤ C(|y| + 1)` there by `norm_riemannZeta_le_mul_abs_im`; and `|ζ(3/2 + iy)| ≥ ζ(3)/ζ(3/2)`
(Euler product; PNT+ `ZetaFixedLowerBound`). So `M ≍ |y|` and `log M ≪ log |y|`. -/
theorem norm_negLogDerivZeta_le_log (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ z : ℂ, 1 / 2 + ε ≤ z.re → 4 ≤ |z.im| →
      ‖negLogDerivZeta z‖ ≤ C * Real.log |z.im| := by
  obtain ⟨C₁, hC₁⟩ := norm_riemannZeta_le_mul_abs_im
  set D : ℝ := max C₁ 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  set e : ℝ := min ε (1 / 2) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have heε : e ≤ ε := min_le_left _ _
  set c₀ : ℝ := ‖riemannZeta 3 / riemannZeta (3 / 2)‖ with hc₀
  have hc₀pos : 0 < c₀ := by
    rw [hc₀, norm_div]
    apply div_pos <;> apply norm_pos_iff.mpr <;> apply riemannZeta_ne_zero_of_one_le_re <;>
      norm_num
  set K : ℝ := Real.log (2 * D / c₀ + 2) with hK
  have hK0 : 0 ≤ K := Real.log_nonneg (by
    have : 0 < 2 * D / c₀ := by positivity
    linarith)
  refine ⟨vmConst + 128 * (K + 1) / e ^ 3, fun z hre him => ?_⟩
  set y : ℝ := z.im with hy
  have hlog4 : 1 < Real.log 4 := by
    have := Real.exp_one_lt_d9
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith
  have hy0 : 0 < |y| := by linarith
  have hlogy : 1 ≤ Real.log |y| := le_trans hlog4.le (Real.log_le_log (by norm_num) him)
  have hA : 0 ≤ vmConst := vmConst_nonneg
  have hB : 0 ≤ 128 * (K + 1) / e ^ 3 := by positivity
  rcases le_or_gt 2 z.re with hx | hx
  · -- `Re z ≥ 2`: the absolutely convergent Dirichlet series
    have h2 : (2 : ℝ) ^ (-z.re) ≤ 1 / 4 := by
      calc (2 : ℝ) ^ (-z.re) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 4 := by rw [Real.rpow_neg (by norm_num)]; norm_num
    have h3 : ‖negLogDerivZeta z‖ ≤ vmConst := by
      calc ‖negLogDerivZeta z‖ ≤ vmConst * (4 * (2 : ℝ) ^ (-z.re)) := norm_negLogDerivZeta_le hx
        _ ≤ vmConst * (4 * (1 / 4)) := by gcongr
        _ = vmConst := by ring
    calc ‖negLogDerivZeta z‖ ≤ vmConst := h3
      _ ≤ vmConst * Real.log |y| := le_mul_of_one_le_right hA hlogy
      _ ≤ (vmConst + 128 * (K + 1) / e ^ 3) * Real.log |y| := by
          have := mul_nonneg hB (by linarith : (0 : ℝ) ≤ Real.log |y|)
          rw [add_mul]; linarith
  · -- `Re z < 2`: Borel–Carathéodory on the disc centred at `3/2 + iy`
    set z₀ : ℂ := 3 / 2 + I * y with hz₀
    have hz0re : z₀.re = 3 / 2 := by simp [hz₀]
    have hz0im : z₀.im = y := by simp [hz₀]
    set R : ℝ := 1 - e / 2 with hR
    set r : ℝ := 1 - e with hr'
    set M : ℝ := 2 * D * |y| / c₀ + 2 with hMdef
    have hr : 0 < r := by linarith
    have hrR : r < R := by linarith
    have hM : 1 < M := by
      have : 0 ≤ 2 * D * |y| / c₀ := by positivity
      linarith
    have hdisc : ∀ w ∈ closedBall z₀ R, 1 / 2 + e / 2 ≤ w.re ∧ 3 ≤ |w.im| ∧
        |w.im| ≤ |y| + 1 := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      have h1 := Complex.abs_re_le_norm (w - z₀)
      have h2 := Complex.abs_im_le_norm (w - z₀)
      simp only [sub_re, sub_im, hz0re, hz0im] at h1 h2
      refine ⟨?_, ?_, ?_⟩
      · have := neg_abs_le (w.re - 3 / 2); linarith
      · have := abs_sub_abs_le_abs_sub y w.im
        rw [abs_sub_comm] at this; linarith
      · have := abs_sub_abs_le_abs_sub w.im y; linarith
    have hw1 : ∀ w ∈ closedBall z₀ R, w ≠ 1 := by
      intro w hw h
      have := (hdisc w hw).2.1
      rw [h] at this; norm_num at this
    have hf : AnalyticOnNhd ℂ riemannZeta (closedBall z₀ R) := fun w hw =>
      DifferentiableOn.analyticAt (s := {s : ℂ | s ≠ 1})
        (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt)
        (isOpen_ne.mem_nhds (hw1 w hw))
    have hne : ∀ w ∈ closedBall z₀ R, riemannZeta w ≠ 0 := by
      intro w hw h
      have hre' := (hdisc w hw).1
      have := sigmaMero_re_eq_half hRH h (by linarith)
      linarith
    have hlow : c₀ ≤ ‖riemannZeta z₀‖ := by
      have := G7c.zetaFixedLowerBound y
      rw [hc₀, hz₀]
      exact_mod_cast this
    have hbound : ∀ w ∈ closedBall z₀ R, ‖riemannZeta w‖ ≤ M * ‖riemannZeta z₀‖ := by
      intro w hw
      obtain ⟨hwre, hwim, hwim'⟩ := hdisc w hw
      have h1 := hC₁ w (by linarith) (by linarith)
      have h2 : ‖riemannZeta w‖ ≤ 2 * D * |y| := by
        calc ‖riemannZeta w‖ ≤ C₁ * |w.im| := h1
          _ ≤ D * |w.im| := by gcongr; exact le_max_left _ _
          _ ≤ D * (|y| + 1) := by gcongr
          _ = D * |y| + D * 1 := by ring
          _ ≤ D * |y| + D * |y| := by gcongr; linarith
          _ = 2 * D * |y| := by ring
      have h3 : 2 * D * |y| ≤ M * c₀ := by
        rw [hMdef, add_mul, div_mul_cancel₀ _ hc₀pos.ne']; linarith
      calc ‖riemannZeta w‖ ≤ 2 * D * |y| := h2
        _ ≤ M * c₀ := h3
        _ ≤ M * ‖riemannZeta z₀‖ := by gcongr
    have hz : z ∈ closedBall z₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      have hn := Complex.norm_le_abs_re_add_abs_im (z - z₀)
      simp only [sub_re, sub_im, hz0re, hz0im, hy, sub_self, abs_zero, add_zero] at hn
      refine hn.trans ?_
      rw [abs_le]; constructor <;> linarith
    have key := norm_logDeriv_le_of_closedBall hr hrR hM hf hne hbound z hz
    have hRr : R - r = e / 2 := by rw [hR, hr']; ring
    have hR1 : R ^ 2 ≤ 1 := by
      have : 0 ≤ R := by linarith
      exact pow_le_one₀ this (by linarith)
    have hlogM0 : 0 < Real.log M := Real.log_pos hM
    have hstep : 16 * Real.log M * R ^ 2 / (R - r) ^ 3 ≤ 128 * Real.log M / e ^ 3 := by
      rw [hRr, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (e / 2) ^ 3 = e ^ 3 / 8 := by ring
      rw [this]
      have he3 : 0 < e ^ 3 := by positivity
      have := mul_nonneg (mul_nonneg hlogM0.le he3.le) (sub_nonneg.mpr hR1)
      nlinarith
    have hlogM : Real.log M ≤ K + Real.log |y| := by
      have hy1 : 1 ≤ |y| := by linarith
      have hM' : M ≤ (2 * D / c₀ + 2) * |y| := by
        have : 2 * D * |y| / c₀ = 2 * D / c₀ * |y| := by ring
        rw [hMdef, add_mul, this]; linarith
      calc Real.log M ≤ Real.log ((2 * D / c₀ + 2) * |y|) :=
            Real.log_le_log (by linarith) hM'
        _ = K + Real.log |y| := by
            rw [Real.log_mul (by positivity) hy0.ne']
    have hfin : 128 * Real.log M / e ^ 3 ≤ 128 * (K + 1) / e ^ 3 * Real.log |y| := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      have h1 := mul_le_mul_of_nonneg_left hlogy hK0
      have h2 : 128 * (K + 1) * Real.log |y| = 128 * (K * Real.log |y|) + 128 * Real.log |y| := by
        ring
      rw [h2]; linarith
    have hneg : ‖negLogDerivZeta z‖ = ‖deriv riemannZeta z / riemannZeta z‖ := by
      rw [negLogDerivZeta, norm_neg]
    rw [hneg]
    calc ‖deriv riemannZeta z / riemannZeta z‖
        ≤ 16 * Real.log M * R ^ 2 / (R - r) ^ 3 := key
      _ ≤ 128 * Real.log M / e ^ 3 := hstep
      _ ≤ 128 * (K + 1) / e ^ 3 * Real.log |y| := hfin
      _ ≤ (vmConst + 128 * (K + 1) / e ^ 3) * Real.log |y| := by
          have := mul_nonneg hA (by linarith : (0 : ℝ) ≤ Real.log |y|)
          rw [add_mul]; linarith

end TIdentity
end GoldbachBoundaries
