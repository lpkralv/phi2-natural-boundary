import Phi2NB.Defs
import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# Non-trivial zeros of arbitrarily large height

`ζ` has non-trivial zeros of arbitrarily large positive and negative height (no RH), and the non-trivial zeros are
closed under conjugation.

Route. If the zeros of Riemann's entire `ξ` (PNT+ `riemannXi`) were finitely many, PNT+'s genus-one Hadamard
factorisation `riemannXi_hadamard_factorization_no_monomial` would be a *finite* product, so `|ξ(z)| ≤ exp(a + b|z|)`.
But `|ξ(2m+2)| ≥ m! / π^(m+1)` (from `ξ = s(s-1)Γ_ℝ(s)ζ(s)/2`, `Γ_ℝ(2m+2) = π^{-(m+1)} m!`, `ζ(2m+2) ≥ 1`), and `m!`
beats every exponential. Every zero of `ξ` is a non-trivial zero of `ζ` (`Re ≥ 1` is zero-free and the functional
equation `ξ(1-s) = ξ(s)` reflects `Re ≤ 0` into it). The divisor of `ξ` has finitely many points of bounded modulus,
so there are non-trivial zeros of arbitrarily large modulus; they lie in the strip `0 < Re < 1`, so their heights
are unbounded, and conjugation turns a large negative height into a large positive one.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-! ## Zeros of `ξ` are non-trivial zeros of `ζ` -/

lemma riemannXi_one : riemannXi 1 = 1 / 2 := by
  simp [riemannXi]

/-- A zero of `ξ` with positive real part is a zero of `ζ`. -/
lemma riemannZeta_eq_zero_of_riemannXi_eq_zero {w : ℂ} (hw : riemannXi w = 0) (hre : 0 < w.re) :
    riemannZeta w = 0 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hre
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [riemannXi_one] at hw
    norm_num at hw
  rw [riemannXi_eq_mul_completedRiemannZeta hw0 hw1] at hw
  have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hΛ : completedRiemannZeta w = 0 := by
    have : w * (w - 1) * completedRiemannZeta w = 0 := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      field_simp at hw
      simpa using hw
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hw0
      · exact absurd h hw1'
    · exact h
  rw [riemannZeta_def_of_ne_zero hw0, hΛ, zero_div]

/-- Every zero of `ξ` is a non-trivial zero of `ζ`. -/
lemma mem_nontrivialZeros_of_riemannXi_eq_zero {z : ℂ} (hz : riemannXi z = 0) :
    z ∈ NontrivialZeros := by
  have hlt : z.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h
      (riemannZeta_eq_zero_of_riemannXi_eq_zero hz (by linarith))
  have hpos : 0 < z.re := by
    by_contra h
    push Not at h
    have h1 : riemannXi (1 - z) = 0 := by rw [riemannXi_one_sub]; exact hz
    have hre : 1 ≤ (1 - z).re := by simp; linarith
    exact riemannZeta_ne_zero_of_one_le_re hre
      (riemannZeta_eq_zero_of_riemannXi_eq_zero h1 (by linarith))
  exact ⟨riemannZeta_eq_zero_of_riemannXi_eq_zero hz hpos, hpos, hlt⟩

/-- A point in the support of the divisor of `ξ` is a zero of `ξ`. -/
lemma riemannXi_eq_zero_of_divisor_ne_zero {z : ℂ}
    (hz : MeromorphicOn.divisor riemannXi (univ : Set ℂ) z ≠ 0) : riemannXi z = 0 := by
  have han : AnalyticAt ℂ riemannXi z := differentiable_riemannXi.analyticAt z
  have hmero : MeromorphicOn riemannXi (univ : Set ℂ) :=
    fun x _ => (differentiable_riemannXi.analyticAt x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (mem_univ z)] at hz
  by_contra hne
  have h0 : analyticOrderAt riemannXi z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hne)
  rw [han.meromorphicOrderAt_eq, h0] at hz
  simp at hz

/-! ## Growth of `ξ` -/

/-- `|E₁(u)| ≤ exp(2|u|)` for the genus-one Weierstrass factor `E₁(u) = (1 - u) e^u`. -/
lemma norm_weierstrassFactor_one_le (u : ℂ) :
    ‖weierstrassFactor 1 u‖ ≤ Real.exp (2 * ‖u‖) := by
  have hpl : partialLogSum 1 u = u := by
    simp [partialLogSum, logTaylor, Finset.sum_range_succ]
  rw [weierstrassFactor_def, hpl, norm_mul, Complex.norm_exp]
  have h1 : ‖1 - u‖ ≤ Real.exp ‖u‖ := by
    calc ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
      _ = ‖u‖ + 1 := by simp [add_comm]
      _ ≤ Real.exp ‖u‖ := Real.add_one_le_exp _
  have h2 : Real.exp u.re ≤ Real.exp ‖u‖ :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (Complex.abs_re_le_norm u))
  calc ‖1 - u‖ * Real.exp u.re ≤ Real.exp ‖u‖ * Real.exp ‖u‖ :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ‖u‖) := by rw [← Real.exp_add]; ring_nf

/-- If `ξ` had only finitely many zeros (with multiplicity), it would have exponential growth. -/
lemma riemannXi_exp_bound_of_finite
    (hfin : Finite (Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ))) :
    ∃ a b : ℝ, ∀ z : ℂ, ‖riemannXi z‖ ≤ Real.exp (a + b * ‖z‖) := by
  classical
  let := Fintype.ofFinite (Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ))
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  set c : ℝ := ∑ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
    2 * ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ with hc
  refine ⟨‖P.coeff 0‖, ‖P.coeff 1‖ + c, fun z => ?_⟩
  rw [hfac z, norm_mul, Complex.norm_exp]
  have hP : (Polynomial.eval z P).re ≤ ‖P.coeff 0‖ + ‖P.coeff 1‖ * ‖z‖ := by
    have hPe : Polynomial.eval z P = P.coeff 1 * z + P.coeff 0 := by
      conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
      simp
    rw [hPe]
    calc (P.coeff 1 * z + P.coeff 0).re ≤ ‖P.coeff 1 * z + P.coeff 0‖ := Complex.re_le_norm _
      _ ≤ ‖P.coeff 1 * z‖ + ‖P.coeff 0‖ := norm_add_le _ _
      _ = ‖P.coeff 0‖ + ‖P.coeff 1‖ * ‖z‖ := by rw [norm_mul]; ring
  have hprod : ‖Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (univ : Set ℂ) z‖ ≤
      Real.exp (c * ‖z‖) := by
    rw [Complex.Hadamard.divisorCanonicalProduct, tprod_fintype, norm_prod]
    calc ∏ p, ‖weierstrassFactor 1 (z / Complex.Hadamard.divisorZeroIndex₀_val p)‖
        ≤ ∏ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
            Real.exp (2 * ‖z / Complex.Hadamard.divisorZeroIndex₀_val p‖) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
            (fun p _ => norm_weierstrassFactor_one_le _)
      _ = Real.exp (c * ‖z‖) := by
          rw [← Real.exp_sum, hc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [norm_div]
          ring
  calc Real.exp (Polynomial.eval z P).re *
        ‖Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (univ : Set ℂ) z‖
      ≤ Real.exp (‖P.coeff 0‖ + ‖P.coeff 1‖ * ‖z‖) * Real.exp (c * ‖z‖) :=
        mul_le_mul (Real.exp_le_exp.mpr hP) hprod (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (‖P.coeff 0‖ + (‖P.coeff 1‖ + c) * ‖z‖) := by rw [← Real.exp_add]; ring_nf

/-- `ζ(k) ≥ 1` in norm for an integer `k ≥ 2`. -/
lemma one_le_norm_riemannZeta_nat {k : ℕ} (hk : 1 < k) : 1 ≤ ‖riemannZeta k‖ := by
  rw [zeta_nat_eq_tsum_of_gt_one hk]
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ k := Real.summable_one_div_nat_pow.mpr hk
  have hcast : (∑' n : ℕ, 1 / (n : ℂ) ^ k) = ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have h1 : (1 : ℝ) ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
    have := hsum.le_tsum 1 (fun j _ => by positivity)
    simpa using this
  exact h1.trans (le_abs_self _)

/-- `|ξ(2m+2)| ≥ m! / π^(m+1)`. -/
lemma riemannXi_two_mul_succ_lower (m : ℕ) :
    (m.factorial : ℝ) / Real.pi ^ (m + 1) ≤ ‖riemannXi (2 * ((m : ℂ) + 1))‖ := by
  set s : ℂ := 2 * ((m : ℂ) + 1) with hs
  have hsre : s.re = 2 * ((m : ℝ) + 1) := by simp [hs]
  have hspos : 0 < s.re := by rw [hsre]; positivity
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hspos; simp at hspos
  have hs1 : s ≠ 1 := by
    rintro h
    have : s.re = 1 := by rw [h]; simp
    rw [hsre] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp [Gammaℝ_ne_zero_of_re_pos hspos]
  have hG : Gammaℝ s = ((Real.pi : ℂ) ^ (m + 1))⁻¹ * (m.factorial : ℂ) := by
    rw [Gammaℝ_def]
    have h1 : -s / 2 = -(((m + 1 : ℕ) : ℂ)) := by rw [hs]; push_cast; ring
    have h2 : s / 2 = (m : ℂ) + 1 := by rw [hs]; ring
    rw [h1, h2, Complex.Gamma_nat_eq_factorial, Complex.cpow_neg, Complex.cpow_natCast]
  have hz : riemannZeta s = riemannZeta ((2 * m + 2 : ℕ) : ℂ) := by
    rw [hs]; push_cast; ring_nf
  have hζ : 1 ≤ ‖riemannZeta s‖ := by
    rw [hz]; exact one_le_norm_riemannZeta_nat (by omega)
  have hpoly : 1 ≤ ‖s * (s - 1) / 2‖ := by
    have : s * (s - 1) / 2 = (((m + 1) * (2 * m + 1) : ℕ) : ℂ) := by rw [hs]; push_cast; ring
    rw [this, Complex.norm_natCast]
    have : 1 ≤ (m + 1) * (2 * m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hGn : ‖Gammaℝ s‖ = (m.factorial : ℝ) / Real.pi ^ (m + 1) := by
    rw [hG, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_natCast]
    ring
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hΛ]
  have heq : s * (s - 1) * (Gammaℝ s * riemannZeta s) / 2 =
      (s * (s - 1) / 2) * Gammaℝ s * riemannZeta s := by ring
  rw [heq, norm_mul, norm_mul, hGn]
  have hnn : 0 ≤ (m.factorial : ℝ) / Real.pi ^ (m + 1) := by positivity
  calc (m.factorial : ℝ) / Real.pi ^ (m + 1)
      = 1 * ((m.factorial : ℝ) / Real.pi ^ (m + 1)) * 1 := by ring
    _ ≤ ‖s * (s - 1) / 2‖ * ((m.factorial : ℝ) / Real.pi ^ (m + 1)) * ‖riemannZeta s‖ := by
        gcongr

/-- `ξ` has infinitely many zeros (with multiplicity): the divisor index type is infinite. -/
lemma infinite_divisorZeroIndex₀_riemannXi :
    ¬ Finite (Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ)) := by
  intro hfin
  obtain ⟨a, b, hab⟩ := riemannXi_exp_bound_of_finite hfin
  set c : ℝ := Real.pi * Real.exp (2 * b) with hc
  set K : ℝ := Real.pi * Real.exp (a + 2 * b) with hK
  have hKpos : 0 < K := by positivity
  -- `m! ≤ K c^m` for all `m`
  have hle : ∀ m : ℕ, (m.factorial : ℝ) ≤ K * c ^ m := by
    intro m
    have h1 := riemannXi_two_mul_succ_lower m
    have h2 := hab (2 * ((m : ℂ) + 1))
    have hn : ‖(2 : ℂ) * ((m : ℂ) + 1)‖ = 2 * ((m : ℝ) + 1) := by
      have : (2 : ℂ) * ((m : ℂ) + 1) = ((2 * (m + 1) : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; push_cast; ring
    rw [hn] at h2
    have h3 : (m.factorial : ℝ) / Real.pi ^ (m + 1) ≤ Real.exp (a + b * (2 * ((m : ℝ) + 1))) :=
      h1.trans h2
    have hpi : 0 < Real.pi ^ (m + 1) := by positivity
    rw [div_le_iff₀ hpi] at h3
    calc (m.factorial : ℝ) ≤ Real.exp (a + b * (2 * ((m : ℝ) + 1))) * Real.pi ^ (m + 1) := h3
      _ = K * c ^ m := by
          rw [hK, hc, mul_pow, ← Real.exp_nat_mul, pow_succ]
          have : a + b * (2 * ((m : ℝ) + 1)) = (a + 2 * b) + (m : ℝ) * (2 * b) := by ring
          rw [this, Real.exp_add]
          ring
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop c
  have hev : ∀ᶠ m : ℕ in atTop, c ^ m / (m.factorial : ℝ) < 1 / (2 * K) :=
    ht.eventually (gt_mem_nhds (by positivity))
  obtain ⟨m, hm⟩ := hev.exists
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [div_lt_div_iff₀ hf (by positivity)] at hm
  have := hle m
  nlinarith

/-- `ζ` has non-trivial zeros of arbitrarily large modulus. -/
lemma exists_nontrivialZero_norm_gt (B : ℝ) : ∃ ρ ∈ NontrivialZeros, B < ‖ρ‖ := by
  by_contra h
  push Not at h
  apply infinite_divisorZeroIndex₀_riemannXi
  have hsub : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ B := fun p =>
    h _ (mem_nontrivialZeros_of_riemannXi_eq_zero
      (riemannXi_eq_zero_of_divisor_ne_zero
        (Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p)))
  have hF := Complex.Hadamard.finite_divisorZeroIndex₀_subtype_norm_le (f := riemannXi)
    (U := univ) B (subset_univ _)
  exact Finite.of_injective (fun p => (⟨p, hsub p⟩ :
    {p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ) //
      ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ B})) (fun p q h => by simpa using h)

lemma conj_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    (starRingEnd ℂ) ρ ∈ NontrivialZeros := by
  refine ⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2⟩
  rw [riemannZeta_conj, hρ.1, map_zero]

/-- Non-trivial zeros of arbitrarily large positive height (conjugation handles the negative ones). -/
lemma exists_nontrivialZero_im_gt (T : ℝ) :
    ∃ ρ ∈ NontrivialZeros, T < ρ.im := by
  obtain ⟨ρ, hρ, hn⟩ := exists_nontrivialZero_norm_gt (|T| + 1)
  have hle := Complex.norm_le_abs_re_add_abs_im ρ
  have hre : |ρ.re| < 1 := abs_lt.mpr ⟨by linarith [hρ.2.1], hρ.2.2⟩
  have him : |T| < |ρ.im| := by linarith
  rcases le_or_gt 0 ρ.im with h | h
  · exact ⟨ρ, hρ, by rw [abs_of_nonneg h] at him; linarith [le_abs_self T]⟩
  · refine ⟨_, conj_mem_nontrivialZeros hρ, ?_⟩
    rw [abs_of_neg h] at him
    simp only [Complex.conj_im]
    linarith [le_abs_self T]

