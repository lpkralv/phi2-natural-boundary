import Phi2NB.Phi2.Proof.M3Radial

/-! The phase cone `bKer_cone`, by Euler's limit `Complex.GammaSeq_tendsto_Gamma`. The `n^z n!`
factors cancel in `b_τ(u)/b_τ(u₀)` (the arguments sum to `1 + iτ` on both sides), leaving
`∏_{j ≤ n} (P₀ + iq)/(P₁ + iq)` with `c = j + 1/2`, `q = cτ`, `P₀ = c² + u₀(u₀+τ) ≤ P₁ = c² + u(u+τ)`. Each factor has
`0 ≤ arg ≤ q(P₁ - P₀)/P₀²` (via `arg ≤ tan arg`), so the argument of the product is the sum of the arguments
(`Complex.arg_mul`), at most `τ(s₁ - s₀) ∑_j c/(c² + s₀)² ≤ 2τ(s₁ - s₀)/s₀` (telescoping), which is `≤ 1 < π/3` for
`u₀ ≥ max 1 (64Y²)` and `u ≤ u₀ + √u₀`. The cone `‖w‖ ≤ 2 Re w` is closed, so the limit lies in it. No digamma, no
continuous argument. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The cone `‖w‖ ≤ 2 Re w` is closed. -/
private lemma isClosed_cone : IsClosed {w : ℂ | ‖w‖ ≤ 2 * w.re} :=
  isClosed_le continuous_norm (continuous_const.mul Complex.continuous_re)

/-- A non-zero complex number with `0 ≤ arg z ≤ π/3` lies in the cone. -/
private lemma mem_cone_of_arg {z : ℂ} (hz : z ≠ 0) (h0 : 0 ≤ arg z) (h1 : arg z ≤ Real.pi / 3) :
    ‖z‖ ≤ 2 * z.re := by
  have hc := Complex.cos_arg hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcos : 1 / 2 ≤ Real.cos (arg z) := by
    have := Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) h1
    rwa [Real.cos_pi_div_three] at this
  rw [hc, le_div_iff₀ hn] at hcos
  linarith

/-- For `0 < P₀ ≤ P₁`, `0 ≤ q`, the quotient `(P₀ + iq)/(P₁ + iq)` is non-zero with
`0 ≤ arg ≤ q (P₁ - P₀)/P₀²`. -/
private lemma arg_quot_le {P₀ P₁ q : ℝ} (hP₀ : 0 < P₀) (hP : P₀ ≤ P₁) (hq : 0 ≤ q) :
    ((P₀ : ℂ) + q * I) / ((P₁ : ℂ) + q * I) ≠ 0 ∧
      0 ≤ arg (((P₀ : ℂ) + q * I) / ((P₁ : ℂ) + q * I)) ∧
      arg (((P₀ : ℂ) + q * I) / ((P₁ : ℂ) + q * I)) ≤ q * (P₁ - P₀) / P₀ ^ 2 := by
  set z := ((P₀ : ℂ) + q * I) / ((P₁ : ℂ) + q * I) with hzdef
  have hP₁ : 0 < P₁ := by linarith
  have hD : 0 < P₁ ^ 2 + q ^ 2 := by positivity
  have hden : ((P₁ : ℂ) + q * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hre : z.re = (P₀ * P₁ + q * q) / (P₁ ^ 2 + q ^ 2) := by
    rw [hzdef, Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
  have him : z.im = q * (P₁ - P₀) / (P₁ ^ 2 + q ^ 2) := by
    rw [hzdef, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp
  have hrepos : 0 < z.re := by rw [hre]; positivity
  have himnn : 0 ≤ z.im := by rw [him]; exact div_nonneg (mul_nonneg hq (by linarith)) hD.le
  have hz : z ≠ 0 := fun h => by rw [h] at hrepos; simp at hrepos
  have harg0 : 0 ≤ arg z := Complex.arg_nonneg_iff.mpr himnn
  have hlt : arg z < Real.pi / 2 := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrepos)
    exact (abs_lt.mp this).2
  refine ⟨hz, harg0, ?_⟩
  have htan := Real.le_tan harg0 hlt
  rw [Complex.tan_arg, hre, him] at htan
  refine htan.trans ?_
  rw [div_div_div_cancel_right₀ hD.ne']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ q * (P₁ - P₀) := mul_nonneg hq (by linarith)
  have h2 : P₀ ^ 2 ≤ P₀ * P₁ + q * q := by nlinarith
  exact mul_le_mul_of_nonneg_left h2 h1

/-- Arguments add along a product of factors with arguments in `[0, π]` whose partial sums stay `≤ π`. -/
private lemma arg_prod_range {f : ℕ → ℂ} (hf : ∀ j, f j ≠ 0) (h0 : ∀ j, 0 ≤ arg (f j)) :
    ∀ N : ℕ, ∑ j ∈ Finset.range N, arg (f j) ≤ Real.pi →
      (∏ j ∈ Finset.range N, f j) ≠ 0 ∧ arg (∏ j ∈ Finset.range N, f j) = ∑ j ∈ Finset.range N, arg (f j) := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ n ih =>
    intro hB
    rw [Finset.sum_range_succ] at hB
    have hB' : ∑ j ∈ Finset.range n, arg (f j) ≤ Real.pi := by linarith [h0 n]
    obtain ⟨hne, harg⟩ := ih hB'
    have hs0 : 0 ≤ ∑ j ∈ Finset.range n, arg (f j) := Finset.sum_nonneg fun j _ => h0 j
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    refine ⟨mul_ne_zero hne (hf n), ?_⟩
    rw [Complex.arg_mul hne (hf n) ⟨by rw [harg]; linarith [Real.pi_pos, h0 n], by rw [harg]; linarith⟩, harg]

/-- Telescoping: `∑_{j<N} c_j/(c_j² + s)² ≤ 2/s - 2/(N² + s)` with `c_j = j + 1/2`, `s > 0`. -/
private lemma sum_c_div_sq_le {s : ℝ} (hs : 0 < s) (N : ℕ) :
    ∑ j ∈ Finset.range N, ((j : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) ^ 2 + s) ^ 2 ≤
      2 / s - 2 / ((N : ℝ) ^ 2 + s) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : ((n : ℝ) + 1 / 2) / (((n : ℝ) + 1 / 2) ^ 2 + s) ^ 2 ≤
        2 / ((n : ℝ) ^ 2 + s) - 2 / (((n + 1 : ℕ) : ℝ) ^ 2 + s) := by
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : 0 < (n : ℝ) ^ 2 + s := by positivity
      have h2 : 0 < ((n : ℝ) + 1) ^ 2 + s := by positivity
      have h3 : 0 < ((n : ℝ) + 1 / 2) ^ 2 + s := by positivity
      rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      have hA : (n : ℝ) ^ 2 + s ≤ ((n : ℝ) + 1 / 2) ^ 2 + s := by nlinarith
      have hB : ((n : ℝ) + 1) ^ 2 + s ≤ 4 * (((n : ℝ) + 1 / 2) ^ 2 + s) := by nlinarith
      have hP : ((n : ℝ) ^ 2 + s) * (((n : ℝ) + 1) ^ 2 + s) ≤
          4 * (((n : ℝ) + 1 / 2) ^ 2 + s) ^ 2 := by
        calc _ ≤ (((n : ℝ) + 1 / 2) ^ 2 + s) * (4 * (((n : ℝ) + 1 / 2) ^ 2 + s)) :=
              mul_le_mul hA hB h2.le h3.le
          _ = _ := by ring
      have hc : 0 ≤ (n : ℝ) + 1 / 2 := by positivity
      have : 2 * (((n : ℝ) + 1) ^ 2 + s) - (n ^ 2 + s) * 2 = 4 * ((n : ℝ) + 1 / 2) := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hP hc]
    linarith

private lemma add_nat_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (j : ℕ) : s + j ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

private lemma prod_add_ne_zero {s : ℂ} (hs : 0 < s.re) (n : ℕ) : ∏ j ∈ Finset.range (n + 1), (s + j) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => add_nat_ne_zero_of_re_pos hs j

/-- The `n^z n!` factors of Euler's sequence cancel in the ratio. -/
private lemma GammaSeq_ratio {a b a0 b0 : ℂ} (hab : a + b = a0 + b0) (ha : 0 < a.re) (hb : 0 < b.re)
    (ha0 : 0 < a0.re) (hb0 : 0 < b0.re) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq a n * GammaSeq b n / (GammaSeq a0 n * GammaSeq b0 n) =
      ∏ j ∈ Finset.range (n + 1), ((a0 + j) * (b0 + j)) / ((a + j) * (b + j)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpow : (n : ℂ) ^ a * (n : ℂ) ^ b = (n : ℂ) ^ a0 * (n : ℂ) ^ b0 := by
    rw [← cpow_add _ _ hn', ← cpow_add _ _ hn', hab]
  have hpow0 : (n : ℂ) ^ a0 * (n : ℂ) ^ b0 ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hn')) (cpow_ne_zero_iff.mpr (Or.inl hn'))
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h1 := prod_add_ne_zero ha n
  have h2 := prod_add_ne_zero hb n
  have h3 := prod_add_ne_zero ha0 n
  have h4 := prod_add_ne_zero hb0 n
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [GammaSeq]
  rw [div_mul_div_comm, div_mul_div_comm, div_div_div_eq, mul_mul_mul_comm ((n : ℂ) ^ a),
    mul_mul_mul_comm ((n : ℂ) ^ a0), hpow]
  field_simp
  exact div_self hpow0

/-- `(1/2 + i(x+τ) + j)(1/2 - ix + j) = (c² + x(x+τ)) + i cτ`, `c = j + 1/2`. -/
private lemma factor_eq (τ x : ℝ) (j : ℕ) :
    ((1 / 2 + ((x + τ : ℝ) : ℂ) * I) + j) * ((1 / 2 - (x : ℂ) * I) + j) =
      ((((j : ℝ) + 1 / 2) ^ 2 + x * (x + τ) : ℝ) : ℂ) + ((((j : ℝ) + 1 / 2) * τ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [pow_two] <;> ring

/-- The phase bound for the finite products. -/
private lemma cone_factors {τ u₀ u : ℝ} (hτ : 0 < τ) (hu₀ : 0 < u₀) (h : u₀ ≤ u) (j : ℕ) :
    let F := ((1 / 2 + ((u₀ + τ : ℝ) : ℂ) * I) + j) * ((1 / 2 - (u₀ : ℂ) * I) + j) /
      (((1 / 2 + ((u + τ : ℝ) : ℂ) * I) + j) * ((1 / 2 - (u : ℂ) * I) + j))
    F ≠ 0 ∧ 0 ≤ arg F ∧ arg F ≤ τ * (u * (u + τ) - u₀ * (u₀ + τ)) *
      (((j : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) ^ 2 + u₀ * (u₀ + τ)) ^ 2) := by
  intro F
  have hc : 0 < (j : ℝ) + 1 / 2 := by positivity
  have hF : F = (((((j : ℝ) + 1 / 2) ^ 2 + u₀ * (u₀ + τ) : ℝ) : ℂ) + ((((j : ℝ) + 1 / 2) * τ : ℝ) : ℂ) * I) /
      (((((j : ℝ) + 1 / 2) ^ 2 + u * (u + τ) : ℝ) : ℂ) + ((((j : ℝ) + 1 / 2) * τ : ℝ) : ℂ) * I) := by
    simp only [F]; rw [factor_eq, factor_eq]
  have hs : u₀ * (u₀ + τ) ≤ u * (u + τ) := by nlinarith
  obtain ⟨h1, h2, h3⟩ := arg_quot_le (P₀ := ((j : ℝ) + 1 / 2) ^ 2 + u₀ * (u₀ + τ))
    (P₁ := ((j : ℝ) + 1 / 2) ^ 2 + u * (u + τ)) (q := ((j : ℝ) + 1 / 2) * τ) (by positivity)
    (by linarith) (by positivity)
  rw [hF]
  refine ⟨h1, h2, h3.trans (le_of_eq ?_)⟩
  ring

private lemma re_half_add (x : ℝ) : 0 < (1 / 2 + (x : ℂ) * I).re := by simp
private lemma re_half_sub (x : ℝ) : 0 < (1 / 2 - (x : ℂ) * I).re := by simp

/-- **The phase cone** (`bKer_cone`), via Euler's limit for `Γ`: the finite products of
`(c + i(u₀+τ))(c - iu₀)/((c + i(u+τ))(c - iu))`, `c = j + 1/2`, have arguments in `[0, 1] ⊂ [0, π/3]`
(`arg_quot_le`, telescoping `sum_c_div_sq_le`), and the cone is closed. `U = max 1 (64 Y²)`. -/
theorem bKer_cone {Y : ℝ} (hY : 0 < Y) :
    ∃ U : ℝ, 0 < U ∧ ∀ τ ∈ Ioc (0 : ℝ) Y, ∀ u₀ u : ℝ, U ≤ u₀ → u₀ ≤ u → u ≤ u₀ + Real.sqrt u₀ →
      ‖bKer τ u / bKer τ u₀‖ ≤ 2 * (bKer τ u / bKer τ u₀).re := by
  refine ⟨max 1 (64 * Y ^ 2), by positivity, ?_⟩
  intro τ hτ u₀ u hU h hw
  obtain ⟨hτ0, hτY⟩ := hτ
  have hu₀1 : 1 ≤ u₀ := le_trans (le_max_left _ _) hU
  have hu₀Y : 64 * Y ^ 2 ≤ u₀ := le_trans (le_max_right _ _) hU
  have hu₀ : 0 < u₀ := by linarith
  set r := Real.sqrt u₀ with hr
  have hr2 : r ^ 2 = u₀ := Real.sq_sqrt hu₀.le
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hu₀1
  have hr8 : 8 * Y ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  set s₀ := u₀ * (u₀ + τ) with hs₀
  set s₁ := u * (u + τ) with hs₁
  have hs0pos : 0 < s₀ := by positivity
  have hds : 0 ≤ s₁ - s₀ := by rw [hs₀, hs₁]; nlinarith
  -- the total phase bound
  have hT : τ * (s₁ - s₀) * (2 / s₀) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hs0pos]
    have key : s₁ - s₀ = (u - u₀) * (2 * u₀ + (u - u₀) + τ) := by rw [hs₀, hs₁]; ring
    have hd0 : 0 ≤ u - u₀ := by linarith
    have hd : u - u₀ ≤ r := by linarith
    have hYr : Y ≤ r := by linarith
    have hrr : r ≤ r ^ 2 := by nlinarith
    have b1 : 2 * u₀ + (u - u₀) + τ ≤ 4 * r ^ 2 := by nlinarith
    have b2 : (u - u₀) * (2 * u₀ + (u - u₀) + τ) ≤ r * (4 * r ^ 2) :=
      mul_le_mul hd b1 (by linarith) (by positivity)
    have b3 : τ * (s₁ - s₀) * 2 ≤ Y * (r * (4 * r ^ 2)) * 2 := by
      rw [key]
      have := mul_le_mul hτY b2 (by positivity) hY.le
      linarith
    have b4 : Y * (r * (4 * r ^ 2)) * 2 ≤ r ^ 4 := by
      have : 8 * Y * r ^ 3 ≤ r * r ^ 3 := mul_le_mul_of_nonneg_right hr8 (by positivity)
      nlinarith
    have b5 : r ^ 4 ≤ s₀ := by rw [hs₀, ← hr2]; nlinarith
    linarith
  -- the factors
  set F : ℕ → ℂ := fun j => ((1 / 2 + ((u₀ + τ : ℝ) : ℂ) * I) + j) * ((1 / 2 - (u₀ : ℂ) * I) + j) /
      (((1 / 2 + ((u + τ : ℝ) : ℂ) * I) + j) * ((1 / 2 - (u : ℂ) * I) + j)) with hFdef
  have hFj : ∀ j, F j ≠ 0 ∧ 0 ≤ arg (F j) ∧ arg (F j) ≤ τ * (s₁ - s₀) *
      (((j : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) ^ 2 + s₀) ^ 2) := fun j => cone_factors hτ0 hu₀ h j
  have hsum : ∀ N, ∑ j ∈ Finset.range N, arg (F j) ≤ 1 := by
    intro N
    calc ∑ j ∈ Finset.range N, arg (F j)
        ≤ ∑ j ∈ Finset.range N, τ * (s₁ - s₀) *
            (((j : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) ^ 2 + s₀) ^ 2) :=
          Finset.sum_le_sum fun j _ => (hFj j).2.2
      _ = τ * (s₁ - s₀) * ∑ j ∈ Finset.range N,
            (((j : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) ^ 2 + s₀) ^ 2) := by rw [Finset.mul_sum]
      _ ≤ τ * (s₁ - s₀) * (2 / s₀) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hτ0.le hds)
          have h1 := sum_c_div_sq_le hs0pos N
          have h2 : 0 ≤ 2 / ((N : ℝ) ^ 2 + s₀) := by positivity
          linarith
      _ ≤ 1 := hT
  have hcone : ∀ N, ‖∏ j ∈ Finset.range N, F j‖ ≤ 2 * (∏ j ∈ Finset.range N, F j).re := by
    intro N
    have hpi := Real.pi_gt_three
    obtain ⟨hne, harg⟩ := arg_prod_range (fun j => (hFj j).1) (fun j => (hFj j).2.1) N
      (by linarith [hsum N])
    apply mem_cone_of_arg hne
    · rw [harg]; exact Finset.sum_nonneg fun j _ => (hFj j).2.1
    · rw [harg]; linarith [hsum N]
  -- Euler's limit
  have hne0 : bKer τ u₀ ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (re_half_add _))
      (Complex.Gamma_ne_zero_of_re_pos (re_half_sub _))
  have hlim : Tendsto (fun n => GammaSeq (1 / 2 + ((u + τ : ℝ) : ℂ) * I) n * GammaSeq (1 / 2 - (u : ℂ) * I) n /
      (GammaSeq (1 / 2 + ((u₀ + τ : ℝ) : ℂ) * I) n * GammaSeq (1 / 2 - (u₀ : ℂ) * I) n)) atTop
      (𝓝 (bKer τ u / bKer τ u₀)) :=
    ((GammaSeq_tendsto_Gamma _).mul (GammaSeq_tendsto_Gamma _)).div
      ((GammaSeq_tendsto_Gamma _).mul (GammaSeq_tendsto_Gamma _)) hne0
  apply isClosed_cone.mem_of_tendsto hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hsumeq : (1 / 2 + ((u + τ : ℝ) : ℂ) * I) + (1 / 2 - (u : ℂ) * I) =
      (1 / 2 + ((u₀ + τ : ℝ) : ℂ) * I) + (1 / 2 - (u₀ : ℂ) * I) := by push_cast; ring
  rw [GammaSeq_ratio hsumeq (re_half_add _) (re_half_sub _) (re_half_add _)
    (re_half_sub _) hn]
  exact hcone (n + 1)

end GoldbachBoundaries.Phi2Proof
