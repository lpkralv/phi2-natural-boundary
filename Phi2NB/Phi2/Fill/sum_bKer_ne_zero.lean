import Phi2NB.Phi2.Fill.DCommon
import Phi2NB.Phi2.Fill.bKer_cone
import Phi2NB.Phi2.Fill.norm_bKer_le

/-! The non-cancellation lemma without zeros: `sum_bKer_ne_zero`. Divide by `b_τ(u₀)`. In the window `u_i ≤ u₀ + √u₀` every
term has real part `≥ 0` (`bKer_cone`) and the `i₀` term is `q_{i₀} ≥ 1`. Outside, `|b_τ(u_i)/b_τ(u₀)| ≤ 2e^{-π(u_i - u₀)}`
(`norm_bKer_le`), and with `log²x ≤ 4x` the unit fibre at `u₀ + n` (which meets the tail only when `u₀ < (n+1)²`)
contributes at most `16 K (n+2)² e^{-πn}`; the tail of this convergent series past `N` is `≤ 1/2` once `u₀ ≥ (N+1)²`.
So the real part of the normalised sum is `≥ 1/2`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `log² x ≤ 4x` for `x ≥ 1`. -/
private lemma log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : Real.log x ≤ 2 * Real.sqrt x := by linarith
  calc Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ hl h2 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt (by linarith)]; ring

/-- **The non-cancellation lemma, without zeros**. Fix `Y > 0` and `K`. There is `U` such that for
`0 < τ ≤ Y` and any family of heights `u_i` with weights `q_i ∈ ℕ`: if the minimum `u₀ = u_{i₀} ≥ U` is attained with
`q_{i₀} ≥ 1`, every unit interval `[v, v+1)` holds finitely many `u_i`, and for `v ≥ 0` their total weight is
`≤ K log²(v + 3)`, then `∑ q_i b_τ(u_i) ≠ 0`.

Proof: divide by `b_τ(u₀)`. Window `u_i ≤ u₀ + √u₀`: every term has real part `≥ 0` (`bKer_cone`), and the `i₀` term
is `q_{i₀} ≥ 1`. Tail: by `norm_bKer_le` and the unit-interval weights it is `≤ 2K ∑_{j ≥ 0} e^{-π(√u₀ + j)}
log²(u₀ + √u₀ + j + 4) ≤ 1/2` for `u₀ ≥ U`. So the real part of the normalized sum is `≥ 1/2`. (Summability of the family
follows from the same bounds.) -/
theorem sum_bKer_ne_zero {Y K : ℝ} (hY : 0 < Y) :
    ∃ U : ℝ, ∀ τ ∈ Ioc (0 : ℝ) Y, ∀ {ι : Type} (u : ι → ℝ) (q : ι → ℕ) (i₀ : ι),
      U ≤ u i₀ → (∀ i, u i₀ ≤ u i) → 1 ≤ q i₀ →
      (∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite) →
      (∀ v : ℝ, 0 ≤ v → ∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, (q i : ℝ) ≤ K * Real.log (v + 3) ^ 2) →
      ∑' i, (q i : ℂ) * bKer τ (u i) ≠ 0 := by
  classical
  obtain ⟨U₁, -, hU₁⟩ := bKer_cone hY
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  -- the tail series
  set A : ℕ → ℝ := fun n => 16 * K' * ((2 + n) ^ 2 * Real.exp (-Real.pi * n)) with hA
  have hA0 : ∀ n, 0 ≤ A n := fun n => by positivity
  have hAs : Summable A := (D_summable_sq_exp 2).mul_left (16 * K')
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_sum_nat_add A)).2 (1 / 2) (by norm_num)).exists
  refine ⟨max (max U₁ 1) (((N : ℝ) + 1) ^ 2), ?_⟩
  intro τ hτ ι u q i₀ hU hmin hq hfin hW
  set u₀ := u i₀ with hu₀def
  have hu₀U₁ : U₁ ≤ u₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hU
  have hu₀1 : 1 ≤ u₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hU
  have hu₀N : ((N : ℝ) + 1) ^ 2 ≤ u₀ := le_trans (le_max_right _ _) hU
  have hτ0 : 0 ≤ τ := hτ.1.le
  have hpi := Real.pi_pos
  -- normalisation
  set b₀ := bKer τ u₀ with hb₀
  have hb₀ne : b₀ ≠ 0 := by
    rw [hb₀, bKer]
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp))
      (Complex.Gamma_ne_zero_of_re_pos (by simp))
  set w : ι → ℂ := fun i => bKer τ (u i) / b₀ with hw
  have hwle : ∀ i, ‖w i‖ ≤ 2 * Real.exp (-Real.pi * (⌊u i - u₀⌋₊ : ℕ)) := by
    intro i
    have h0 : 0 ≤ u i - u₀ := by linarith [hmin i]
    have h1 := norm_bKer_le hτ0 (by linarith) (hmin i) (τ := τ)
    have hb₀pos : 0 < ‖b₀‖ := norm_pos_iff.mpr hb₀ne
    rw [hw, norm_div, div_le_iff₀ hb₀pos]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hb₀pos.le)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have := Nat.floor_le h0
    nlinarith
  -- fibre weights
  set W : ℕ → ℝ := fun n => 4 * K' * (u₀ + n + 3) with hWdef
  have hW0 : ∀ n, 0 ≤ W n := fun n => by positivity
  have hWb : ∀ n : ℕ, ∑ᶠ i ∈ {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}, (q i : ℝ) ≤ W n := by
    intro n
    refine (hW (u₀ + n) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)).trans ?_
    have hl := log_sq_le_four_mul (x := u₀ + n + 3)
      (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    calc K * Real.log (u₀ + n + 3) ^ 2 ≤ K' * Real.log (u₀ + n + 3) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ K' * (4 * (u₀ + n + 3)) := mul_le_mul_of_nonneg_left hl hK'0
      _ = W n := by rw [hWdef]; ring
  -- summability of the normalised family
  have hsumW : Summable fun n : ℕ => W n * (2 * Real.exp (-Real.pi * n)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((D_summable_sq_exp (u₀ + 3)).mul_left (8 * K'))
    have h1 : u₀ + n + 3 ≤ (u₀ + 3 + n) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 8 * K' * Real.exp (-Real.pi * n))
    simp only [hWdef]
    nlinarith
  obtain ⟨hSn, -⟩ := D_fibre_tsum_le u q u₀ hmin hfin W hW0 hWb (fun i => ‖w i‖)
    (fun n => 2 * Real.exp (-Real.pi * n)) (fun i => norm_nonneg _) (fun n => by positivity) hwle hsumW
  have hSc : Summable fun i => (q i : ℂ) * w i := by
    refine Summable.of_norm (hSn.congr fun i => ?_)
    simp
  -- the tail
  set r := Real.sqrt u₀ with hr
  set t : ι → ℝ := fun i => if u i ≤ u₀ + r then 0 else ‖w i‖ with ht
  set ψT : ℕ → ℝ := fun n => if (n : ℝ) + 1 ≤ r then 0 else 2 * Real.exp (-Real.pi * n) with hψT
  set AN : ℕ → ℝ := fun n => if N ≤ n then A n else 0 with hAN
  have hAN0 : ∀ n, 0 ≤ AN n := fun n => by simp only [hAN]; split_ifs <;> simp [hA0 n]
  have hANs : Summable AN := Summable.of_nonneg_of_le hAN0
    (fun n => by simp only [hAN]; split_ifs <;> simp [hA0 n]) hAs
  have hNr : (N : ℝ) + 1 ≤ r := by rw [hr]; exact Real.le_sqrt_of_sq_le hu₀N
  have hWψ : ∀ n, W n * ψT n ≤ AN n := by
    intro n
    simp only [hψT, hAN]
    by_cases hn : (n : ℝ) + 1 ≤ r
    · rw [ite_eq_left hn, mul_zero]; split_ifs <;> simp [hA0 n]
    · rw [ite_eq_right hn]
      push Not at hn
      have hNn : N ≤ n := by exact_mod_cast (by linarith : (N : ℝ) ≤ n)
      rw [ite_eq_left hNn]
      have hr0 : 0 ≤ r := Real.sqrt_nonneg _
      have hu₀n : u₀ < ((n : ℝ) + 1) ^ 2 := by
        rw [← Real.sq_sqrt (by linarith : (0 : ℝ) ≤ u₀), ← hr]
        exact pow_lt_pow_left₀ hn hr0 (by norm_num)
      have hpoly : u₀ + n + 3 ≤ 2 * (2 + n) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      simp only [hWdef, hA]
      have he := Real.exp_pos (-Real.pi * n)
      have := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 8 * K' * Real.exp (-Real.pi * n))
      nlinarith
  have hψT0 : ∀ n, 0 ≤ ψT n := fun n => by simp only [hψT]; split_ifs <;> positivity
  have hWψs : Summable fun n => W n * ψT n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hW0 n) (hψT0 n)) hWψ hANs
  have htψ : ∀ i, t i ≤ ψT ⌊u i - u₀⌋₊ := by
    intro i
    simp only [ht, hψT]
    by_cases hi : u i ≤ u₀ + r
    · rw [ite_eq_left hi]; split_ifs <;> positivity
    · rw [ite_eq_right hi]
      have h2 := Nat.lt_floor_add_one (u i - u₀)
      rw [ite_eq_right (by push Not; linarith)]
      exact hwle i
  obtain ⟨hTs, hTle⟩ := D_fibre_tsum_le u q u₀ hmin hfin W hW0 hWb t ψT
    (fun i => by simp only [ht]; split_ifs <;> simp) hψT0 htψ hWψs
  have hT : ∑' i, (q i : ℝ) * t i ≤ 1 / 2 := by
    refine hTle.trans ?_
    refine (hWψs.tsum_le_tsum hWψ hANs).trans ?_
    rw [← hANs.sum_add_tsum_nat_add N, Finset.sum_eq_zero (fun n hn => by
      simp only [hAN]; rw [ite_eq_right (by simpa using hn)])]
    simp only [zero_add, hAN]
    have : ∀ i : ℕ, (if N ≤ i + N then A (i + N) else 0) = A (i + N) := fun i => ite_eq_left (by omega)
    simp only [this]
    exact hN.le
  -- the real part
  have hlow : ∀ i, (if i = i₀ then (1 : ℝ) else 0) - (q i : ℝ) * t i ≤ ((q i : ℂ) * w i).re := by
    intro i
    have hre : ((q i : ℂ) * w i).re = (q i : ℝ) * (w i).re := by simp
    rw [hre]
    by_cases hi : u i ≤ u₀ + r
    · have ht0 : t i = 0 := by simp only [ht]; rw [ite_eq_left hi]
      rw [ht0, mul_zero, sub_zero]
      have hcone := hU₁ τ hτ u₀ (u i) hu₀U₁ (hmin i) hi
      have hwre : 0 ≤ (w i).re := by
        have := norm_nonneg (w i)
        simp only [hw]; linarith
      split_ifs with h
      · subst h
        have : w i = 1 := by simp only [hw]; exact div_self hb₀ne
        rw [this, Complex.one_re, mul_one]; exact_mod_cast hq
      · exact mul_nonneg (Nat.cast_nonneg _) hwre
    · have hne : i ≠ i₀ := by
        rintro rfl; exact hi (by simp only [← hu₀def]; linarith [Real.sqrt_nonneg u₀])
      have ht0 : t i = ‖w i‖ := by simp only [ht]; rw [ite_eq_right hi]
      rw [ite_eq_right hne, ht0, zero_sub, ← mul_neg]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have := Complex.abs_re_le_norm (w i)
      linarith [abs_le.mp this]
  have hres : Summable fun i => ((q i : ℂ) * w i).re := (Complex.hasSum_re hSc.hasSum).summable
  have hind : Summable fun i : ι => (if i = i₀ then (1 : ℝ) else 0) :=
    (hasSum_ite_eq i₀ (1 : ℝ)).summable
  have hge : 1 - ∑' i, (q i : ℝ) * t i ≤ (∑' i, (q i : ℂ) * w i).re := by
    rw [Complex.re_tsum hSc]
    calc 1 - ∑' i, (q i : ℝ) * t i
        = ∑' i, ((if i = i₀ then (1 : ℝ) else 0) - (q i : ℝ) * t i) := by
          rw [hind.tsum_sub hTs, tsum_ite_eq]
      _ ≤ _ := (hind.sub hTs).tsum_le_tsum hlow hres
  have hS0 : ∑' i, (q i : ℂ) * w i ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hge
    linarith
  have heq : ∑' i, (q i : ℂ) * bKer τ (u i) = b₀ * ∑' i, (q i : ℂ) * w i := by
    rw [← tsum_mul_left]
    congr 1
    funext i
    simp only [hw]
    field_simp
  rw [heq]
  exact mul_ne_zero hb₀ne hS0

end GoldbachBoundaries.Phi2Proof
