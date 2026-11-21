import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.bKer_cone_hinf
import Phi2NB.Phi2HInf.Fill.norm_bKer_ratio_le
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.sum_bKer_ne_zero_hinf`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries GoldbachBoundaries.Paper2 Phi2Proof

private lemma log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h2 : Real.log x ≤ 2 * Real.sqrt x := by linarith
  calc Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := pow_le_pow_left₀ hl h2 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt (by linarith)]; ring

theorem summable_cube_exp (c : ℝ) : Summable fun n : ℕ => (c + n) ^ 3 * Real.exp (-Real.pi * n) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 Real.pi_pos
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 Real.pi_pos
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 Real.pi_pos
  have h3 := Real.summable_pow_mul_exp_neg_nat_mul 3 Real.pi_pos
  have h := (((h0.mul_left (c ^ 3)).add (h1.mul_left (3 * c ^ 2))).add
    (h2.mul_left (3 * c))).add h3
  convert h using 1
  ext n
  simp only [pow_zero, one_mul]
  ring

set_option maxHeartbeats 600000 in

theorem sum_bKer_ne_zero_hinf (hStir : StirlingStrip) {B Y K : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧ ∀ τ : ℝ, |τ| ≤ Y →
      ∀ {ι : Type} (b c u : ι → ℝ) (q : ι → ℕ) (i₀ : ι),
      (∀ i, b i ∈ Icc (1 - B) B ∧ c i ∈ Icc (1 - B) B) →
      (∀ i, b i + c i = b i₀ + c i₀) → U ≤ u i₀ → (∀ i, u i₀ ≤ u i) → 1 ≤ q i₀ →
      (∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite) →
      (∀ v : ℝ, 0 ≤ v →
        ∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, (q i : ℝ) ≤ K * Real.log (v + Y + 4) ^ 2) →
      Summable (fun i => ‖(q i : ℂ) * bKerH (b i) (c i) τ (u i)‖) ∧
        ∑' i, (q i : ℂ) * bKerH (b i) (c i) τ (u i) ≠ 0 := by
  classical
  obtain ⟨Uc, hUc, hcone⟩ := bKer_cone_hinf hStir hB hB1 hY
  obtain ⟨D, Ud, hD, hUd, hdecay⟩ := norm_bKer_ratio_le hStir hB hB1 hY
  let U₁ := max Uc Ud
  have hk := coneMargin_pos hB hB1
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  
  set A : ℕ → ℝ := fun n => 4 * K' * D * (Y + 6) * ((2 + n) ^ 3 * Real.exp (-Real.pi * n)) with hA
  have hA0 : ∀ n, 0 ≤ A n := fun n => by positivity
  have hAs : Summable A := (summable_cube_exp 2).mul_left (4 * K' * D * (Y + 6))
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_sum_nat_add A)).2 (coneMargin B / 2) (by positivity)).exists
  refine ⟨max (max U₁ 1) (((N : ℝ) + 1) ^ 2),
    hUc.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))), ?_⟩
  intro τ hτ ι b c u q i₀ hbc hα hU hmin hq hfin hW
  set u₀ := u i₀ with hu₀def
  have hu₀U₁ : U₁ ≤ u₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hU
  have hu₀1 : 1 ≤ u₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hU
  have hu₀N : ((N : ℝ) + 1) ^ 2 ≤ u₀ := le_trans (le_max_right _ _) hU
  have hu₀c : Uc ≤ u₀ := (le_max_left _ _).trans hu₀U₁
  have hu₀d : Ud ≤ u₀ := (le_max_right _ _).trans hu₀U₁
  have hpi := Real.pi_pos
  
  set b₀ := bKerH (b i₀) (c i₀) τ u₀ with hb₀
  have hb₀ne : b₀ ≠ 0 := by
    rw [hb₀, bKerH]
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(hbc i₀).1.1]))
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(hbc i₀).2.1]))
  have hb₀pos : 0 < ‖b₀‖ := norm_pos_iff.mpr hb₀ne
  set rot := coneRotation τ u₀
  have hrot : ‖rot‖ = 1 := norm_coneRotation τ u₀
  set w : ι → ℂ := fun i => rot * bKerH (b i) (c i) τ (u i) / (‖b₀‖ : ℂ) with hw
  have hwle : ∀ i, ‖w i‖ ≤ D * (2 + (⌊u i - u₀⌋₊ : ℕ)) *
      Real.exp (-Real.pi * (⌊u i - u₀⌋₊ : ℕ)) := by
    intro i
    have h0 : 0 ≤ u i - u₀ := by linarith [hmin i]
    have h1 := hdecay (b i) (hbc i).1 (c i) (hbc i).2
      (b i₀) (hbc i₀).1 (c i₀) (hbc i₀).2 (hα i) τ hτ u₀ (u i) hu₀d (hmin i)
    rw [hw, norm_div, norm_mul, hrot, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _), div_le_iff₀ hb₀pos]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hb₀pos.le)
    have hn := Nat.floor_le h0
    have hn' := Nat.lt_floor_add_one (u i - u₀)
    have he : Real.exp (-Real.pi * (u i - u₀)) ≤
        Real.exp (-Real.pi * (⌊u i - u₀⌋₊ : ℕ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hd : D * (1 + u i - u₀) ≤ D * (2 + (⌊u i - u₀⌋₊ : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      linarith
    exact mul_le_mul hd he (Real.exp_pos _).le (by positivity)
  
  set W : ℕ → ℝ := fun n => 4 * K' * (u₀ + n + Y + 4) with hWdef
  have hW0 : ∀ n, 0 ≤ W n := fun n => by positivity
  have hWb : ∀ n : ℕ, ∑ᶠ i ∈ {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}, (q i : ℝ) ≤ W n := by
    intro n
    refine (hW (u₀ + n) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)).trans ?_
    have hl := log_sq_le_four_mul (x := u₀ + n + Y + 4)
      (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    calc K * Real.log (u₀ + n + Y + 4) ^ 2 ≤ K' * Real.log (u₀ + n + Y + 4) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ K' * (4 * (u₀ + n + Y + 4)) := mul_le_mul_of_nonneg_left hl hK'0
      _ = W n := by rw [hWdef]; ring
  
  have hsumW : Summable fun n : ℕ => W n * (D * (2 + n) * Real.exp (-Real.pi * n)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_cube_exp (u₀ + Y + 4)).mul_left (4 * K' * D))
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbase : 1 ≤ u₀ + Y + 4 + n := by linarith
    have hsmall : 2 + (n : ℝ) ≤ u₀ + Y + 4 + n := by linarith
    have hprod : (u₀ + n + Y + 4) * (2 + n) ≤ (u₀ + Y + 4 + n) ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ u₀ + n + Y + 4)
      nlinarith only [hh, mul_nonneg (sq_nonneg (u₀ + Y + 4 + n)) (sub_nonneg.2 hbase)]
    have hh := mul_le_mul_of_nonneg_left hprod
      (by positivity : 0 ≤ 4 * K' * D * Real.exp (-Real.pi * n))
    dsimp [W]
    nlinarith only [hh]
  obtain ⟨hSn, -⟩ := D_fibre_tsum_le u q u₀ hmin hfin W hW0 hWb (fun i => ‖w i‖)
    (fun n => D * (2 + n) * Real.exp (-Real.pi * n)) (fun i => norm_nonneg _) (fun n => by positivity) hwle hsumW
  have hSc : Summable fun i => (q i : ℂ) * w i := by
    refine Summable.of_norm (hSn.congr fun i => ?_)
    simp
  
  set r := Real.sqrt u₀ with hr
  set t : ι → ℝ := fun i => if u i ≤ u₀ + r then 0 else ‖w i‖ with ht
  set ψT : ℕ → ℝ := fun n => if (n : ℝ) + 1 ≤ r then 0 else D * (2 + n) * Real.exp (-Real.pi * n) with hψT
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
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hpoly : u₀ + n + Y + 4 ≤ (Y + 6) * (2 + n) ^ 2 := by
        nlinarith only [hu₀n, hn0,
          mul_nonneg hY.le (by nlinarith only [hn0, sq_nonneg (n : ℝ)] : 0 ≤ (2 + (n : ℝ)) ^ 2 - 1)]
      simp only [hWdef, hA]
      have he := Real.exp_pos (-Real.pi * n)
      have hh := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ 4 * K' * D * (2 + n) * Real.exp (-Real.pi * n))
      nlinarith only [hh]
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
  have hT : ∑' i, (q i : ℝ) * t i ≤ coneMargin B / 2 := by
    refine hTle.trans ?_
    refine (hWψs.tsum_le_tsum hWψ hANs).trans ?_
    rw [← hANs.sum_add_tsum_nat_add N, Finset.sum_eq_zero (fun n hn => by
      simp only [hAN]; rw [ite_eq_right (by simpa using hn)])]
    simp only [zero_add, hAN]
    have : ∀ i : ℕ, (if N ≤ i + N then A (i + N) else 0) = A (i + N) := fun i => ite_eq_left (by omega)
    simp only [this]
    exact hN.le
  
  have hlow : ∀ i, (if i = i₀ then coneMargin B else 0) - (q i : ℝ) * t i ≤ ((q i : ℂ) * w i).re := by
    intro i
    have hre : ((q i : ℂ) * w i).re = (q i : ℝ) * (w i).re := by simp
    rw [hre]
    by_cases hi : u i ≤ u₀ + r
    · have ht0 : t i = 0 := by simp only [ht]; rw [ite_eq_left hi]
      rw [ht0, mul_zero, sub_zero]
      have hc := hcone (b i) (hbc i).1 (c i) (hbc i).2 τ hτ u₀ (u i) hu₀c (hmin i) hi
      have hwre : 0 ≤ (w i).re := by
        have hp : 0 ≤ (rot * bKerH (b i) (c i) τ (u i)).re :=
          (mul_nonneg hk.le (norm_nonneg _)).trans hc
        simpa only [hw, Complex.div_ofReal_re] using div_nonneg hp hb₀pos.le
      split_ifs with h
      · subst h
        have hhead : coneMargin B ≤ (w i).re := by
          rw [hw, Complex.div_ofReal_re]
          apply (le_div_iff₀ hb₀pos).2
          exact hc
        have hq' : (1 : ℝ) ≤ q i := by exact_mod_cast hq
        exact hhead.trans (by simpa using mul_le_mul_of_nonneg_right hq' hwre)
      · exact mul_nonneg (Nat.cast_nonneg _) hwre
    · have hne : i ≠ i₀ := by
        rintro rfl; exact hi (by simp only [← hu₀def]; linarith [Real.sqrt_nonneg u₀])
      have ht0 : t i = ‖w i‖ := by simp only [ht]; rw [ite_eq_right hi]
      rw [ite_eq_right hne, ht0, zero_sub, ← mul_neg]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have := Complex.abs_re_le_norm (w i)
      linarith [abs_le.mp this]
  have hres : Summable fun i => ((q i : ℂ) * w i).re := (Complex.hasSum_re hSc.hasSum).summable
  have hind : Summable fun i : ι => (if i = i₀ then coneMargin B else 0) :=
    (hasSum_ite_eq i₀ (coneMargin B)).summable
  have hge : coneMargin B - ∑' i, (q i : ℝ) * t i ≤ (∑' i, (q i : ℂ) * w i).re := by
    rw [Complex.re_tsum hSc]
    calc coneMargin B - ∑' i, (q i : ℝ) * t i
        = ∑' i, ((if i = i₀ then coneMargin B else 0) - (q i : ℝ) * t i) := by
          rw [hind.tsum_sub hTs, tsum_ite_eq]
      _ ≤ _ := (hind.sub hTs).tsum_le_tsum hlow hres
  have hS0 : ∑' i, (q i : ℂ) * w i ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hge
    linarith only [hge, hT, hk]
  have hrotne : rot ≠ 0 := by intro he; simp [he] at hrot
  have hscale : (‖b₀‖ : ℂ) / rot ≠ 0 := div_ne_zero
    (Complex.ofReal_ne_zero.mpr hb₀pos.ne') hrotne
  have heq : (fun i => (q i : ℂ) * bKerH (b i) (c i) τ (u i)) =
      fun i => ((‖b₀‖ : ℂ) / rot) * ((q i : ℂ) * w i) := by
    funext i
    dsimp [w]
    field_simp [hrotne, Complex.ofReal_ne_zero.mpr hb₀pos.ne']
  constructor
  · have hn : Summable (fun i => ‖(q i : ℂ) * w i‖) :=
      hSn.congr (fun i => by simp)
    have hs : Summable (fun i => ‖((‖b₀‖ : ℂ) / rot) * ((q i : ℂ) * w i)‖) := by
      simpa only [norm_mul] using hn.mul_left ‖(‖b₀‖ : ℂ) / rot‖
    exact hs.congr (fun i => congrArg norm (congrFun heq i).symm)
  · rw [heq, tsum_mul_left]
    exact mul_ne_zero hscale hS0

#print axioms log_sq_le_four_mul

end GoldbachBoundaries.Phi2HInf
