import Phi2NB.PhiR.Proof.Defs
import Phi2NB.Phi2.Fill.ACommon

set_option maxHeartbeats 800000

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.PhiRProof.FillA
open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- Finite powers of a nonnegative real sum, indexed by tuples. -/
private theorem hasSum_tuple_prod {f : ℕ → ℝ} (hf : Summable f) (hn : ∀ n, 0 ≤ f n) (r : ℕ) :
    HasSum (fun k : Fin r → ℕ => ∏ i, f (k i)) ((∑' n, f n) ^ r) := by
  induction r with
  | zero => simpa using (hasSum_fintype (fun k : Fin 0 → ℕ => ∏ i, f (k i)))
  | succ r ih =>
    have hnn : ∀ k : Fin r → ℕ, 0 ≤ ∏ i, f (k i) :=
      fun k => Finset.prod_nonneg fun i hi => hn (k i)
    have hsum : Summable (fun p : ℕ × (Fin r → ℕ) => f p.1 * ∏ i, f (p.2 i)) :=
      hf.mul_of_nonneg ih.summable hn hnn
    have hp := hf.hasSum.mul ih hsum
    apply (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).hasSum_iff.mp
    convert hp using 1
    · funext k
      simp [Function.comp_apply, Fin.prod_univ_succ, Fin.consEquiv]
    · rw [pow_succ]; ring


local notation "Λ" => ArithmeticFunction.vonMangoldt

private abbrev posTuple (r : ℕ) : Set (Fin r → ℕ) := {k | ∀ i, k i ≠ 0}

private theorem tuple_sum_pos {r : ℕ} (hr : 1 ≤ r) {k : Fin r → ℕ}
    (hk : ∀ i, k i ≠ 0) : 0 < ∑ i, k i := by
  have hi : k ⟨0, by omega⟩ ≤ ∑ i, k i := Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_univ _)
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (hk _)) hi

private theorem tuple_zero {r : ℕ} {k : Fin r → ℕ} (hk : ¬ ∀ i, k i ≠ 0) :
    (∏ i, ((Λ (k i) : ℝ) : ℂ)) = 0 := by
  classical
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem norm_tuple_term {r : ℕ} (hr : 1 ≤ r) {k : Fin r → ℕ}
    (hk : ∀ i, k i ≠ 0) (s : ℂ) :
    ‖(∏ i, ((Λ (k i) : ℝ) : ℂ)) * (((∑ i, k i : ℕ) : ℂ)) ^ (-s)‖ =
      (∏ i, Λ (k i)) / ((∑ i, k i : ℕ) : ℝ) ^ s.re := by
  rw [norm_mul, Complex.norm_prod, norm_natCast_cpow_of_pos (tuple_sum_pos hr hk), neg_re,
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

private theorem mellin_FL_pow_aux {r : ℕ} (hr : 1 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Summable (fun k : Fin r → ℕ => ‖(∏ i, ((Λ (k i) : ℝ) : ℂ)) *
      (((∑ i, k i : ℕ) : ℂ)) ^ (-s)‖) ∧
    MellinConvergent (fun t => ((FL t ^ r : ℝ) : ℂ)) s ∧
    mellin (fun t => ((FL t ^ r : ℝ) : ℂ)) s = Gamma s * PhiR r s := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs0 : 0 < s.re := lt_trans hr0 hs
  have hΛ : ∀ n : ℕ, 0 ≤ Λ n := fun _ => ArithmeticFunction.vonMangoldt_nonneg
  set g : ℕ → ℝ := fun n => Λ n / (n : ℝ) ^ (s.re / r) with hg
  have hg_sum : Summable g := by
    have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((s.re / r : ℝ) : ℂ))
      (by simp only [ofReal_re]; exact (lt_div_iff₀ hr0).mpr (by simpa using hs))).norm
    refine h.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [ite_eq_right hn, Complex.norm_real, Real.norm_of_nonneg (hΛ n), ofReal_re]
  have hg_nn : ∀ n, 0 ≤ g n := fun n => div_nonneg (hΛ n) (by positivity)
  have hprod := (hasSum_tuple_prod hg_sum hg_nn r).summable
  have key : ∀ k : Fin r → ℕ, (∀ i, k i ≠ 0) →
      (∏ i, (k i : ℝ) ^ (s.re / r)) ≤ ((∑ i, k i : ℕ) : ℝ) ^ s.re := by
    intro k hk
    calc (∏ i, (k i : ℝ) ^ (s.re / r))
        ≤ ∏ _i : Fin r, (((∑ i, k i : ℕ) : ℝ) ^ (s.re / r)) := by
          apply Finset.prod_le_prod₀
          · intro i hi; positivity
          · intro i hi
            apply Real.rpow_le_rpow (Nat.cast_nonneg _)
            · exact_mod_cast (Finset.single_le_sum (fun j hj => Nat.zero_le (k j)) (Finset.mem_univ i))
            · positivity
      _ = ((∑ i, k i : ℕ) : ℝ) ^ s.re := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
          congr 1
          field_simp
  have hnorm : Summable (fun k : Fin r → ℕ => ‖(∏ i, ((Λ (k i) : ℝ) : ℂ)) *
      (((∑ i, k i : ℕ) : ℂ)) ^ (-s)‖) := by
    refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) fun k => ?_
    by_cases hk : ∀ i, k i ≠ 0
    · rw [norm_tuple_term hr hk, hg, Finset.prod_div_distrib]
      apply div_le_div_of_nonneg_left
      · exact Finset.prod_nonneg fun i hi => hΛ _
      · exact Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (hk i)) _
      · exact key k hk
    · rw [tuple_zero hk, zero_mul, norm_zero]
      exact Finset.prod_nonneg fun i hi => hg_nn _
  let a : posTuple r → ℂ := fun k => ∏ i, ((Λ (k.val i) : ℝ) : ℂ)
  let w : posTuple r → ℝ := fun k => ((∑ i, k.val i : ℕ) : ℝ)
  have hw : ∀ k, 0 < w k := fun k => by
    dsimp [w]
    exact_mod_cast tuple_sum_pos hr k.prop
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun k => a k * Real.exp (-w k * t))
      ((FL t ^ r : ℝ) : ℂ) := by
    intro t ht
    have hf := Phi2Proof.FillA.summable_vonMangoldt_mul_exp_neg (mem_Ioi.mp ht)
    have hp := hasSum_tuple_prod hf (fun n => mul_nonneg (hΛ n) (Real.exp_pos _).le) r
    rw [← Complex.hasSum_ofReal] at hp
    have hsupp : Function.support (fun k : Fin r → ℕ =>
        ((∏ i, Λ (k i) * Real.exp (-((k i : ℝ) * t)) : ℝ) : ℂ)) ⊆ posTuple r := by
      intro k hk
      by_contra hn
      change ¬ ∀ i, k i ≠ 0 at hn
      change _ ≠ 0 at hk
      apply hk
      push Not at hn
      obtain ⟨i, hi⟩ := hn
      dsimp only
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), ofReal_zero]
    have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hp
    convert hsub using 1
    · funext k
      dsimp only [a, w, Function.comp_apply]
      rw [← Complex.ofReal_prod, ← Complex.ofReal_mul]
      congr 1
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      push_cast
      rw [Finset.sum_neg_distrib, neg_mul, Finset.sum_mul]
    · rfl
  have hFc : ContinuousOn (fun t => ((FL t ^ r : ℝ) : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn (Phi2Proof.FillA.FL_continuousOn_and_le_exp.1.pow r)
  have h_sum : Summable fun k => ‖a k‖ / (w k) ^ s.re := by
    refine (hnorm.subtype (posTuple r)).congr fun k => ?_
    dsimp only [Function.comp_apply]
    rw [norm_tuple_term hr k.prop]
    dsimp [a, w]
    rw [Complex.norm_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Complex.norm_real, Real.norm_of_nonneg (hΛ _)]
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw hs0 hF hFc h_sum
  refine ⟨hnorm, hconv, ?_⟩
  have hsupp : Function.support (fun k : Fin r → ℕ =>
      (∏ i, ((Λ (k i) : ℝ) : ℂ)) * (((∑ i, k i : ℕ) : ℂ)) ^ (-s)) ⊆ posTuple r := by
    intro k hk
    by_contra hn
    change _ ≠ 0 at hk
    apply hk
    dsimp only
    rw [tuple_zero hn, zero_mul]
  rw [← hval.tsum_eq, PhiR, ← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp [a, w]
  rw [cpow_neg, mul_div_assoc, div_eq_mul_inv]

/-- Mellin transform and absolute convergence of the r-fold series. -/
theorem mellin_FL_pow' {r : ℕ} (hr : 1 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Summable (fun k : Fin r → ℕ => ‖(∏ i, ((ArithmeticFunction.vonMangoldt (k i) : ℝ) : ℂ)) *
      (((∑ i, k i : ℕ) : ℂ)) ^ (-s)‖) ∧
      ∫ t in Ioi (0 : ℝ), ((FL t ^ r : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) = Gamma s * PhiR r s := by
  obtain ⟨hsum, -, hval⟩ := mellin_FL_pow_aux hr hs
  refine ⟨hsum, ?_⟩
  rw [← hval, mellin]
  simp only [smul_eq_mul, mul_comm]

end GoldbachBoundaries.PhiRProof.FillA
