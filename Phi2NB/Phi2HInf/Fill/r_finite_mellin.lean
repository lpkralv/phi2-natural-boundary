import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.Proof.RDefs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.r_finite_mellin`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof PhiRProof

lemma mellin_exceptionalTransform (E : Finset NontrivialZeros) {g : ℝ → ℂ} {f : ℂ → ℂ}
    {a : ℝ} (hf : ∀ s : ℂ, a < s.re →
      IntegrableOn (fun x : ℝ => g x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
        f s = ∫ x in Ioc (0 : ℝ) 1, g x * (x : ℂ) ^ (s - 1)) (n : ℕ)
    {s : ℂ} (hs : (n : ℝ) + a < s.re) :
    IntegrableOn (fun x : ℝ => exceptionalE E x ^ n * g x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      exceptionalTransform E n f s =
        ∫ x in Ioc (0 : ℝ) 1, exceptionalE E x ^ n * g x * (x : ℂ) ^ (s - 1) := by
  induction n generalizing s with
  | zero => simpa [exceptionalTransform] using hf s (by simpa using hs)
  | succ n ih =>
    have hi (ρ : NontrivialZeros) := ih (s := s - ρ) (by
      simp only [sub_re]
      push_cast at hs
      linarith [ρ.2.2.2])
    have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
        exceptionalE E x ^ (n + 1) * g x * (x : ℂ) ^ (s - 1) =
          ∑ ρ ∈ E, -zeroCoef ρ *
            (exceptionalE E x ^ n * g x * (x : ℂ) ^ ((s - ρ) - 1)) := by
      have ht : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
      simp_rw [show ∀ ρ : NontrivialZeros, (s - ρ) - 1 = -(ρ : ℂ) + (s - 1) by
        intro ρ; ring, cpow_add _ _ ht]
      rw [pow_succ, exceptionalE, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ρ hρ
      ring
    have hI : IntegrableOn (fun x : ℝ => ∑ ρ ∈ E, -zeroCoef ρ *
        (exceptionalE E x ^ n * g x * (x : ℂ) ^ ((s - ρ) - 1))) (Ioc 0 1) :=
      integrable_finsetSum E (fun ρ _ => (hi ρ).1.const_mul _)
    refine ⟨hI.congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc heq,
      integral_finsetSum E (fun ρ _ => (hi ρ).1.const_mul _)]
    unfold exceptionalTransform
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [integral_const_mul, (hi ρ).2]

lemma mellin_one {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (1 : ℂ) * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      1 / s = ∫ x in Ioc (0 : ℝ) 1, (1 : ℂ) * (x : ℂ) ^ (s - 1) := by
  have hexp : -1 < (s - 1).re := by simp; linarith
  simpa using And.intro (TIdentity.integrableOn_Ioc_cpow_of_neg_one_lt hexp)
    (TIdentity.integral_Ioc_cpow_of_neg_one_lt hexp).symm

lemma meromorphicOn_exceptionalTransform (E : Finset NontrivialZeros) {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (n : ℕ) : MeromorphicOn (exceptionalTransform E n f) univ := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro s _
    apply MeromorphicAt.fun_sum
    intro ρ hρ
    exact (MeromorphicAt.const _ s).mul
      ((ih (s - ρ) (mem_univ _)).comp_analyticAt (g := fun z : ℂ => z - ρ) (by fun_prop))

theorem meromorphicOn_Gb (E : Finset NontrivialZeros) : MeromorphicOn (Gb E) univ := by
  intro s _
  have hsum : MeromorphicAt (fun z : ℂ => ∑ ρ ∈ E, -zeroCoef ρ / (z - ρ)) s :=
    MeromorphicAt.fun_sum (fun ρ _ => (MeromorphicAt.const _ s).div
      (analyticAt_id.sub analyticAt_const).meromorphicAt)
  exact ((((meromorphicAt_Gamma s).mul (meromorphicAt_negLogDerivZeta s)).sub
    (Phi2Proof.FillA.differentiable_e1L'.analyticAt s).meromorphicAt).sub
    ((MeromorphicAt.const _ s).div (analyticAt_id.sub analyticAt_const).meromorphicAt)).sub hsum

theorem Gb_eq_integral (E : Finset NontrivialZeros) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => residualG E x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      Gb E s = ∫ x in Ioc (0 : ℝ) 1, residualG E x * (x : ℂ) ^ (s - 1) := by
  have he := mellin_exceptionalTransform E (g := fun _ => 1) (f := fun z => 1 / z)
    (a := 0) (fun z hz => mellin_one hz) 1 (s := s) (by simpa using hs)
  simp only [pow_one, mul_one] at he
  have hi := Phi2Proof.FillA.integrableOn_Ioc_hL_mul_cpow hs
  have heq : Gb E s = m1L s - exceptionalTransform E 1 (fun z => 1 / z) s := by
    have hh := Phi2Proof.FillA.Gamma_mul_negLogDerivZeta_split' hs
    rw [Gb, hh]
    simp only [exceptionalTransform, mul_one_div]
    ring
  refine ⟨(hi.sub he.1).congr_fun (fun x hx => by dsimp [residualG]; ring) measurableSet_Ioc, ?_⟩
  rw [heq, he.2]
  simp only [m1L]
  rw [← integral_sub hi he.1]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp [residualG]
  ring

lemma mellin_nat_shift (m : ℕ) (g : ℝ → ℂ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (1 / (x : ℂ)) ^ m * g x * (x : ℂ) ^ (s - 1) =
      g x * (x : ℂ) ^ ((s - m) - 1) := by
  rw [show s - (m : ℂ) - 1 = (s - 1) - m by ring,
    cpow_sub (s - 1) (m : ℂ) (ofReal_ne_zero.mpr hx.ne'), cpow_natCast, one_div, inv_pow]
  ring

theorem mellin_Pr (E : Finset NontrivialZeros) {r : ℕ} (hr : 2 ≤ r)
    {s : ℂ} (hs : (r : ℝ) < s.re) :
    IntegrableOn (fun x : ℝ => PrFun E r x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      Pr E r s = ∫ x in Ioc (0 : ℝ) 1, PrFun E r x * (x : ℂ) ^ (s - 1) := by
  have hi0 (k : ℕ) (hk : k ∈ Finset.Ico 3 (r + 1)) :=
    mellin_exceptionalTransform E (g := fun _ => 1) (f := fun z => 1 / z) (a := 0)
      (fun z hz => mellin_one hz) k (s := s - r + k) (by simp; linarith)
  have hi1 (k : ℕ) (hk : k ∈ Finset.Ico 3 (r + 1)) :=
    mellin_exceptionalTransform E (fun z hz => Gb_eq_integral E hz) (k - 1)
      (s := s - r + k) (by
        have hk1 : 1 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
        simp [Nat.cast_sub hk1]; linarith)
  let f (k : ℕ) (x : ℝ) : ℂ :=
    (exceptionalE E x ^ k + (k : ℂ) * exceptionalE E x ^ (k - 1) * residualG E x) *
      (x : ℂ) ^ ((s - r + k) - 1)
  have hif (k : ℕ) (hk : k ∈ Finset.Ico 3 (r + 1)) : IntegrableOn (f k) (Ioc 0 1) := by
    apply ((hi0 k hk).1.add ((hi1 k hk).1.const_mul (k : ℂ))).congr_fun _ measurableSet_Ioc
    intro x hx
    dsimp [f]
    ring
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      PrFun E r x * (x : ℂ) ^ (s - 1) = ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℂ) * f k x := by
    unfold PrFun
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkr : k ≤ r := by have := (Finset.mem_Ico.mp hk).2; omega
    have hh := mellin_nat_shift (r - k)
      (fun x => exceptionalE E x ^ k + (k : ℂ) * exceptionalE E x ^ (k - 1) * residualG E x)
      s hx.1
    rw [Nat.cast_sub hkr] at hh
    dsimp [f]
    rw [show s - ((r : ℂ) - k) = s - r + k by ring] at hh
    linear_combination (r.choose k : ℂ) * hh
  have hI : IntegrableOn (fun x : ℝ => ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℂ) * f k x) (Ioc 0 1) :=
    integrable_finsetSum (Finset.Ico 3 (r + 1)) (fun k hk => (hif k hk).const_mul (r.choose k : ℂ))
  refine ⟨hI.congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc heq,
    integral_finsetSum _ (fun k hk => (hif k hk).const_mul (r.choose k : ℂ))]
  unfold Pr
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  congr 1
  have h0 := (hi0 k hk).2
  have h1 := (hi1 k hk).2
  rw [h0, h1, ← integral_const_mul]
  rw [← integral_add (hi0 k hk).1 ((hi1 k hk).1.const_mul (k : ℂ))]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp [f]
  ring

theorem meromorphicOn_Pr (E : Finset NontrivialZeros) (r : ℕ) :
    MeromorphicOn (Pr E r) univ := by
  intro s _
  apply MeromorphicAt.fun_sum
  intro k hk
  have h0 : MeromorphicOn (fun z : ℂ => 1 / z) univ :=
    fun z _ => (MeromorphicAt.const _ z).div analyticAt_id.meromorphicAt
  have hp := (meromorphicOn_exceptionalTransform E h0 k (s - r + k) (mem_univ _)).comp_analyticAt (g := fun z : ℂ => z - r + k)
    (show AnalyticAt ℂ (fun z : ℂ => z - r + k) s by fun_prop)
  have hg := (meromorphicOn_exceptionalTransform E (meromorphicOn_Gb E) (k - 1)
    (s - r + k) (mem_univ _)).comp_analyticAt (g := fun z : ℂ => z - r + k)
    (show AnalyticAt ℂ (fun z : ℂ => z - r + k) s by fun_prop)
  exact (MeromorphicAt.const _ s).mul (hp.add ((MeromorphicAt.const _ s).mul hg))

theorem meromorphicOn_Mr_hinf (E : Finset NontrivialZeros) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (Mr E r) univ := by
  intro s _
  have hg : MeromorphicAt (fun z : ℂ => Gamma (z - r + 1)) s :=
    (meromorphicAt_Gamma _).comp_analyticAt (by fun_prop)
  have hd : MeromorphicAt (fun z : ℂ => negLogDerivZeta (z - r + 1)) s :=
    (meromorphicAt_negLogDerivZeta _).comp_analyticAt (by fun_prop)
  have ha : MeromorphicAt (fun z : ℂ => (cA r : ℂ) / (z - r)) s :=
    (MeromorphicAt.const _ s).div (analyticAt_id.sub analyticAt_const).meromorphicAt
  have ht := (differentiable_ER (r := r) (by omega)).analyticAt s
  have ht2 : AnalyticAt ℂ (fun z : ℂ => (cC r : ℂ) * E2L (z - r + 2)) s :=
    analyticAt_const.mul ((Phi2Proof.FillA.differentiable_E2L'.analyticAt _).comp (by fun_prop))
  have ht1 : AnalyticAt ℂ (fun z : ℂ => (cB r : ℂ) * e1L (z - r + 1)) s :=
    analyticAt_const.mul ((Phi2Proof.FillA.differentiable_e1L'.analyticAt _).comp (by fun_prop))
  exact (((((((MeromorphicAt.const _ s).mul hg).mul hd).add ha).add ht.meromorphicAt).sub
    ht2.meromorphicAt).sub ht1.meromorphicAt |>.add (meromorphicOn_Pr E r s (mem_univ _))).mul
      (analyticAt_inv_Gamma s).meromorphicAt

end GoldbachBoundaries.Phi2HInf
