import Phi2NB.Phi2.Proof.Defs
import Phi2NB.TIdentity.Assembly

/-!
# The Mellin side of the continuation of `Φ₂`

Helpers for `Phi2/Proof/M1Continuation.lean`. With `FL(t) = ∑_n Λ(n) e^{-nt}`, `hL(t) = FL(t) - 1/t` and
`ψ = negLogDerivZeta = -ζ'/ζ`: the Mellin transforms `∫_0^∞ FL(t) t^{z-1} dt = Γ(z) ψ(z)` (`Re z > 1`) and
`∫_0^∞ FL(t)² t^{s-1} dt = Γ(s) Φ₂(s)` (`Re s > 2`), their splits at `t = 1`, Mellin inversion for `FL`, the
contour shift past the pole of `ψ` at `1` (RH), the bound `hL(t) = O(t^{-b})`, and the algebra of the identity
`Φ₂ = phi2Main + Hphi2`. The names live in the sub-namespace `FillA`.

Index sets. `Λ(0) = 0`, so the sums over `ℕ` (and `ℕ × ℕ`) are sums over `n ≠ 0` (both coordinates `≠ 0`).
`TIdentity.mellin_convergent_and_hasSum_of_exp` needs positive frequencies, so it is applied on the subtypes
`posNat = {n | n ≠ 0}` and `posPair = {mn | mn.1 ≠ 0 ∧ mn.2 ≠ 0}` and transferred with
`hasSum_subtype_iff_of_support_subset` / `tsum_subtype_eq_of_support_subset`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries.Phi2Proof.FillA

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.TIdentity

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## `FL`: summability, continuity, decay -/

theorem vonMangoldt_zero' : Λ 0 = 0 := by simp

/-- `∑_n Λ(n) e^{-nδ}` converges for `δ > 0` (`Λ(n) ≤ log n ≤ n`). -/
theorem summable_vonMangoldt_mul_exp_neg {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ => Λ n * Real.exp (-((n : ℝ) * δ)) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul 1 hδ
  refine h.of_nonneg_of_le (fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.exp_pos _).le) fun n => ?_
  simp only [pow_one]
  rw [show -((n : ℝ) * δ) = -δ * (n : ℝ) by ring]
  exact mul_le_mul_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_self (Nat.cast_nonneg _))) (Real.exp_pos _).le

theorem FL_nonneg' (t : ℝ) : 0 ≤ FL t :=
  tsum_nonneg fun _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

/-- `FL` is continuous on `t > 0` and `FL t ≤ C e^{-t}` for `t ≥ 1`. -/
theorem FL_continuousOn_and_le_exp :
    ContinuousOn FL (Ioi 0) ∧ ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → FL t ≤ C * Real.exp (-t) := by
  have hΛ : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  refine ⟨fun t ht => ?_, ?_⟩
  · have ht' : 0 < t / 2 := by have := mem_Ioi.mp ht; linarith
    have hcont : ContinuousOn FL (Ioi (t / 2)) := by
      refine continuousOn_tsum (fun n => by fun_prop) (summable_vonMangoldt_mul_exp_neg ht')
        fun n x hx => ?_
      rw [Real.norm_of_nonneg (mul_nonneg (hΛ n) (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hΛ n)
      have hx' : t / 2 < x := hx
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hmem : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (by have := mem_Ioi.mp ht; linarith)
    exact (hcont.continuousAt hmem).continuousWithinAt
  · refine ⟨Real.exp 1 * ∑' n : ℕ, Λ n * Real.exp (-((n : ℝ) * 1)), fun t ht => ?_⟩
    have hs1 := summable_vonMangoldt_mul_exp_neg (δ := 1) one_pos
    have hst := summable_vonMangoldt_mul_exp_neg (δ := t) (by linarith)
    rw [show Real.exp 1 * (∑' n : ℕ, Λ n * Real.exp (-((n : ℝ) * 1))) *
        Real.exp (-t) = ∑' n : ℕ, Real.exp (-t) * (Real.exp 1 *
          (Λ n * Real.exp (-((n : ℝ) * 1)))) by
      rw [tsum_mul_left, tsum_mul_left]; ring]
    refine Summable.tsum_le_tsum (fun n => ?_) hst ((hs1.mul_left _).mul_left _)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [vonMangoldt_zero']
    have hp : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc Λ n * Real.exp (-((n : ℝ) * t))
        ≤ Λ n * Real.exp (-t + 1 + -((n : ℝ) * 1)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (hΛ n)
      _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-! ## Mellin transforms of `FL` and `FL²` -/

/-- The positive integers, as an index set. -/
def posNat : Set ℕ := {n | n ≠ 0}

/-- Pairs of positive integers. -/
def posPair : Set (ℕ × ℕ) := {mn | mn.1 ≠ 0 ∧ mn.2 ≠ 0}

/-- For `t > 0`, `FL t` is the sum over `n ≠ 0` of `Λ(n) e^{-nt}`, as a complex `HasSum`. -/
theorem hasSum_FL_posNat {t : ℝ} (ht : 0 < t) :
    HasSum (fun i : posNat => ((Λ (i : ℕ) : ℝ) : ℂ) * ((Real.exp (-((i : ℕ) : ℝ) * t) : ℝ) : ℂ))
      (FL t : ℂ) := by
  have h := (summable_vonMangoldt_mul_exp_neg ht).hasSum
  rw [← Complex.hasSum_ofReal] at h
  have h' : HasSum (fun n : ℕ => ((Λ n : ℝ) : ℂ) * ((Real.exp (-(n : ℝ) * t) : ℝ) : ℂ))
      (FL t : ℂ) := by
    convert h using 1
    · funext n; push_cast; ring_nf
    · rfl
  have hsupp : Function.support (fun n : ℕ => ((Λ n : ℝ) : ℂ) *
      ((Real.exp (-(n : ℝ) * t) : ℝ) : ℂ)) ⊆ posNat := by
    intro n hn
    simp only [Function.mem_support] at hn
    show n ≠ 0
    intro h0
    apply hn
    rw [h0, vonMangoldt_zero']; simp
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr h'

/-- **Mellin transform of `FL`** (no RH), in `mellin` form: `mellin FL z = Γ(z) ψ(z)` for `Re z > 1`. -/
theorem mellin_FL' {z : ℂ} (hz : 1 < z.re) :
    MellinConvergent (fun t => (FL t : ℂ)) z ∧
      mellin (fun t => (FL t : ℂ)) z = Gamma z * negLogDerivZeta z := by
  have hz0 : 0 < z.re := by linarith
  have hw : ∀ i : posNat, (0 : ℝ) < (((i : ℕ)) : ℝ) := fun i => by
    have := i.prop; exact_mod_cast Nat.pos_of_ne_zero this
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i : posNat ↦
      ((Λ (i : ℕ) : ℝ) : ℂ) * Real.exp (-(((i : ℕ)) : ℝ) * t)) (FL t : ℂ) := fun t ht ↦
    hasSum_FL_posNat (mem_Ioi.mp ht)
  have hFc : ContinuousOn (fun t => (FL t : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn FL_continuousOn_and_le_exp.1
  have hLS := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (z.re : ℂ)) (by simpa using hz)
  have h_sum : Summable fun i : posNat ↦
      ‖((Λ (i : ℕ) : ℝ) : ℂ)‖ / (((i : ℕ)) : ℝ) ^ z.re := by
    refine (hLS.norm.subtype posNat).congr fun i => ?_
    simp only [Function.comp_apply]
    rw [LSeries.norm_term_eq, if_neg i.prop]
    simp
  obtain ⟨hconv, hval⟩ := mellin_convergent_and_hasSum_of_exp hw hz0 hF hFc h_sum
  refine ⟨hconv, ?_⟩
  have hsupp : Function.support (LSeries.term (fun n => ((Λ n : ℝ) : ℂ)) z) ⊆ posNat := by
    intro n hn
    show n ≠ 0
    intro h0
    apply hn
    rw [h0, LSeries.term_zero]
  rw [← hval.tsum_eq, negLogDerivZeta_eq_LSeries hz, LSeries,
    ← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  refine tsum_congr fun i ↦ ?_
  rw [LSeries.term_of_ne_zero i.prop, ofReal_natCast, mul_div_assoc]

/-- The norm of a `Φ₂` term, for `m, n ≠ 0`. -/
theorem norm_phi2_term {s : ℂ} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ‖((Λ m : ℝ) : ℂ) * ((Λ n : ℝ) : ℂ) * (((m + n : ℕ) : ℂ)) ^ (-s)‖ =
      Λ m * Λ n / ((m : ℝ) + (n : ℝ)) ^ s.re := by
  have hpos : 0 < m + n := by omega
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hpos, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, neg_re,
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  push_cast
  ring

/-- **Mellin transform of `FL²`** (no RH): absolute convergence of `Φ₂` and `mellin FL² = Γ Φ₂` for
`Re s > 2`. -/
theorem mellin_FL_sq' {s : ℂ} (hs : 2 < s.re) :
    Summable (fun mn : ℕ × ℕ => ‖((Λ mn.1 : ℝ) : ℂ) *
      ((Λ mn.2 : ℝ) : ℂ) * (((mn.1 + mn.2 : ℕ) : ℂ)) ^ (-s)‖) ∧
    MellinConvergent (fun t => ((FL t ^ 2 : ℝ) : ℂ)) s ∧
      mellin (fun t => ((FL t ^ 2 : ℝ) : ℂ)) s = Gamma s * Phi2 s := by
  set σ := s.re with hσ
  have hs0 : 0 < σ := by linarith
  have hΛ : ∀ n : ℕ, 0 ≤ Λ n := fun n => ArithmeticFunction.vonMangoldt_nonneg
  have hpos : ∀ i : posPair, (0 : ℝ) < (((i : ℕ × ℕ).1 : ℕ) : ℝ) ∧
      (0 : ℝ) < (((i : ℕ × ℕ).2 : ℕ) : ℝ) := fun i =>
    ⟨by exact_mod_cast Nat.pos_of_ne_zero i.prop.1, by exact_mod_cast Nat.pos_of_ne_zero i.prop.2⟩
  set a : posPair → ℂ :=
    fun i => ((Λ (i : ℕ × ℕ).1 : ℝ) : ℂ) * ((Λ (i : ℕ × ℕ).2 : ℝ) : ℂ) with ha
  set w : posPair → ℝ := fun i => (((i : ℕ × ℕ).1 : ℕ) : ℝ) + (((i : ℕ × ℕ).2 : ℕ) : ℝ)
    with hwdef
  have hw : ∀ i, 0 < w i := fun i => add_pos (hpos i).1 (hpos i).2
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun i ↦ a i * Real.exp (-w i * t))
      ((FL t ^ 2 : ℝ) : ℂ) := fun t ht ↦ by
    have hf := summable_vonMangoldt_mul_exp_neg (mem_Ioi.mp ht)
    have hnn : ∀ n : ℕ, 0 ≤ Λ n * Real.exp (-((n : ℝ) * t)) := fun n =>
      mul_nonneg (hΛ n) (Real.exp_pos _).le
    have hprod := hf.hasSum.mul hf.hasSum (hf.mul_of_nonneg hf hnn hnn)
    rw [← Complex.hasSum_ofReal] at hprod
    have hsupp : Function.support (fun mn : ℕ × ℕ => ((((Λ mn.1 * Real.exp (-((mn.1 : ℝ) * t))) *
        (Λ mn.2 * Real.exp (-((mn.2 : ℝ) * t))) : ℝ)) : ℂ)) ⊆ posPair := by
      intro mn hmn
      simp only [Function.mem_support] at hmn
      refine ⟨fun h0 => hmn ?_, fun h0 => hmn ?_⟩ <;> rw [h0, vonMangoldt_zero'] <;> simp
    have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hprod
    convert hsub using 1
    · funext i
      simp only [ha, hwdef, Function.comp_apply]
      rw [show -((((i : ℕ × ℕ).1 : ℕ) : ℝ) + (((i : ℕ × ℕ).2 : ℕ) : ℝ)) * t =
        -((((i : ℕ × ℕ).1 : ℕ) : ℝ) * t) + -((((i : ℕ × ℕ).2 : ℕ) : ℝ) * t) by ring, Real.exp_add]
      push_cast
      ring
    · rw [sq]; rfl
  have hFc : ContinuousOn (fun t => ((FL t ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn (FL_continuousOn_and_le_exp.1.pow 2)
  -- `(m + n)^σ ≥ (mn)^{σ/2}`
  have key : ∀ x y : ℝ, 0 < x → 0 < y → x ^ (σ / 2) * y ^ (σ / 2) ≤ (x + y) ^ σ := by
    intro x y hx hy
    calc x ^ (σ / 2) * y ^ (σ / 2) = (x * y) ^ (σ / 2) := (Real.mul_rpow hx.le hy.le).symm
      _ ≤ ((x + y) ^ (2 : ℝ)) ^ (σ / 2) :=
          Real.rpow_le_rpow (by positivity) (by rw [Real.rpow_two]; nlinarith) (by linarith)
      _ = (x + y) ^ σ := by rw [← Real.rpow_mul (by positivity)]; ring_nf
  set g : ℕ → ℝ := fun n => Λ n / (n : ℝ) ^ (σ / 2) with hg
  have hg_sum : Summable g := by
    have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((σ / 2 : ℝ) : ℂ))
      (by simp only [ofReal_re]; linarith)).norm
    refine h.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg, vonMangoldt_zero']
    · rw [if_neg hn, Complex.norm_real, Real.norm_of_nonneg (hΛ n), ofReal_re]
  have hg_nn : 0 ≤ g := fun n => div_nonneg (hΛ n) (by positivity)
  have hgg := hg_sum.mul_of_nonneg hg_sum hg_nn hg_nn
  -- full-type summability of the norms of the `Φ₂` terms
  have hnorm : Summable (fun mn : ℕ × ℕ => ‖((Λ mn.1 : ℝ) : ℂ) *
      ((Λ mn.2 : ℝ) : ℂ) * (((mn.1 + mn.2 : ℕ) : ℂ)) ^ (-s)‖) := by
    refine hgg.of_nonneg_of_le (fun _ => norm_nonneg _) fun mn => ?_
    rcases eq_or_ne mn.1 0 with h1 | h1
    · simp only [h1, vonMangoldt_zero']; simp only [ofReal_zero, zero_mul, norm_zero]
      exact mul_nonneg (hg_nn _) (hg_nn _)
    rcases eq_or_ne mn.2 0 with h2 | h2
    · simp only [h2, vonMangoldt_zero']; simp only [ofReal_zero, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (hg_nn _) (hg_nn _)
    have hp1 : (0 : ℝ) < (mn.1 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h1
    have hp2 : (0 : ℝ) < (mn.2 : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h2
    rw [norm_phi2_term h1 h2]
    simp only [hg]
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_left (mul_nonneg (hΛ _) (hΛ _)) (by positivity) (key _ _ hp1 hp2)
  have h_sum : Summable fun i ↦ ‖a i‖ / (w i) ^ σ := by
    refine (hnorm.subtype posPair).congr fun i => ?_
    simp only [Function.comp_apply, ha, hwdef]
    rw [norm_phi2_term i.prop.1 i.prop.2, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hΛ _), Real.norm_of_nonneg (hΛ _)]
  obtain ⟨hconv, hval⟩ := mellin_convergent_and_hasSum_of_exp hw hs0 hF hFc h_sum
  refine ⟨hnorm, hconv, ?_⟩
  have hsupp : Function.support (fun mn : ℕ × ℕ => ((Λ mn.1 : ℝ) : ℂ) *
      ((Λ mn.2 : ℝ) : ℂ) * (((mn.1 + mn.2 : ℕ) : ℂ)) ^ (-s)) ⊆ posPair := by
    intro mn hmn
    simp only [Function.mem_support] at hmn
    refine ⟨fun h0 => hmn ?_, fun h0 => hmn ?_⟩ <;> rw [h0, vonMangoldt_zero'] <;> simp
  rw [← hval.tsum_eq, Phi2, ← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  refine tsum_congr fun i ↦ ?_
  have hcast : ((w i : ℝ) : ℂ) = (((((i : ℕ × ℕ).1 + (i : ℕ × ℕ).2 : ℕ)) : ℂ)) := by
    simp only [hwdef]; push_cast; ring
  rw [hcast, cpow_neg, mul_div_assoc, div_eq_mul_inv]

/-! ## Splits at `t = 1` -/

/-- On `(0, 1]` and `Re z > 1`: `hL(t) t^{z-1}` is integrable. -/
theorem integrableOn_Ioc_hL_mul_cpow {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ => (hL t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • (FL t : ℂ)) (Ioc (0 : ℝ) 1) :=
    (mellin_FL' hz).1.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 2)) (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_cpow_of_neg_one_lt (by simp; linarith)
  refine (h1.sub h2).congr_fun (fun t ht => ?_) measurableSet_Ioc
  have ht0 : 0 < t := ht.1
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hc : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ (z - 2) * t := by
    rw [← ofReal_cpow_add_one ht0]; ring_nf
  simp only [Pi.sub_apply, hL, smul_eq_mul, hc]
  push_cast
  field_simp

/-- **Split of `Γψ` at `t = 1`** (no RH): `Γ(z) ψ(z) = 1/(z-1) + m₁(z) + e₁(z)` for `Re z > 1`. -/
theorem Gamma_mul_negLogDerivZeta_split' {z : ℂ} (hz : 1 < z.re) :
    Gamma z * negLogDerivZeta z = 1 / (z - 1) + m1L z + e1L z := by
  obtain ⟨hconv, hmel⟩ := mellin_FL' hz
  rw [← hmel, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one))]
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 2)) (Ioc (0 : ℝ) 1) :=
    integrableOn_Ioc_cpow_of_neg_one_lt (by simp; linarith)
  have hI : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (z - 1) • (FL t : ℂ)
      = ∫ t in Ioc (0 : ℝ) 1, ((hL t : ℂ) * (t : ℂ) ^ (z - 1) + (t : ℂ) ^ (z - 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have hc : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ (z - 2) * t := by
      rw [← ofReal_cpow_add_one ht0]; ring_nf
    simp only [hL, smul_eq_mul, hc]
    push_cast
    field_simp
    ring
  have hE : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) • (FL t : ℂ) = e1L z := by
    simp only [e1L, smul_eq_mul, mul_comm]
  rw [hI, hE, integral_add (integrableOn_Ioc_hL_mul_cpow hz) h2,
    integral_Ioc_cpow_of_neg_one_lt (by simp; linarith)]
  simp only [m1L]
  ring_nf

/-- **Split of `ΓΦ₂` at `t = 1`** (no RH): `Γ(s) Φ₂(s) = 1/(s-2) + 2 m₁(s-1) + R(s) + E₂(s)` for `Re s > 2`, with
`R = RrL`. -/
theorem Gamma_mul_Phi2_split' {s : ℂ} (hs : 2 < s.re) :
    Gamma s * Phi2 s = 1 / (s - 2) + 2 * m1L (s - 1) + RrL s + E2L s := by
  have hpowI : ∀ r : ℂ, -1 < r.re → IntegrableOn (fun t : ℝ => (t : ℂ) ^ r) (Ioc (0 : ℝ) 1) :=
    fun r hr => integrableOn_Ioc_cpow_of_neg_one_lt hr
  have hpowV : ∀ r : ℂ, -1 < r.re → ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ r = 1 / (r + 1) :=
    fun r hr => integral_Ioc_cpow_of_neg_one_lt hr
  have hadd : ∀ t : ℝ, 0 < t → ∀ w : ℂ, (t : ℂ) ^ (w + 1) = (t : ℂ) ^ w * t :=
    fun t ht w => ofReal_cpow_add_one ht w
  have hc1 : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (s - 1 - 1) = (t : ℂ) ^ (s - 3) * t := by
    intro t ht
    rw [← hadd t ht]
    ring_nf
  have hc2 : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 3) * t * t := by
    intro t ht
    rw [← hc1 t ht, ← hadd t ht]
    ring_nf
  obtain ⟨-, hconv2, hmel2⟩ := mellin_FL_sq' hs
  have hs1 : 1 < (s - 1).re := by simp; linarith
  have hconv1 := (mellin_FL' hs1).1
  have hA : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 3)) (Ioc (0 : ℝ) 1) :=
    hpowI _ (by simp; linarith)
  have hB : IntegrableOn (fun t : ℝ => (hL t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) (Ioc (0 : ℝ) 1) := by
    refine ((hconv1.mono_set Ioc_subset_Ioi_self).sub hA).congr_fun (fun t ht => ?_)
      measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    simp only [Pi.sub_apply, hL, smul_eq_mul, hc1 t ht0]
    push_cast
    field_simp
  have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((FL t ^ 2 : ℝ) : ℂ)
      = ((hL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
        + 2 * ((hL t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) + (t : ℂ) ^ (s - 3) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    simp only [hL, smul_eq_mul, hc1 t ht0, hc2 t ht0]
    push_cast
    field_simp
    ring
  have hC : IntegrableOn (fun t : ℝ => ((hL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) := by
    refine (((hconv2.mono_set Ioc_subset_Ioi_self).sub (hB.const_mul 2)).sub hA).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply, hpt t ht]
    ring
  have hsplit : ∫ t in Ioc (0 : ℝ) 1, (((hL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
        + 2 * ((hL t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) + (t : ℂ) ^ (s - 3))
      = RrL s + 2 * m1L (s - 1) + 1 / (s - 2) := by
    have hB2 : IntegrableOn (fun t : ℝ => 2 * ((hL t : ℂ) * (t : ℂ) ^ (s - 1 - 1)))
        (Ioc (0 : ℝ) 1) := hB.const_mul 2
    have hCB : IntegrableOn (fun t : ℝ => ((hL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
        + 2 * ((hL t : ℂ) * (t : ℂ) ^ (s - 1 - 1))) (Ioc (0 : ℝ) 1) := hC.add hB2
    rw [integral_add hCB hA, integral_add hC hB2,
      integral_const_mul, hpowV _ (by simp; linarith)]
    simp only [m1L, RrL]
    ring_nf
  rw [← hmel2, mellin, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv2.mono_set Ioc_subset_Ioi_self) (hconv2.mono_set (Ioi_subset_Ioi zero_le_one)),
    setIntegral_congr_fun measurableSet_Ioc hpt, hsplit]
  have hE : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • ((FL t ^ 2 : ℝ) : ℂ) = E2L s := by
    simp only [E2L, smul_eq_mul, mul_comm]
  rw [hE]
  ring

/-! ## `e₁`, `E₂` entire -/

theorem differentiable_e1L' : Differentiable ℂ e1L := by
  obtain ⟨hc, C, hC⟩ := FL_continuousOn_and_le_exp
  refine differentiable_integral_Ioi_cpow (C := C) ?_ fun t ht => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (hc.mono fun t ht => lt_trans one_pos (mem_Ioi.mp ht))).aestronglyMeasurable measurableSet_Ioi
  · rw [Complex.norm_real, Real.norm_of_nonneg (FL_nonneg' t)]
    exact hC t (le_of_lt ht)

theorem differentiable_E2L' : Differentiable ℂ E2L := by
  obtain ⟨hc, C, hC⟩ := FL_continuousOn_and_le_exp
  refine differentiable_integral_Ioi_cpow (C := C ^ 2) ?_ fun t ht => ?_
  · exact (Complex.continuous_ofReal.comp_continuousOn
      ((hc.mono fun t ht => lt_trans one_pos (mem_Ioi.mp ht)).pow 2)).aestronglyMeasurable
      measurableSet_Ioi
  · have ht1 : 1 ≤ t := le_of_lt ht
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : FL t ^ 2 ≤ (C * Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (FL_nonneg' t) (hC t ht1) 2
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (C * Real.exp (-t)) ^ 2 = C ^ 2 * Real.exp (-t) * Real.exp (-t) := by ring
    calc FL t ^ 2 ≤ C ^ 2 * Real.exp (-t) * Real.exp (-t) := h3 ▸ h1
      _ ≤ C ^ 2 * Real.exp (-t) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ = C ^ 2 * Real.exp (-t) := mul_one _

/-! ## `ψ` on vertical lines -/

/-- `ψ` is analytic on `Re z > 1` (no RH). -/
theorem analyticAt_negLogDerivZeta_of_one_lt {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ negLogDerivZeta z :=
  analyticAt_negLogDerivZeta (fun h => by rw [h] at hz; simp at hz)
    (riemannZeta_ne_zero_of_one_le_re hz.le)

/-- Under RH, `ψ` is analytic at every `z ≠ 1` with `Re z > 1/2`: `ζ z ≠ 0` there. -/
theorem analyticAt_negLogDerivZeta_of_RH (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re)
    (hz1 : z ≠ 1) : AnalyticAt ℂ negLogDerivZeta z := by
  refine analyticAt_negLogDerivZeta hz1 fun h0 => ?_
  have htriv : ¬∃ n : ℕ, z = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at hz
    linarith
  have := hRH z h0 htriv hz1
  linarith

/-- On `Re z = σ > 1`, `Γ ψ` is integrable (no RH). -/
theorem integrable_Gamma_mul_negLogDerivZeta_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    Integrable fun y : ℝ => Gamma (σ + y * I) * negLogDerivZeta (σ + y * I) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ y : ℝ, ‖negLogDerivZeta (σ + y * I)‖ ≤ K :=
    ⟨_, fun y => norm_negLogDerivZeta_le_of_re hσ (w := σ + y * I) (by simp)⟩
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  refine integrable_Gamma_mul_of_bound (by linarith) ?_ (K := K) fun y => ?_
  · rw [continuous_iff_continuousAt]
    intro y
    have hre : 1 < ((σ : ℂ) + y * I).re := by simpa using hσ
    exact (analyticAt_negLogDerivZeta_of_one_lt hre).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  · calc ‖negLogDerivZeta (σ + y * I)‖ ≤ K := hK y
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * (1 + |y|) := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg y]) hK0

/-- Under RH, `Γ ψ` is integrable on `Re z = σ ∈ (1/2, 1)`. -/
theorem integrable_Gamma_mul_negLogDerivZeta_of_RH (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    Integrable fun y : ℝ => Gamma (σ + y * I) * negLogDerivZeta (σ + y * I) := by
  have hcont : Continuous fun y : ℝ => negLogDerivZeta (σ + y * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hre : 1 / 2 < ((σ : ℂ) + y * I).re := by simpa using hσ
    have hne : (σ : ℂ) + y * I ≠ 1 := fun h => by
      have := congrArg Complex.re h
      simp at this
      linarith
    exact (analyticAt_negLogDerivZeta_of_RH hRH hre hne).continuousAt.comp
      (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-4 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨by norm_num, by norm_num⟩)
  obtain ⟨C, hC⟩ := norm_negLogDerivZeta_le_log hRH (ε := σ - 1 / 2) (by linarith)
  refine integrable_Gamma_mul_of_bound (by linarith) hcont (K := M + |C|) fun y => ?_
  have hy0 : 0 ≤ |y| := abs_nonneg y
  rcases le_or_gt |y| 4 with hy | hy
  · have h1 := hM y ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    nlinarith [abs_nonneg C]
  · have h1 := hC (σ + y * I) (by simp) (by simp; linarith)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at h1
    have hlog0 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hlog1 : Real.log |y| ≤ 1 + |y| := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < |y|)
      linarith
    have h2 : C * Real.log |y| ≤ |C| * (1 + |y|) :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
        (mul_le_mul_of_nonneg_left hlog1 (abs_nonneg C))
    nlinarith [abs_nonneg C]

/-! ## Mellin inversion for `FL` -/

theorem FL_eq_verticalIntegral'_aux {c t : ℝ} (hc : 1 < c) (ht : 0 < t) :
    (FL t : ℂ) = VerticalIntegral' (kernelL t) c := by
  have hmel : ∀ y : ℝ, mellin (fun t => (FL t : ℂ)) (c + y * I) =
      Gamma (c + y * I) * negLogDerivZeta (c + y * I) := by
    intro y
    have hre : 1 < ((c : ℂ) + y * I).re := by simpa using hc
    rw [(mellin_FL' hre).2]
  have hconv : MellinConvergent (fun t => (FL t : ℂ)) (c : ℂ) :=
    (mellin_FL' (by simpa using hc)).1
  have hvi : VerticalIntegrable (mellin (fun t => (FL t : ℂ))) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_Gamma_mul_negLogDerivZeta_of_one_lt hc
  have hcont : ContinuousAt (fun t => (FL t : ℂ)) t :=
    continuous_ofReal.continuousAt.comp
      ((FL_continuousOn_and_le_exp.1).continuousAt (Ioi_mem_nhds ht))
  rw [← mellinInv_mellin_eq c _ ht hconv hvi hcont, mellinInv, VerticalIntegral', VerticalIntegral]
  simp_rw [hmel, kernelL, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp
  push_cast
  ring_nf
  exact mul_inv_cancel₀ hpi

/-! ## The contour shift -/

/-- `|t^{-z}| = t^{-Re z}` makes `kernelL t` integrable on any line where `Γ ψ` is. -/
theorem integrable_kernelL {σ t : ℝ} (ht : 0 < t)
    (h : Integrable fun y : ℝ => Gamma (σ + y * I) * negLogDerivZeta (σ + y * I)) :
    Integrable fun y : ℝ => kernelL t (σ + y * I) := by
  refine Integrable.mono' (h.norm.const_mul (t ^ (-σ))) ?_ (Eventually.of_forall fun y => ?_)
  · have hc : Continuous fun y : ℝ => (t : ℂ) ^ (-((σ : ℂ) + y * I)) :=
      Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast ht.ne'))
    exact hc.aestronglyMeasurable.mul h.aestronglyMeasurable
  · simp only [kernelL, norm_mul]
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp

/-- Uniform bound on the horizontal segments (RH). -/
theorem norm_kernelL_le (hRH : RiemannHypothesis) {b c t : ℝ} (hb : 1 / 2 < b) (ht : 0 < t) :
    ∃ K : ℝ, ∀ y : ℝ, 4 ≤ |y| → ∀ x ∈ Icc b c,
      ‖kernelL t (x + y * I)‖ ≤ K * (1 + |y|)⁻¹ := by
  obtain ⟨CΓ, hCΓ⟩ := norm_Gamma_mul_one_add_abs_im_pow_le (a := b) (a' := c) (by linarith) 2
  obtain ⟨C, hC⟩ := norm_negLogDerivZeta_le_log hRH (ε := b - 1 / 2) (by linarith)
  refine ⟨(t ^ (-b) + t ^ (-c)) * |C| * CΓ, fun y hy x hx => ?_⟩
  have hpos : 0 < 1 + |y| := by positivity
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  have hT : ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ ≤ t ^ (-b) + t ^ (-c) := by
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp only [neg_re, hre]
    have h1 : 0 ≤ t ^ (-b) := Real.rpow_nonneg ht.le _
    have h2 : 0 ≤ t ^ (-c) := Real.rpow_nonneg ht.le _
    rcases le_or_gt 1 t with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show -x ≤ -b by linarith [hx.1])
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge ht h.le (show -c ≤ -x by linarith [hx.2])
      linarith
  have hG := hCΓ (x + y * I) (by rw [hre]; exact hx.1) (by rw [hre]; exact hx.2)
  rw [him] at hG
  have hQ : ‖negLogDerivZeta (x + y * I)‖ ≤ |C| * (1 + |y|) := by
    have h1 := hC (x + y * I) (by rw [hre]; linarith [hx.1]) (by rw [him]; exact hy)
    rw [him] at h1
    have hlog0 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hlog1 : Real.log |y| ≤ 1 + |y| := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < |y|)
      linarith
    exact h1.trans (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
      (mul_le_mul_of_nonneg_left hlog1 (abs_nonneg C)))
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  simp only [kernelL, norm_mul]
  have hT0 : 0 ≤ t ^ (-b) + t ^ (-c) := by positivity
  calc ‖(t : ℂ) ^ (-((x : ℂ) + y * I))‖ * (‖Gamma (x + y * I)‖ *
        ‖negLogDerivZeta (x + y * I)‖) * (1 + |y|)
      ≤ (t ^ (-b) + t ^ (-c)) * (‖Gamma (x + y * I)‖ * (|C| * (1 + |y|))) * (1 + |y|) := by
        gcongr
    _ = (t ^ (-b) + t ^ (-c)) * |C| * (‖Gamma (x + y * I)‖ * (1 + |y|) ^ 2) := by ring
    _ ≤ (t ^ (-b) + t ^ (-c)) * |C| * CΓ :=
        mul_le_mul_of_nonneg_left hG (mul_nonneg hT0 (abs_nonneg C))

/-- The horizontal integrals tend to `0` (RH). -/
theorem tendsto_integral_kernelL_horizontal (hRH : RiemannHypothesis) {b c t : ℝ} (hb : 1 / 2 < b)
    (hbc : b ≤ c) (ht : 0 < t) {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) :
    Tendsto (fun y : ℝ => ∫ x in b..c, kernelL t (x + y * I)) l (𝓝 0) := by
  obtain ⟨K, hK⟩ := norm_kernelL_le hRH (c := c) hb ht
  have hlim : Tendsto (fun y : ℝ => K * (1 + |y|)⁻¹ * |c - b|) l (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (1 + |y|)⁻¹) l (𝓝 0) :=
      (tendsto_atTop_add_const_left _ 1 hl).inv_tendsto_atTop
    simpa using (h1.const_mul K).mul_const |c - b|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hl.eventually (eventually_ge_atTop 4)] with y hy
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [uIoc_of_le hbc] at hx
  exact hK y hy x ⟨le_of_lt hx.1, hx.2⟩

/-- Near `z = 1`, `kernelL t - (1/t)/(z - 1)` is bounded, by `hasResidue_negLogDerivZeta_one`. -/
theorem kernelL_sub_pole_isBigO {t : ℝ} (ht : 0 < t) :
    (kernelL t - fun s => 1 / (t : ℂ) / (s - 1)) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) := by
  have hm : MeromorphicAt negLogDerivZeta 1 := meromorphicAt_negLogDerivZeta 1
  have hord := hasResidue_negLogDerivZeta_one.meromorphicOrderAt_eq_neg_one hm one_ne_zero
  obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hm).mp hord
  have hg1 : g 1 = 1 := by
    have h1 : Tendsto g (𝓝[≠] (1 : ℂ)) (𝓝 (g 1)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto g (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
      refine (hasResidue_negLogDerivZeta_one : Tendsto _ _ _).congr' ?_
      filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz1
      have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      rw [hz, smul_eq_mul, zpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hz1', one_mul]
    exact tendsto_nhds_unique h1 h2
  set φ : ℂ → ℂ := fun z => (t : ℂ) ^ (-z) * Gamma z * g z with hφdef
  have hφd : DifferentiableAt ℂ φ 1 :=
    ((differentiableAt_ofReal_cpow_neg ht 1).mul
      (differentiableAt_Gamma_of_re_pos (by norm_num))).mul hg.differentiableAt
  have hφ1 : φ 1 = 1 / (t : ℂ) := by
    simp only [hφdef, cpow_neg_one, Gamma_one, hg1, mul_one, one_div]
  have hB : (dslope φ 1) =O[𝓝[≠] (1 : ℂ)] (1 : ℂ → ℂ) :=
    ((continuousAt_dslope_same.mpr hφd).tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds
  refine hB.congr' ?_ EventuallyEq.rfl
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hz1
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [dslope_of_ne _ hz1, slope_def_field, hφ1]
  simp only [Pi.sub_apply, kernelL, hz, smul_eq_mul, zpow_neg_one, hφdef]
  field_simp

/-- **The contour shift** (RH): for `1/2 < b < 1 < c` and `t > 0`, moving the line of integration of `kernelL t`
from `Re w = c` to `Re w = b` crosses only the pole `w = 1`, with residue `1/t`. -/
theorem verticalIntegral'_kernelL_shift' (hRH : RiemannHypothesis) {b c t : ℝ}
    (hb : 1 / 2 < b) (hb1 : b < 1) (hc : 1 < c) (ht : 0 < t) :
    VerticalIntegral' (kernelL t) c = 1 / (t : ℂ) + VerticalIntegral' (kernelL t) b := by
  have hbc : b ≤ c := by linarith
  refine verticalIntegral'_eq_add_of_simplePole (p := 1) (A := 1 / (t : ℂ))
    ⟨by simpa using hb1, by simpa using hc⟩ ?_ (kernelL_sub_pole_isBigO ht)
    (tendsto_integral_kernelL_horizontal hRH hb hbc ht tendsto_abs_atBot_atTop)
    (tendsto_integral_kernelL_horizontal hRH hb hbc ht tendsto_abs_atTop_atTop)
    (integrable_kernelL ht (integrable_Gamma_mul_negLogDerivZeta_of_RH hRH hb hb1))
    (integrable_kernelL ht (integrable_Gamma_mul_negLogDerivZeta_of_one_lt hc))
  rintro z ⟨hz, hz1⟩
  have hzre : z.re ∈ Icc b c := (mem_reProdIm.mp hz).1
  have hz1' : z ≠ 1 := hz1
  have hre : 1 / 2 < z.re := by linarith [hzre.1]
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (fun z : ℂ => (t : ℂ) ^ (-z) * (Gamma z * negLogDerivZeta z)) z
  exact (differentiableAt_ofReal_cpow_neg ht z).mul
    ((differentiableAt_Gamma_of_re_pos (by linarith)).mul
      (analyticAt_negLogDerivZeta_of_RH hRH hre hz1').differentiableAt)

/-! ## `hL = O(t^{-b})` -/

theorem norm_verticalIntegral'_kernelL_le (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 / 2 < b)
    (hb1 : b < 1) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖VerticalIntegral' (kernelL t) b‖ ≤ C * t ^ (-b) := by
  have hint := integrable_Gamma_mul_negLogDerivZeta_of_RH hRH hb hb1
  set g : ℝ → ℂ := fun y => Gamma (b + y * I) * negLogDerivZeta (b + y * I) with hg
  refine ⟨(1 / (2 * Real.pi)) * ∫ y, ‖g y‖, fun t ht => ?_⟩
  have hnorm : ∀ y : ℝ, ‖kernelL t (b + y * I)‖ = t ^ (-b) * ‖g y‖ := by
    intro y
    simp only [kernelL, norm_mul, hg]
    rw [norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  calc ‖VerticalIntegral' (kernelL t) b‖
      = ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ * ‖∫ y : ℝ, kernelL t (b + y * I)‖ := by
        simp only [VerticalIntegral', VerticalIntegral, norm_smul]; ring
    _ ≤ 1 / (2 * Real.pi) * ∫ y : ℝ, ‖kernelL t (b + y * I)‖ := by
        rw [hI]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = 1 / (2 * Real.pi) * (t ^ (-b) * ∫ y : ℝ, ‖g y‖) := by
        rw [integral_congr_ae (Eventually.of_forall hnorm), integral_const_mul]
    _ = 1 / (2 * Real.pi) * (∫ y, ‖g y‖) * t ^ (-b) := by ring

theorem continuousOn_hL' : ContinuousOn hL (Ioi 0) :=
  FL_continuousOn_and_le_exp.1.sub
    (continuousOn_const.div continuousOn_id fun _ ht => (ne_of_gt (mem_Ioi.mp ht)))

theorem norm_hL_le' (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → |hL t| ≤ C * t ^ (-b) := by
  obtain ⟨C, hC⟩ := norm_verticalIntegral'_kernelL_le hRH hb hb1
  refine ⟨C, fun t ht => ?_⟩
  have h1 := FL_eq_verticalIntegral'_aux (c := 2) (by norm_num) ht
  have h2 := verticalIntegral'_kernelL_shift' hRH hb hb1 (by norm_num : (1 : ℝ) < 2) ht
  have heq : ((hL t : ℝ) : ℂ) = VerticalIntegral' (kernelL t) b := by
    simp only [hL]
    push_cast
    rw [h1, h2]
    ring
  have := hC t ht
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-! ## The `Φ₂` identity

Eliminate `m₁(s-1)` between the two splits and divide by `Γ(s) = (s-1)Γ(s-1)`. -/

theorem phi2_identity' {s : ℂ} (hs : 2 < s.re) : Phi2 s = phi2Main s + Hphi2 s := by
  have hs1 : 1 < (s - 1).re := by simp; linarith
  have hS1 := Gamma_mul_negLogDerivZeta_split' hs1
  have hS2 := Gamma_mul_Phi2_split' hs
  have hs10 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs20 : s - 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hΓ : Gamma s = (s - 1) * Gamma (s - 1) := by
    have := Gamma_add_one (s - 1) hs10
    rwa [sub_add_cancel] at this
  have hΓ1 : Gamma (s - 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓs : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hm : m1L (s - 1) = Gamma (s - 1) * negLogDerivZeta (s - 1) - 1 / (s - 2) - e1L (s - 1) := by
    rw [show s - 1 - 1 = s - 2 by ring] at hS1
    linear_combination -hS1
  have hT : Phi2 s = (Gamma s)⁻¹ * (Gamma s * Phi2 s) := by field_simp
  show Phi2 s = 2 * negLogDerivZeta (s - 1) / (s - 1) - 1 / (Gamma s * (s - 2)) +
    (E2L s - 2 * e1L (s - 1) + RrL s) * (Gamma s)⁻¹
  rw [hT, hS2, hm, hΓ]
  field_simp
  ring

end GoldbachBoundaries.Phi2Proof.FillA
