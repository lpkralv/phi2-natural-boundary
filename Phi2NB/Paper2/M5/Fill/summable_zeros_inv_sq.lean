import Phi2NB.Paper2.Defs
import Phi2NB.Defs
import Phi2NB.ZetaRealNonvanishing
import Phi2NB.SigmaFinite
import Phi2NB.SigmaMeromorphic
import Phi2NB.TIdentity.Assembly
import Phi2NB.Density
import Phi2NB.TBoundary
import Mathlib.MeasureTheory.Group.Prod
import Phi2NB.TIdentity.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.Module.Cardinality
import Phi2NB.Paper2.M1.Fill.BCommon
import Phi2NB.TIdentity.G8d_ContourShift
import Phi2NB.Paper2.M1.Fill.sum_zetaMult_window_le
import Phi2NB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles
import Phi2NB.Paper2.M2.Fill.ncard_zeros_im_Icc_le
import Phi2NB.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.Paper2.M2.Fill.ACommon
import PrimeNumberTheoremAnd.Consequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Phi2NB.Paper2.M4b.Fill.BCommon
import Phi2NB.Paper2.M4b.Fill.isBigO_mul_sub_residue
import Phi2NB.Paper2.M5.Fill.order_residue_of_codiscrete_line
import Phi2NB.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep
import Phi2NB.Paper2.M5.Fill.exists_sep_height
import Phi2NB.Paper2.M5.Fill.QCommon

/-!
# `∑_ρ (1 + |γ|)^{-2} < ∞`

Group the zeros by `⌊γ⌋ = n ∈ ℤ` (`Equiv.sigmaFiberEquiv`). Each fibre lies in `{n ≤ γ ≤ n + 1}`, which
`ncard_zeros_im_Icc_le` (`L = 1`) bounds by `C log(|n| + 4)`; on it `1 + |γ| ≥ (1 + |n|)/2`. So the fibre sums are
`≤ 4C log(|n| + 4)/(1 + |n|)²`, which is `≤ K|n|^{-3/2}` for `n ≠ 0` (`log x ≤ 2√x`), summable over `ℤ`
(`Real.summable_abs_int_rpow`). `summable_sigma_of_nonneg` concludes.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem summable_zeros_inv_sq (hZ1 : ZeroSymmetry) (hRvM : RiemannVonMangoldt) :
    Summable (fun ρ : NontrivialZeros => 1 / (1 + |(ρ : ℂ).im|) ^ 2) := by
  obtain ⟨C, hC⟩ := M2.ncard_zeros_im_Icc_le hZ1 hRvM
  set f : NontrivialZeros → ℝ := fun ρ => 1 / (1 + |(ρ : ℂ).im|) ^ 2 with hf
  have hf0 : ∀ ρ, 0 ≤ f ρ := fun ρ => by positivity
  set φ : NontrivialZeros → ℤ := fun ρ => ⌊(ρ : ℂ).im⌋ with hφ
  -- the fibre sets
  set S : ℤ → Set ℂ := fun n => {ρ : ℂ | ρ ∈ NontrivialZeros ∧ (n : ℝ) ≤ ρ.im ∧ ρ.im ≤ n + 1}
    with hS
  have hSfin : ∀ n : ℤ, (S n).Finite := fun n => by
    have h := (hC n 1 le_rfl).1
    simp only [Nat.cast_one] at h
    exact h
  have hScard : ∀ n : ℤ, ((S n).ncard : ℝ) ≤ C * Real.log (|(n : ℝ)| + 4) := by
    intro n
    have h := (hC n 1 le_rfl).2
    simp only [Nat.cast_one, mul_one] at h ⊢
    have : |(n : ℝ)| + 1 + 3 = |(n : ℝ)| + 4 := by ring
    rw [this] at h
    change (({ρ : ℂ | ρ ∈ NontrivialZeros ∧ (n : ℝ) ≤ ρ.im ∧ ρ.im ≤ n + 1}).ncard : ℝ) ≤ _
    exact h
  let ι : ∀ n : ℤ, {ρ : NontrivialZeros // φ ρ = n} → S n := fun n y =>
    ⟨(y.1 : ℂ), y.1.2, by
      have h1 := Int.floor_le (y.1 : ℂ).im
      have h2 := Int.lt_floor_add_one (y.1 : ℂ).im
      have hy : φ y.1 = n := y.2
      simp only [hφ] at hy
      rw [hy] at h1 h2
      exact ⟨h1, h2.le⟩⟩
  have hι : ∀ n, Function.Injective (ι n) := by
    intro n a b hab
    have := congrArg (fun x : S n => (x : ℂ)) hab
    exact Subtype.ext (Subtype.ext this)
  have hfinF : ∀ n : ℤ, Finite {ρ : NontrivialZeros // φ ρ = n} := fun n =>
    haveI := (hSfin n).to_subtype
    Finite.of_injective (ι n) (hι n)
  have hcard : ∀ n : ℤ, (Nat.card {ρ : NontrivialZeros // φ ρ = n} : ℝ) ≤
      C * Real.log (|(n : ℝ)| + 4) := by
    intro n
    have := (hSfin n).to_subtype
    have h1 := Nat.card_le_card_of_injective (ι n) (hι n)
    rw [Nat.card_coe_set_eq] at h1
    exact (Nat.cast_le.mpr h1).trans (hScard n)
  have hpt : ∀ n : ℤ, ∀ y : {ρ : NontrivialZeros // φ ρ = n}, f y.1 ≤ 4 / (1 + |(n : ℝ)|) ^ 2 := by
    intro n y
    have h1 := Int.floor_le (y.1 : ℂ).im
    have h2 := Int.lt_floor_add_one (y.1 : ℂ).im
    have hy : φ y.1 = n := y.2
    simp only [hφ] at hy
    rw [hy] at h1 h2
    set γ : ℝ := (y.1 : ℂ).im
    have hlow : (1 + |(n : ℝ)|) / 2 ≤ 1 + |γ| := by
      rcases le_or_gt 0 n with hn | hn
      · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
        rw [abs_of_nonneg hn', abs_of_nonneg (hn'.trans h1)]
        linarith
      · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
        rw [abs_of_neg (by linarith : (n : ℝ) < 0), abs_of_neg (by linarith : γ < 0)]
        linarith
    have hp : 0 < (1 + |(n : ℝ)|) / 2 := by positivity
    show 1 / (1 + |γ|) ^ 2 ≤ 4 / (1 + |(n : ℝ)|) ^ 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul hlow hlow hp.le (by positivity : (0 : ℝ) ≤ 1 + |γ|)]
  rw [← (Equiv.sigmaFiberEquiv φ).summable_iff]
  show Summable (fun x => f ((Equiv.sigmaFiberEquiv φ) x))
  rw [summable_sigma_of_nonneg (fun x => hf0 _)]
  refine ⟨fun n => ?_, ?_⟩
  · have := hfinF n
    exact Summable.of_finite
  · -- the fibre sums
    have hfib : ∀ n : ℤ, ∑' y : {ρ : NontrivialZeros // φ ρ = n}, f ((Equiv.sigmaFiberEquiv φ) ⟨n, y⟩) ≤
        C * Real.log (|(n : ℝ)| + 4) * (4 / (1 + |(n : ℝ)|) ^ 2) := by
      intro n
      have := hfinF n
      calc ∑' y : {ρ : NontrivialZeros // φ ρ = n}, f ((Equiv.sigmaFiberEquiv φ) ⟨n, y⟩)
          ≤ ∑' _ : {ρ : NontrivialZeros // φ ρ = n}, 4 / (1 + |(n : ℝ)|) ^ 2 :=
            Summable.tsum_le_tsum (fun y => hpt n y) Summable.of_finite Summable.of_finite
        _ = (Nat.card {ρ : NontrivialZeros // φ ρ = n} : ℝ) * (4 / (1 + |(n : ℝ)|) ^ 2) := by
            rw [tsum_const, nsmul_eq_mul]
        _ ≤ _ := by gcongr; exact hcard n
    have hnn : ∀ n : ℤ, 0 ≤ ∑' y : {ρ : NontrivialZeros // φ ρ = n}, f ((Equiv.sigmaFiberEquiv φ) ⟨n, y⟩) :=
      fun n => tsum_nonneg fun y => hf0 _
    -- comparison with `|n|^{-3/2}`
    have hsum : Summable fun n : ℤ => (24 * |C|) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
      (Real.summable_abs_int_rpow (by norm_num)).mul_left _
    refine Summable.of_norm_bounded_eventually hsum ?_
    have hfin0 : ({0} : Set ℤ).Finite := Set.finite_singleton 0
    filter_upwards [hfin0.compl_mem_cofinite] with n hn
    have hn0 : n ≠ 0 := hn
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    set a : ℝ := |(n : ℝ)| with ha
    have ha0 : 0 < a := by linarith
    rw [Real.norm_of_nonneg (hnn n)]
    refine (hfib n).trans ?_
    -- `log(a + 4) ≤ 2 (a + 4)^{1/2} ≤ 2 √5 a^{1/2} ≤ 6 a^{1/2}`
    have hlog : Real.log (a + 4) ≤ 6 * a ^ (1 / 2 : ℝ) := by
      have h1 := Real.log_le_rpow_div (x := a + 4) (by linarith) (ε := 1 / 2) (by norm_num)
      have h2 : (a + 4) ^ (1 / 2 : ℝ) ≤ (5 * a) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have h3 : (5 * a) ^ (1 / 2 : ℝ) = (5 : ℝ) ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) :=
        Real.mul_rpow (by norm_num) ha0.le
      have h4 : (5 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
      have h5 : 0 ≤ a ^ (1 / 2 : ℝ) := Real.rpow_nonneg ha0.le _
      calc Real.log (a + 4) ≤ (a + 4) ^ (1 / 2 : ℝ) / (1 / 2) := h1
        _ = 2 * (a + 4) ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * ((5 : ℝ) ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ)) := by rw [← h3]; gcongr
        _ ≤ 2 * (3 * a ^ (1 / 2 : ℝ)) := by gcongr
        _ = 6 * a ^ (1 / 2 : ℝ) := by ring
    have hlog0 : 0 ≤ Real.log (a + 4) := Real.log_nonneg (by linarith)
    have hpow : a ^ (1 / 2 : ℝ) / a ^ (2 : ℝ) = a ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_sub ha0]; norm_num
    have hsq : a ^ (2 : ℝ) ≤ (1 + a) ^ 2 := by
      rw [Real.rpow_two]; nlinarith
    have ha2 : 0 < a ^ (2 : ℝ) := Real.rpow_pos_of_pos ha0 _
    calc C * Real.log (a + 4) * (4 / (1 + a) ^ 2)
        ≤ |C| * Real.log (a + 4) * (4 / (1 + a) ^ 2) := by
          gcongr; exact le_abs_self C
      _ ≤ |C| * (6 * a ^ (1 / 2 : ℝ)) * (4 / a ^ (2 : ℝ)) := by
          gcongr
      _ = (24 * |C|) * (a ^ (1 / 2 : ℝ) / a ^ (2 : ℝ)) := by ring
      _ = (24 * |C|) * a ^ (-(3 / 2 : ℝ)) := by rw [hpow]

end GoldbachBoundaries.Paper2.M5
