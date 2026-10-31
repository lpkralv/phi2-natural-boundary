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

/-! A height far from the ordinates: `exists_sep_height`. The measure argument: for `n ≤ 3` only ordinates in
`[nY - 1, nY + 4]` can come within `1` of `nY'`, `Y' ∈ [Y, Y + 1]`; `ncard_zeros_im_Icc_le` (`L = 5`) counts them
by `5 C₂ log(nY + 7) ≤ 15 C₂ log Y`. The bad set `⋃_n ⋃_γ ((γ - δ)/n, (γ + δ)/n)` has volume `≤ 90 C₂ δ log Y < 1`
for `δ = 1/(1 + (90 C₂ + 1) log Y)`, so it does not cover `[Y, Y + 1]`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **A height `Y'` with `|nY' - γ| ≥ δ(Y)` for every ordinate `γ` and `1 ≤ n ≤ 3`**, so `Y'` is at distance
`≥ δ(Y)/n` from every `γ/n` ((ZeroSymmetry), (RiemannVonMangoldt)). -/
theorem exists_sep_height (hZ1 : ZeroSymmetry) (hRvM : RiemannVonMangoldt) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 3 ≤ Y → ∃ Y' ∈ Icc Y (Y + 1), ∀ n : ℕ, 1 ≤ n → n ≤ 3 →
      ∀ ρ ∈ NontrivialZeros, 1 / (1 + C * Real.log Y) ≤ |(n : ℝ) * Y' - ρ.im| := by
  classical
  obtain ⟨C₂, hC₂⟩ := M2.ncard_zeros_im_Icc_le hZ1 hRvM
  set D := max C₂ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  refine ⟨90 * D + 1, by positivity, fun Y hY => ?_⟩
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set δ := 1 / (1 + (90 * D + 1) * L) with hδdef
  have hden : 0 < 1 + (90 * D + 1) * L := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδmul : δ * (1 + (90 * D + 1) * L) = 1 := by rw [hδdef]; field_simp
  have hδ1 : δ ≤ 1 := by nlinarith
  -- the windows
  set Z : ℕ → Set ℂ := fun n =>
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ (n : ℝ) * Y - 1 ≤ ρ.im ∧ ρ.im ≤ (n : ℝ) * Y - 1 + ((5 : ℕ) : ℝ)} with hZdef
  have hZfin : ∀ n, (Z n).Finite := fun n => (hC₂ ((n : ℝ) * Y - 1) 5 (by norm_num)).1
  have hZcard : ∀ n : ℕ, 1 ≤ n → n ≤ 3 → ((hZfin n).toFinset.card : ℝ) ≤ 15 * D * L := by
    intro n hn1 hn3
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn3' : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
    have h := (hC₂ ((n : ℝ) * Y - 1) 5 (by norm_num)).2
    rw [← Set.ncard_eq_toFinset_card _ (hZfin n)]
    have habs : |(n : ℝ) * Y - 1| = (n : ℝ) * Y - 1 := abs_of_nonneg (by nlinarith)
    have hpos : 0 < |(n : ℝ) * Y - 1| + ((5 : ℕ) : ℝ) + 3 := by positivity
    have hlog : Real.log (|(n : ℝ) * Y - 1| + ((5 : ℕ) : ℝ) + 3) ≤ 3 * L := by
      rw [hLdef, show (3 : ℝ) * Real.log Y = Real.log (Y ^ 3) by rw [Real.log_pow]; push_cast; ring]
      refine Real.log_le_log hpos ?_
      rw [habs]
      push_cast
      have hY2 : 9 ≤ Y ^ 2 := by nlinarith
      have : 9 * Y ≤ Y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hY2 (by linarith : (0 : ℝ) ≤ Y)]
      nlinarith
    have hlog0 : 0 ≤ Real.log (|(n : ℝ) * Y - 1| + ((5 : ℕ) : ℝ) + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg ((n : ℝ) * Y - 1)])
    calc ((Z n).ncard : ℝ) ≤ C₂ * ((5 : ℕ) : ℝ) * Real.log (|(n : ℝ) * Y - 1| + ((5 : ℕ) : ℝ) + 3) := h
      _ ≤ D * 5 * (3 * L) := by
          push_cast
          gcongr
          · exact le_max_left _ _
          · simpa using hlog
      _ = 15 * D * L := by ring
  -- the bad set
  set I : ℕ → ℂ → Set ℝ := fun n ρ => Ioo ((ρ.im - δ) / n) ((ρ.im + δ) / n) with hIdef
  set Bad : Set ℝ := ⋃ n ∈ Finset.Icc 1 3, ⋃ ρ ∈ (hZfin n).toFinset, I n ρ with hBaddef
  have hsumle : ∑ n ∈ Finset.Icc 1 3, ∑ ρ ∈ (hZfin n).toFinset, 2 * δ / (n : ℝ) ≤ 90 * D * δ * L := by
    calc ∑ n ∈ Finset.Icc 1 3, ∑ ρ ∈ (hZfin n).toFinset, 2 * δ / (n : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 3, 15 * D * L * (2 * δ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [Finset.mem_Icc] at hn
          have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
          rw [Finset.sum_const, nsmul_eq_mul]
          have h2 : 2 * δ / (n : ℝ) ≤ 2 * δ := div_le_self (by positivity) hn1'
          have h3 := hZcard n hn.1 hn.2
          have h4 : 0 ≤ 2 * δ / (n : ℝ) := by positivity
          calc ((hZfin n).toFinset.card : ℝ) * (2 * δ / n) ≤ 15 * D * L * (2 * δ / n) :=
                mul_le_mul_of_nonneg_right h3 h4
            _ ≤ 15 * D * L * (2 * δ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 90 * D * δ * L := by
          rw [Finset.sum_const]
          simp
          ring
  have hlt : 90 * D * δ * L < 1 := by nlinarith
  have hvol : volume Bad < volume (Icc Y (Y + 1)) := by
    rw [Real.volume_Icc, show Y + 1 - Y = 1 by ring]
    calc volume Bad ≤ ∑ n ∈ Finset.Icc 1 3, volume (⋃ ρ ∈ (hZfin n).toFinset, I n ρ) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 3, ∑ ρ ∈ (hZfin n).toFinset, volume (I n ρ) :=
          Finset.sum_le_sum fun n _ => measure_biUnion_finset_le _ _
      _ = ∑ n ∈ Finset.Icc 1 3, ∑ ρ ∈ (hZfin n).toFinset, ENNReal.ofReal (2 * δ / (n : ℝ)) := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun ρ _ => ?_
          rw [hIdef, Real.volume_Ioo]
          congr 1
          ring
      _ = ENNReal.ofReal (∑ n ∈ Finset.Icc 1 3, ∑ ρ ∈ (hZfin n).toFinset, 2 * δ / (n : ℝ)) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun n _ => Finset.sum_nonneg fun ρ _ => by positivity]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun ρ _ => by positivity]
      _ < ENNReal.ofReal 1 := by
          rw [ENNReal.ofReal_lt_ofReal_iff one_pos]
          linarith
  have hnot : ¬ Icc Y (Y + 1) ⊆ Bad := fun h => (measure_mono h).not_gt hvol
  obtain ⟨Y', hY'mem, hY'bad⟩ := Set.not_subset.mp hnot
  refine ⟨Y', hY'mem, fun n hn1 hn3 ρ hρ => ?_⟩
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn3' : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
  have hnY1 : (n : ℝ) * Y ≤ n * Y' := mul_le_mul_of_nonneg_left hY'mem.1 (by linarith)
  have hnY2 : (n : ℝ) * Y' ≤ n * Y + 3 := by nlinarith [hY'mem.2]
  show δ ≤ _
  by_cases hZ : ρ ∈ Z n
  · have hnotI : Y' ∉ I n ρ := by
      intro hI
      apply hY'bad
      rw [hBaddef]
      simp only [Set.mem_iUnion]
      exact ⟨n, Finset.mem_Icc.mpr ⟨hn1, hn3⟩, ρ, (Set.Finite.mem_toFinset _).mpr hZ, hI⟩
    rw [hIdef] at hnotI
    simp only [Set.mem_Ioo, not_and_or, not_lt] at hnotI
    have hnpos : (0 : ℝ) < n := by linarith
    rcases hnotI with h | h
    · rw [le_div_iff₀ hnpos] at h
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    · rw [div_le_iff₀ hnpos] at h
      exact le_trans (by linarith) (le_abs_self _)
  · have hout : ρ.im < (n : ℝ) * Y - 1 ∨ (n : ℝ) * Y - 1 + ((5 : ℕ) : ℝ) < ρ.im := by
      by_contra hc
      push Not at hc
      exact hZ ⟨hρ, hc.1, hc.2⟩
    push_cast at hout
    rcases hout with h | h
    · exact le_trans hδ1 (le_trans (by linarith) (le_abs_self _))
    · rw [abs_sub_comm]
      exact le_trans hδ1 (le_trans (by linarith) (le_abs_self _))

end GoldbachBoundaries.Paper2.M5
