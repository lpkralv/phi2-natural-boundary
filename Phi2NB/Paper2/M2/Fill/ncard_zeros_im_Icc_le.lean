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
import Phi2NB.Paper2.M2.Fill.ACommon

noncomputable section
open Complex Set
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Distinct zeros in a horizontal strip** (ZeroSymmetry, RiemannVonMangoldt): for an integer `L ≥ 1`, the zeros with `t ≤ γ ≤ t + L` are
finitely many and at most `C L log(|t| + L + 3)`. Cover `[t, t + L]` by the `L` windows `|γ - (t + j)| ≤ 1`,
`j = 0, …, L - 1` (each `γ ∈ [t + j, t + j + 1]` is within `1` of `t + j`); each window is finite with total
multiplicity `≤ C log(|t + j| + 3) ≤ C log(|t| + L + 3)` (`sum_zetaMult_window_le`); the number of distinct zeros is
at most the total multiplicity, since `m(ρ) ≥ 1` at every zero, and the size of a finite union is at most the sum of
the sizes. `C ≥ 0`. -/
theorem ncard_zeros_im_Icc_le (hZ1 : ZeroSymmetry) (hRvM : RiemannVonMangoldt) :
    ∃ C : ℝ, ∀ t : ℝ, ∀ L : ℕ, 1 ≤ L →
      {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L}.Finite ∧
      ({ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L}.ncard : ℝ) ≤
        C * L * Real.log (|t| + L + 3) := by
  classical
  obtain ⟨C, hC⟩ := sum_zetaMult_window_le hZ1 hRvM
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hw : ∀ t : ℝ, wsumB {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im - t| ≤ 1} ≤
      D * Real.log (|t| + 3) := fun t =>
    (hC t).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.log_nonneg (by linarith [abs_nonneg t])))
  have hb : ∀ L : ℕ, ∀ t : ℝ,
      wsumB {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L} ≤
        D * (L + 1) * Real.log (|t| + L + 3) := by
    intro L
    induction L with
    | zero =>
      intro t
      have hsub : {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + (0 : ℕ)} ⊆
          {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im - t| ≤ 1} := by
        rintro ρ ⟨hz, hl, hu⟩
        refine ⟨hz, abs_le.mpr ?_⟩
        simp only [Nat.cast_zero, add_zero] at hu
        constructor <;> linarith
      simpa using (wsumB_mono (hC t).1 hsub).trans (hw t)
    | succ L ih =>
      intro t
      let S := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L}
      let W := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - (t + L)| ≤ 1}
      have hsub : {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + (L + 1 : ℕ)} ⊆ S ∪ W := by
        rintro ρ ⟨hz, hl, hu⟩
        by_cases h : ρ.im ≤ t + L
        · exact Or.inl ⟨hz, hl, h⟩
        · right
          refine ⟨hz, abs_le.mpr ?_⟩
          push_cast at hu
          constructor <;> linarith
      have hlog : Real.log (|t| + L + 3) ≤ Real.log (|t| + (L + 1 : ℕ) + 3) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      have hlog' : Real.log (|t + L| + 3) ≤ Real.log (|t| + (L + 1 : ℕ) + 3) := by
        apply Real.log_le_log (by positivity)
        have := abs_add_le t (L : ℝ)
        rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) L)] at this
        push_cast
        linarith
      calc _ ≤ wsumB (S ∪ W) := wsumB_mono ((A_finite_strip t L).union (hC (t + L)).1) hsub
        _ ≤ wsumB S + wsumB W := wsumB_union_le (A_finite_strip t L) (hC (t + L)).1
        _ ≤ D * (L + 1) * Real.log (|t| + L + 3) + D * Real.log (|t + L| + 3) :=
          add_le_add (ih t) (hw (t + L))
        _ ≤ _ := by
          have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ D * (L + 1))
          have h2 := mul_le_mul_of_nonneg_left hlog' hD
          push_cast at *
          nlinarith
  refine ⟨2 * D, fun t L hL => ⟨A_finite_strip t L, ?_⟩⟩
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hl : 0 ≤ Real.log (|t| + L + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  calc _ ≤ wsumB {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L} :=
      A_ncard_le_weight (A_finite_strip t L) fun _ h => h.1
    _ ≤ D * (L + 1) * Real.log (|t| + L + 3) := hb L t
    _ ≤ _ := by nlinarith [mul_nonneg hD hl]
end GoldbachBoundaries.Paper2.M2
