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

noncomputable section
open Complex Set
namespace GoldbachBoundaries.Paper2.M2
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Multiplicity bound** (ZeroSymmetry, RiemannVonMangoldt): `m(ρ) ≤ C log(|γ| + 3)`. Apply `sum_zetaMult_window_le` with `t = γ`: `ρ` lies
in the finite window `{ρ' : |γ' - γ| ≤ 1}`, and one term of a finite sum of non-negative terms is at most the sum
(`finsum_mem_eq_finite_toFinset_sum`, `Finset.single_le_sum`). -/
theorem zetaMult_le_log (hZ1 : ZeroSymmetry) (hRvM : RiemannVonMangoldt) :
    ∃ C : ℝ, ∀ ρ ∈ NontrivialZeros, (zetaMult ρ : ℝ) ≤ C * Real.log (|ρ.im| + 3) := by
  classical
  obtain ⟨C, hC⟩ := sum_zetaMult_window_le hZ1 hRvM
  refine ⟨C, fun ρ hρ => ?_⟩
  obtain ⟨hf, hb⟩ := hC ρ.im
  rw [finsum_mem_eq_finite_toFinset_sum _ hf] at hb
  exact (Finset.single_le_sum (fun r _ => Nat.cast_nonneg (zetaMult r))
    (hf.mem_toFinset.mpr ⟨hρ, by simp⟩)).trans hb
end GoldbachBoundaries.Paper2.M2
