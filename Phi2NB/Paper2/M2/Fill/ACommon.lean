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

lemma A_finite_strip (t : ℝ) (L : ℕ) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ t ≤ ρ.im ∧ ρ.im ≤ t + L}.Finite :=
  (finite_zeros_abs_im_le (|t| + L)).subset fun ρ ⟨hz, hl, hu⟩ =>
    ⟨hz, abs_le.mpr ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩

lemma A_ncard_le_weight {s : Set ℂ} (hs : s.Finite) (hz : s ⊆ NontrivialZeros) :
    (s.ncard : ℝ) ≤ wsumB s := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs, wsumB, finsum_mem_eq_finite_toFinset_sum _ hs]
  calc (hs.toFinset.card : ℝ) = ∑ _ ∈ hs.toFinset, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun ρ hρ => by
      exact_mod_cast one_le_zetaMult_of_zero (by
        have := (hz (hs.mem_toFinset.mp hρ)).2.2
        intro h; simp [h] at this) (hz (hs.mem_toFinset.mp hρ)).1

end GoldbachBoundaries.Paper2.M2
