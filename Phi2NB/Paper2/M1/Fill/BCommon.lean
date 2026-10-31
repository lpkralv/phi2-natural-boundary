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

/-!
# Zeros of bounded height

Zeros of bounded height are finitely many, and no non-trivial zero is real. Both unconditional.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Zeros of bounded height are finite. -/
lemma finite_zeros_abs_im_le (T : ℝ) : {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ T}.Finite := by
  refine ((isCompact_Icc.reProdIm isCompact_Icc :
    IsCompact ((Icc (0 : ℝ) 1) ×ℂ (Icc (-T) T))).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨hρ, h⟩
  rw [abs_le] at h
  refine ⟨?_, hρ.1⟩
  simp only [mem_reProdIm, mem_Icc]
  exact ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, h.1, h.2⟩

/-- No non-trivial zero is real (`ζ(x) ≠ 0` for `0 < x < 1`). -/
lemma im_ne_zero_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.im ≠ 0 := by
  intro h
  have hρ' : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp [h]
  apply riemannZeta_ne_zero_of_mem_Ioo (x := ρ.re) ⟨hρ.2.1, hρ.2.2⟩
  rw [← hρ']
  exact hρ.1

end GoldbachBoundaries.Paper2.M1
