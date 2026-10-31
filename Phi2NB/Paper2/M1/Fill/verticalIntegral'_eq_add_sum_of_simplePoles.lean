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
# Rectangle integrals of finite sums

The rectangle integral is additive over a finite sum of functions that are continuous on the border of the
rectangle.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The rectangle integral of a finite sum of functions continuous on the border is the sum of the rectangle
integrals. -/
theorem rectangleIntegral'_finset_sum_D {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (h : ∀ i ∈ S, ContinuousOn (F i) (RectangleBorder z w)) :
    RectangleIntegral' (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, RectangleIntegral' (F i) z w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral]
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, ContinuousOn (F i) (RectangleBorder z w) :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hfun : (fun s => ∑ i ∈ insert a S, F i s) = F a + fun s => ∑ i ∈ S, F i s := by
      funext s; simp [Finset.sum_insert ha]
    have h1 : RectangleBorderIntegrable (F a) z w :=
      (h a (Finset.mem_insert_self a S)).rectangleBorder_integrable
    have h2 : RectangleBorderIntegrable (fun s => ∑ i ∈ S, F i s) z w :=
      (continuousOn_finsetSum S fun i hi => hS i hi).rectangleBorder_integrable
    rw [hfun, Finset.sum_insert ha, ← ih hS]
    unfold RectangleIntegral'
    rw [RectangleBorderIntegrable.add h1 h2, smul_add]

end GoldbachBoundaries.Paper2.M1
