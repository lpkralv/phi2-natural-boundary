import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.collision_family
import Phi2NB.Phi2HInf.Fill.meromorphicOn_M0
import Phi2NB.Phi2HInf.Fill.meromorphicOn_exceptionalC
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M1Regularization

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Proof.M4Critical`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem criticalAtom_ne_zero_of_large (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {Y : ℝ} (hY : 0 < Y) : ∃ X : ℝ, Y ≤ X ∧
      ∀ τ : ℝ, |τ| ≤ Y → Nonempty (criticalPairIdx τ) →
        (∀ p : criticalPairIdx τ,
          X < |(criticalVal p.1.1).im| ∧ X < |(criticalVal p.1.2).im|) → criticalAtom τ ≠ 0 := by
  obtain ⟨X, hXY, hX⟩ := pair_family_ne_zero_of_large hZ1 hZ2 hStir
    (B := 1 / 2) le_rfl (by norm_num) hY
  refine ⟨X, hXY, ?_⟩
  intro τ hτ hne hlarge
  let f : criticalPairIdx τ → collisionIdx (1 + (τ : ℂ) * I) :=
    fun p => ⟨(p.1.1.1, p.1.2.1), p.2⟩
  have hf : Function.Injective f := by
    intro p q h
    have hv := congrArg (fun r : collisionIdx (1 + (τ : ℂ) * I) => r.1) h
    apply Subtype.ext
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hv)) (Subtype.ext (congrArg Prod.snd hv))
  apply hX (1 + (τ : ℂ) * I) (by simpa using hτ) f hf hne _ hlarge
  intro p
  change (criticalVal p.1.1).re ∈ Icc (1 - 1 / 2) (1 / 2) ∧
    (criticalVal p.1.2).re ∈ Icc (1 - 1 / 2) (1 / 2)
  rw [show (criticalVal p.1.1).re = 1 / 2 from p.1.1.2,
    show (criticalVal p.1.2).re = 1 / 2 from p.1.2.2]
  norm_num

theorem meromorphicOn_W (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hfin : offLineZeros.Finite) : MeromorphicOn W (halfPlane (1 / 2)) := by
  intro s hs
  have hA := ((differentiableOn_A hZ1 hZ2 hZ3 hStir).analyticOnNhd
    (isOpen_halfPlane _) s hs).meromorphicAt
  have hΓ := (differentiable_one_div_Gamma.analyticAt s).meromorphicAt
  have hC := meromorphicOn_exceptionalC hZ1 hZ2 hStir hfin s (mem_univ _)
  have hM := meromorphicOn_M0 hZ1 hZ2 hStir s (mem_univ _)
  convert hM.add ((hC.add hA).mul hΓ) using 1
  ext z
  simp only [W, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv]

end GoldbachBoundaries.Phi2HInf
