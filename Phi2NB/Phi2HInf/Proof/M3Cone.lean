import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon
import Phi2NB.HInfSupport.Paper2.Statements
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.collision_family
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Proof.M3Cone`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem collisionAtom_ne_zero_of_large (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2)
    (hStir : StirlingStrip) {Y : ℝ} (hY : 0 < Y) :
    ∃ X : ℝ, Y ≤ X ∧ ∀ s : ℂ, |s.im| ≤ Y → Nonempty (collisionIdx s) →
      (∀ p : collisionIdx s, X < |(p.1.1 : ℂ).im| ∧ X < |(p.1.2 : ℂ).im|) →
      collisionAtom s ≠ 0 := by
  have hB : 1 / 2 ≤ Bsup := (lem_B_i hZ1).1.trans (lem_B_i hZ1).2.1
  obtain ⟨X, hXY, hX⟩ := pair_family_ne_zero_of_large hZ1 hZ2 hStir hB (lem_B_iii hH) hY
  refine ⟨X, hXY, ?_⟩
  intro s hs hne hlarge
  have hstrip (ρ : NontrivialZeros) : (ρ : ℂ).re ∈ Icc (1 - Bsup) Bsup := by
    refine ⟨?_, M1.re_le_Bsup ρ.2⟩
    have hr := M1.re_le_Bsup ((hZ1 ρ ρ.2).2.1)
    simp only [sub_re, one_re, conj_re] at hr
    linarith
  exact hX s hs id Function.injective_id hne
    (fun p => ⟨hstrip p.1.1, hstrip p.1.2⟩) hlarge

end GoldbachBoundaries.Phi2HInf
