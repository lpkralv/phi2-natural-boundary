import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.cauchy_meromorphic
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.meromorphicOn_exceptionalC`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem meromorphicOn_exceptionalC (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    (hfin : offLineZeros.Finite) : MeromorphicOn exceptionalC univ := by
  classical
  intro s _
  let J := {p : NontrivialZeros × NontrivialZeros //
    (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2}
  obtain ⟨T, hT⟩ := (hfin.image (fun z : ℂ => |z.im|)).bddAbove
  let M := |T| + |s.im| + 2
  have hZ : {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ M}.Finite := by
    refine ((M1.finite_zeros_abs_im_le M).preimage
      (Subtype.val_injective (p := fun ρ : ℂ => ρ ∈ NontrivialZeros)).injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, hρ⟩
  have hP : {p : J | |(p.1.1 : ℂ).im| ≤ M ∧ |(p.1.2 : ℂ).im| ≤ M}.Finite :=
    (hZ.prod hZ).preimage Subtype.val_injective.injOn
  have ha := summable_norm_zeroCoef_hinf hZ1 hZ2 hStir
  have hsum := (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
    (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha).subtype
      (fun p : NontrivialZeros × NontrivialZeros =>
        (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2)
  have hgap : ∀ w ∈ ball s 1, ∀ p : J, p ∉ hP.toFinset →
      1 ≤ ‖w - ((p.1.1 : ℂ) + p.1.2)‖ := by
    intro w hw p hp
    by_contra hn
    have hn' := (abs_im_le_norm (w - ((p.1.1 : ℂ) + p.1.2))).trans_lt (lt_of_not_ge hn)
    simp only [sub_im, add_im] at hn'
    have hw' : ‖w - s‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hwim := (abs_im_le_norm (w - s)).trans_lt hw'
    rw [sub_im, abs_lt] at hwim
    have hsabs := abs_le.mp (le_refl |s.im|)
    have hbound : |(p.1.1 : ℂ).im| ≤ |T| ∨ |(p.1.2 : ℂ).im| ≤ |T| := by
      rcases p.2 with h | h
      · exact Or.inl ((hT (mem_image_of_mem _ (show (p.1.1 : ℂ) ∈ offLineZeros from
          ⟨p.1.1.2, h⟩))).trans (le_abs_self T))
      · exact Or.inr ((hT (mem_image_of_mem _ (show (p.1.2 : ℂ) ∈ offLineZeros from
          ⟨p.1.2.2, h⟩))).trans (le_abs_self T))
    apply hp
    rw [hP.mem_toFinset]
    change |(p.1.1 : ℂ).im| ≤ M ∧ |(p.1.2 : ℂ).im| ≤ M
    rw [abs_lt] at hn'
    rcases hbound with h | h
    · rw [abs_le] at h
      constructor <;> rw [abs_le] <;> dsimp [M] <;>
        constructor <;> linarith [hsabs.1, hsabs.2, abs_nonneg s.im]
    · rw [abs_le] at h
      constructor <;> rw [abs_le] <;> dsimp [M] <;>
        constructor <;> linarith [hsabs.1, hsabs.2, abs_nonneg s.im]
  have hm := meromorphicAt_cauchy_of_gap
    (fun p : J => zeroCoef p.1.1 * zeroCoef p.1.2)
    (fun p : J => (p.1.1 : ℂ) + p.1.2) hsum one_pos one_pos hP.toFinset hgap
  change MeromorphicAt (fun w => ∑' p : J,
    zeroCoef p.1.1 * zeroCoef p.1.2 / (w - p.1.1 - p.1.2)) s
  simpa only [sub_add_eq_sub_sub] using hm

end GoldbachBoundaries.Phi2HInf
