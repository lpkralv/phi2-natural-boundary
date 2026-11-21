import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.sum_zetaMult_window_le
import Phi2NB.HInfSupport.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.collision_bin_le`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem collision_bin_le (hZ1 : Z1) (hZ2 : Z2) {Y : ℝ} (hY : 0 < Y) :
    ∃ K : ℝ, ∀ s : ℂ, |s.im| ≤ Y → ∀ v : ℝ, 0 ≤ v →
      ∑ᶠ p ∈ {p : collisionIdx s | -(p.1.2 : ℂ).im ∈ Ico v (v + 1)},
        ((zetaMult p.1.1 * zetaMult p.1.2 : ℕ) : ℝ) ≤ K * Real.log (v + Y + 4) ^ 2 := by
  classical
  obtain ⟨C, hC⟩ := _root_.GoldbachBoundaries.Paper2.M1.sum_zetaMult_window_le_fullZ2 hZ1 hZ2
  obtain ⟨D, hD⟩ := _root_.GoldbachBoundaries.Paper2.M2.zetaMult_le_log_fullZ2 hZ1 hZ2
  let C₀ := max C 0
  let D₀ := max D 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hD₀ : 0 ≤ D₀ := le_max_right _ _
  refine ⟨D₀ * C₀, ?_⟩
  intro s hs v hv
  let S := {p : collisionIdx s | -(p.1.2 : ℂ).im ∈ Ico v (v + 1)}
  let T := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - (-v)| ≤ 1}
  let g : collisionIdx s → ℂ := fun p => p.1.2
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hp := p.2
      have hq := q.2
      change (p.1.2 : ℂ) = q.1.2 at hpq
      rw [hpq] at hp
      exact add_right_cancel (hp.trans hq.symm)
    · exact Subtype.ext hpq
  have hsub : g '' S ⊆ T := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨p.1.2.2, abs_le.mpr ?_⟩
    change v ≤ -(p.1.2 : ℂ).im ∧ -(p.1.2 : ℂ).im < v + 1 at hp
    dsimp [g]
    constructor <;> linarith [hp.1, hp.2]
  have hT : T.Finite := (hC (-v)).1
  have hS : S.Finite := Set.Finite.of_finite_image (hT.subset hsub) hg.injOn
  let L := Real.log (v + Y + 4)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hpt : ∀ p ∈ S, (zetaMult p.1.1 : ℝ) ≤ D₀ * L := by
    intro p hp
    have him : (p.1.1 : ℂ).im + (p.1.2 : ℂ).im = s.im := by
      simpa using congrArg Complex.im p.2
    have hab : |(p.1.1 : ℂ).im| ≤ v + Y + 1 := by
      change v ≤ -(p.1.2 : ℂ).im ∧ -(p.1.2 : ℂ).im < v + 1 at hp
      rw [abs_le] at hs ⊢
      constructor <;> linarith [hs.1, hs.2, hp.1, hp.2]
    calc (zetaMult p.1.1 : ℝ) ≤ D * Real.log (|(p.1.1 : ℂ).im| + 3) := hD _ p.1.1.2
      _ ≤ D₀ * Real.log (|(p.1.1 : ℂ).im| + 3) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.log_nonneg (by linarith [abs_nonneg (p.1.1 : ℂ).im]))
      _ ≤ D₀ * L := mul_le_mul_of_nonneg_left
        (Real.log_le_log (by positivity) (by linarith)) hD₀
  have hwin : ∑ᶠ p ∈ S, (zetaMult (g p) : ℝ) ≤ C₀ * L := by
    rw [← finsum_mem_image (f := fun ρ : ℂ => (zetaMult ρ : ℝ)) hg.injOn]
    calc ∑ᶠ ρ ∈ g '' S, (zetaMult ρ : ℝ) ≤ ∑ᶠ ρ ∈ T, (zetaMult ρ : ℝ) := by
          rw [finsum_mem_eq_finite_toFinset_sum _ (hT.subset hsub),
            finsum_mem_eq_finite_toFinset_sum _ hT]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Set.Finite.mem_toFinset] at hx ⊢
            exact hsub hx
          · intros; exact Nat.cast_nonneg _
      _ ≤ C * Real.log (|-v| + 3) := (hC (-v)).2
      _ ≤ C₀ * Real.log (v + 3) := by
          rw [abs_neg, abs_of_nonneg hv]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.log_nonneg (by linarith))
      _ ≤ C₀ * L := mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith) (by linarith)) hC₀
  calc
    ∑ᶠ p ∈ S, ((zetaMult p.1.1 * zetaMult p.1.2 : ℕ) : ℝ) ≤
        D₀ * L * ∑ᶠ p ∈ S, (zetaMult (g p) : ℝ) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hS,
        finsum_mem_eq_finite_toFinset_sum _ hS, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (hpt p (hS.mem_toFinset.mp hp)) (Nat.cast_nonneg _)
    _ ≤ D₀ * L * (C₀ * L) := mul_le_mul_of_nonneg_left hwin (mul_nonneg hD₀ hL)
    _ = D₀ * C₀ * L ^ 2 := by ring

end GoldbachBoundaries.Phi2HInf
