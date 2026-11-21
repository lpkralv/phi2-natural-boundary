import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M1.Fill.sum_zetaMult_window_le`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

lemma wsumB_pos_window_le_fullZ2 (hZ2 : Z2) :
    ∃ A : ℝ, ∀ u : ℝ, wsumB {ρ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ |ρ.im - u| ≤ 1} ≤
      A * Real.log (|u| + 3) := by
  obtain ⟨C₁, hC₁⟩ := hZ2.2
  set C := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  set K := wsumB {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ 3} with hKdef
  have hK0 : 0 ≤ K := wsumB_nonneg _
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨3 * C + K / Real.log 3, fun u => ?_⟩
  have hlogu : Real.log 3 ≤ Real.log (|u| + 3) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg u])
  have hlogu0 : 0 ≤ Real.log (|u| + 3) := hlog3.le.trans hlogu
  have hKu : K ≤ K / Real.log 3 * Real.log (|u| + 3) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog3]
    exact mul_le_mul_of_nonneg_left hlogu hK0
  rcases lt_or_ge u 2 with hu | hu
  · 
    have hsub : {ρ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ |ρ.im - u| ≤ 1} ⊆
        {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ 3} := by
      rintro ρ ⟨hρ, h0, h1⟩
      rw [abs_le] at h1
      exact ⟨hρ, by rw [abs_of_pos h0]; linarith⟩
    calc _ ≤ K := wsumB_mono (finite_zeros_abs_im_le 3) hsub
      _ ≤ K / Real.log 3 * Real.log (|u| + 3) := hKu
      _ ≤ _ := by nlinarith
  · 
    set D : ℝ → Set ℂ := fun v => {ρ | ρ ∈ NontrivialZeros ∧ v < ρ.im ∧ ρ.im ≤ v + 1} with hDdef
    have hDfin : ∀ v, (D v).Finite := fun v =>
      (finite_zeros_abs_im_le (|v| + 1)).subset fun ρ ⟨hρ, h1, h2⟩ =>
        ⟨hρ, by rw [abs_le]; constructor <;> linarith [neg_abs_le v, le_abs_self v]⟩
    have hDle : ∀ v, 0 ≤ v → v ≤ u → wsumB (D v) ≤ C * Real.log (|u| + 3) := by
      intro v hv hvu
      rw [wsumB_D_eq hv]
      have hlv : Real.log (v + 3) ≤ Real.log (|u| + 3) :=
        Real.log_le_log (by linarith) (by linarith [le_abs_self u])
      have hlv0 : 0 ≤ Real.log (v + 3) := Real.log_nonneg (by linarith)
      calc Nzero (v + 1) - Nzero v ≤ C₁ * Real.log (v + 3) := hC₁ v hv
        _ ≤ C * Real.log (v + 3) := mul_le_mul_of_nonneg_right (le_max_left _ _) hlv0
        _ ≤ C * Real.log (|u| + 3) := mul_le_mul_of_nonneg_left hlv hC0
    have hsub : {ρ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ |ρ.im - u| ≤ 1} ⊆
        (D (u - 2) ∪ D (u - 1)) ∪ D u := by
      rintro ρ ⟨hρ, -, h1⟩
      rw [abs_le] at h1
      simp only [hDdef, mem_union, mem_ofPred_eq]
      by_cases ha : ρ.im ≤ u - 1
      · exact Or.inl (Or.inl ⟨hρ, by linarith, by linarith⟩)
      · by_cases hb : ρ.im ≤ u
        · exact Or.inl (Or.inr ⟨hρ, by linarith, by linarith⟩)
        · exact Or.inr ⟨hρ, by linarith, by linarith⟩
    have hfinU : ((D (u - 2) ∪ D (u - 1)) ∪ D u).Finite :=
      ((hDfin _).union (hDfin _)).union (hDfin _)
    calc _ ≤ wsumB ((D (u - 2) ∪ D (u - 1)) ∪ D u) := wsumB_mono hfinU hsub
      _ ≤ wsumB (D (u - 2) ∪ D (u - 1)) + wsumB (D u) :=
          wsumB_union_le ((hDfin _).union (hDfin _)) (hDfin _)
      _ ≤ wsumB (D (u - 2)) + wsumB (D (u - 1)) + wsumB (D u) := by
          linarith [wsumB_union_le (hDfin (u - 2)) (hDfin (u - 1))]
      _ ≤ 3 * (C * Real.log (|u| + 3)) := by
          linarith [hDle (u - 2) (by linarith) (by linarith), hDle (u - 1) (by linarith) (by linarith),
            hDle u (by linarith) le_rfl]
      _ ≤ _ := by nlinarith [div_nonneg hK0 hlog3.le]

theorem sum_zetaMult_window_le_fullZ2 (hZ1 : Z1) (hZ2 : Z2) :
    ∃ C : ℝ, ∀ t : ℝ, {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - t| ≤ 1}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - t| ≤ 1}, (zetaMult ρ : ℝ) ≤ C * Real.log (|t| + 3) := by
  obtain ⟨A, hA⟩ := _root_.GoldbachBoundaries.Paper2.M1.wsumB_pos_window_le_fullZ2 hZ2
  refine ⟨2 * A, fun t => ?_⟩
  set W := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - t| ≤ 1} with hWdef
  set Pp : ℝ → Set ℂ := fun u => {ρ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ |ρ.im - u| ≤ 1} with hPpdef
  have hPfin : ∀ u, (Pp u).Finite := fun u =>
    (finite_zeros_abs_im_le (|u| + 1)).subset fun ρ ⟨hρ, _, h1⟩ =>
      ⟨hρ, by have := abs_sub_abs_le_abs_sub ρ.im u; linarith⟩
  have hWfin : W.Finite :=
    (finite_zeros_abs_im_le (|t| + 1)).subset fun ρ ⟨hρ, h1⟩ =>
      ⟨hρ, by have := abs_sub_abs_le_abs_sub ρ.im t; linarith⟩
  refine ⟨hWfin, ?_⟩
  have hsub : W ⊆ Pp t ∪ conj '' Pp (-t) := by
    rintro ρ ⟨hρ, h1⟩
    rcases lt_or_gt_of_ne (im_ne_zero_of_mem_nontrivialZeros hρ) with hneg | hpos
    · refine Or.inr ⟨conj ρ, ⟨conj_mem_nontrivialZeros hρ, ?_, ?_⟩, by simp⟩
      · simp only [conj_im]; linarith
      · simp only [conj_im]
        rw [show -ρ.im - -t = -(ρ.im - t) by ring, abs_neg]
        exact h1
    · exact Or.inl ⟨hρ, hpos, h1⟩
  have hconj : wsumB (conj '' Pp (-t)) = wsumB (Pp (-t)) :=
    wsumB_conj_image hZ1 fun ρ h => h.1
  calc ∑ᶠ ρ ∈ W, (zetaMult ρ : ℝ) = wsumB W := rfl
    _ ≤ wsumB (Pp t ∪ conj '' Pp (-t)) := wsumB_mono ((hPfin t).union ((hPfin _).image _)) hsub
    _ ≤ wsumB (Pp t) + wsumB (conj '' Pp (-t)) := wsumB_union_le (hPfin t) ((hPfin _).image _)
    _ ≤ A * Real.log (|t| + 3) + A * Real.log (|-t| + 3) := by
        rw [hconj]; exact add_le_add (hA t) (hA (-t))
    _ = 2 * A * Real.log (|t| + 3) := by rw [abs_neg]; ring

end GoldbachBoundaries.Paper2.M1
