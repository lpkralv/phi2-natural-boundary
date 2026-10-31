import Phi2NB.Phi2.Proof.M3Radial

/-! Helpers for `sum_bKer_ne_zero`: summing a weighted family over unit-interval fibres. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Fibre summation.** If `u ≥ u₀`, the unit fibres `u ∈ [u₀ + n, u₀ + n + 1)` are finite with weight `≤ W n`, and
`h i ≤ ψ ⌊u i - u₀⌋₊`, then `∑ q_i h_i` is summable and at most `∑ W n ψ n`. -/
theorem D_fibre_tsum_le {ι : Type} (u : ι → ℝ) (q : ι → ℕ) (u₀ : ℝ) (hu : ∀ i, u₀ ≤ u i)
    (hfin : ∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite) (W : ℕ → ℝ) (hW0 : ∀ n, 0 ≤ W n)
    (hW : ∀ n : ℕ, ∑ᶠ i ∈ {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}, (q i : ℝ) ≤ W n)
    (h : ι → ℝ) (ψ : ℕ → ℝ) (hh0 : ∀ i, 0 ≤ h i) (hψ0 : ∀ n, 0 ≤ ψ n)
    (hhψ : ∀ i, h i ≤ ψ ⌊u i - u₀⌋₊) (hsum : Summable fun n => W n * ψ n) :
    Summable (fun i => (q i : ℝ) * h i) ∧ ∑' i, (q i : ℝ) * h i ≤ ∑' n, W n * ψ n := by
  classical
  have hnn : ∀ i, 0 ≤ (q i : ℝ) * h i := fun i => mul_nonneg (Nat.cast_nonneg _) (hh0 i)
  have hT0 : 0 ≤ ∑' n, W n * ψ n := tsum_nonneg fun n => mul_nonneg (hW0 n) (hψ0 n)
  have hfs : ∀ s : Finset ι, ∑ i ∈ s, (q i : ℝ) * h i ≤ ∑' n, W n * ψ n := by
    intro s
    set fl : ι → ℕ := fun i => ⌊u i - u₀⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (t := s.image fl) (g := fl)
      (fun i hi => Finset.mem_image_of_mem fl hi)]
    calc ∑ n ∈ s.image fl, ∑ i ∈ s with fl i = n, (q i : ℝ) * h i
        ≤ ∑ n ∈ s.image fl, W n * ψ n := by
          apply Finset.sum_le_sum
          intro n _
          calc ∑ i ∈ s with fl i = n, (q i : ℝ) * h i
              ≤ ∑ i ∈ s with fl i = n, (q i : ℝ) * ψ n := by
                apply Finset.sum_le_sum
                intro i hi
                have hin := (Finset.mem_filter.mp hi).2
                apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
                rw [← hin]; exact hhψ i
            _ = (∑ i ∈ s with fl i = n, (q i : ℝ)) * ψ n := by rw [Finset.sum_mul]
            _ ≤ W n * ψ n := by
                apply mul_le_mul_of_nonneg_right _ (hψ0 n)
                refine le_trans ?_ (hW n)
                rw [finsum_mem_eq_finite_toFinset_sum _ (hfin (u₀ + n))]
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro i hi
                  obtain ⟨-, hin⟩ := Finset.mem_filter.mp hi
                  rw [Set.Finite.mem_toFinset]
                  have h0 : 0 ≤ u i - u₀ := by linarith [hu i]
                  have h1 := Nat.floor_le h0
                  have h2 := Nat.lt_floor_add_one (u i - u₀)
                  simp only [fl] at hin
                  rw [hin] at h1 h2
                  exact ⟨by linarith, by linarith⟩
                · intro i _ _; exact Nat.cast_nonneg _
      _ ≤ ∑' n, W n * ψ n :=
          hsum.sum_le_tsum _ (fun n _ => mul_nonneg (hW0 n) (hψ0 n))
  exact ⟨summable_of_sum_le hnn hfs, tsum_le_of_sum_le' hT0 hfs⟩

/-- `∑ (c + n)² e^{-πn}` converges. -/
theorem D_summable_sq_exp (c : ℝ) : Summable fun n : ℕ => (c + n) ^ 2 * Real.exp (-Real.pi * n) := by
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 Real.pi_pos
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 Real.pi_pos
  have h2 := Real.summable_pow_mul_exp_neg_nat_mul 2 Real.pi_pos
  have := ((h0.mul_left (c ^ 2)).add (h1.mul_left (2 * c))).add h2
  refine this.congr fun n => ?_
  simp only [pow_zero, pow_one]
  ring

end GoldbachBoundaries.Phi2Proof
