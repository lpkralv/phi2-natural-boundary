import Phi2NB.Phi2.Proof.M3Radial
import Phi2NB.Paper2.M1.Fill.sum_zetaMult_window_le
import Phi2NB.Paper2.M2.Fill.zetaMult_le_log

/-! Unit-interval weights of `A_τ`: `Aidx_bin_le`. The map `i ↦ (i : ℂ)` is injective from `A_τ` into the
zeros, and sends the fibre `Im i ∈ [v, v+1)` into the window `|Im ρ - v| ≤ 1`, which is finite with
`∑ m(ρ) ≤ C log(|v|+3)` (`M1.sum_zetaMult_window_le`). On the fibre, `m(ρ + iτ) ≤ C' log(|γ + τ| + 3)
≤ C' log(v + Y + 4)` (`M2.zetaMult_le_log`), and `log(v + Y + 4) ≤ log((v+3)(Y+2))
≤ (1 + log(Y+2)/log 3) log(v+3)` for `v ≥ 0`. So the total weight is `≤ K log²(v+3)`. (Bounding the number of
distinct zeros and each multiplicity separately would give only `log³`.) -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `log(v + Y + 4) ≤ (1 + log(Y+2)/log 3) log(v+3)` for `v, Y ≥ 0`. -/
private lemma fillDz_log_shift {v Y : ℝ} (hv : 0 ≤ v) (hY : 0 ≤ Y) :
    Real.log (v + Y + 4) ≤ (1 + Real.log (Y + 2) / Real.log 3) * Real.log (v + 3) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hv3 : Real.log 3 ≤ Real.log (v + 3) := Real.log_le_log (by norm_num) (by linarith)
  have hY2 : 0 ≤ Real.log (Y + 2) := Real.log_nonneg (by linarith)
  have h1 : Real.log (v + Y + 4) ≤ Real.log (v + 3) + Real.log (Y + 2) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h2 : Real.log (Y + 2) ≤ Real.log (Y + 2) / Real.log 3 * Real.log (v + 3) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    exact mul_le_mul_of_nonneg_left hv3 hY2
  nlinarith

/-- **Unit-interval weights of `A_τ`** (RH, (RiemannVonMangoldt)): for `Y > 0` there is `K` with, for `0 < τ ≤ Y` and all `v`, finitely
many `ρ ∈ A_τ` with `γ ∈ [v, v+1)`, of total weight `∑ m(ρ) m(ρ + iτ) ≤ K log²(v + 3)` when `v ≥ 0`. (ZeroSymmetry) comes
from RH. -/
theorem Aidx_bin_le (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) {Y : ℝ} (hY : 0 < Y) :
    ∃ K : ℝ, ∀ τ ∈ Ioc (0 : ℝ) Y, ∀ v : ℝ,
      {i : Aidx τ | (i.1 : ℂ).im ∈ Ico v (v + 1)}.Finite ∧
      (0 ≤ v → ∑ᶠ i ∈ {i : Aidx τ | (i.1 : ℂ).im ∈ Ico v (v + 1)}, (Aweight τ i : ℝ) ≤
        K * Real.log (v + 3) ^ 2) := by
  classical
  have hZ1 := zeroSymmetry_of_RH hRH
  obtain ⟨C, hC⟩ := M1.sum_zetaMult_window_le hZ1 hRvM
  obtain ⟨C', hC'⟩ := M2.zetaMult_le_log hZ1 hRvM
  set C0 := max C 0
  set C1 := max C' 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hC1 : 0 ≤ C1 := le_max_right _ _
  refine ⟨C1 * C0 * (1 + Real.log (Y + 2) / Real.log 3), fun τ hτ v => ?_⟩
  obtain ⟨hτ0, hτY⟩ := hτ
  set S := {i : Aidx τ | (i.1 : ℂ).im ∈ Ico v (v + 1)}
  set T := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - v| ≤ 1}
  let g : Aidx τ → ℂ := fun i => (i.1 : ℂ)
  have hg : Function.Injective g := fun i j h => Subtype.ext (Subtype.ext h)
  have hgST : g '' S ⊆ T := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨i.1.2, ?_⟩
    obtain ⟨h1, h2⟩ := hi
    rw [abs_le]
    constructor <;> linarith
  have hT : T.Finite := (hC v).1
  have hSf : S.Finite := Set.Finite.of_finite_image (hT.subset hgST) hg.injOn
  refine ⟨hSf, fun hv => ?_⟩
  -- the pointwise bound on the second multiplicity
  set L := C1 * Real.log (v + Y + 4)
  have hL0 : 0 ≤ L := mul_nonneg hC1 (Real.log_nonneg (by linarith))
  have hpt : ∀ i ∈ S, (Aweight τ i : ℝ) ≤ L * (zetaMult (g i) : ℝ) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hi
    have hm := hC' _ i.2.2
    have him : |((i.1 : ℂ) + τ * I).im| ≤ v + Y + 1 := by
      simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one, add_zero]
      rw [abs_le]
      constructor <;> linarith
    have hlog : Real.log (|((i.1 : ℂ) + τ * I).im| + 3) ≤ Real.log (v + Y + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (|((i.1 : ℂ) + τ * I).im| + 3) := Real.log_nonneg (by
      have := abs_nonneg ((i.1 : ℂ) + τ * I).im; linarith)
    have hm' : (zetaMult ((i.1 : ℂ) + τ * I) : ℝ) ≤ L := by
      calc (zetaMult ((i.1 : ℂ) + τ * I) : ℝ)
          ≤ C' * Real.log (|((i.1 : ℂ) + τ * I).im| + 3) := hm
        _ ≤ C1 * Real.log (|((i.1 : ℂ) + τ * I).im| + 3) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
        _ ≤ L := mul_le_mul_of_nonneg_left hlog hC1
    simp only [Aweight, Nat.cast_mul]
    rw [mul_comm L]
    exact mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg _)
  -- the window sum
  have hwin : ∑ᶠ i ∈ S, (zetaMult (g i) : ℝ) ≤ C0 * Real.log (v + 3) := by
    rw [← finsum_mem_image (f := fun ρ : ℂ => (zetaMult ρ : ℝ)) hg.injOn]
    calc ∑ᶠ ρ ∈ g '' S, (zetaMult ρ : ℝ)
        ≤ ∑ᶠ ρ ∈ T, (zetaMult ρ : ℝ) := by
          rw [finsum_mem_eq_finite_toFinset_sum _ (hT.subset hgST),
            finsum_mem_eq_finite_toFinset_sum _ hT]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            simp only [Set.Finite.mem_toFinset] at hx ⊢
            exact hgST hx
          · intros; exact Nat.cast_nonneg _
      _ ≤ C * Real.log (|v| + 3) := (hC v).2
      _ ≤ C0 * Real.log (v + 3) := by
          rw [abs_of_nonneg hv]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith))
  have hsum : ∑ᶠ i ∈ S, (Aweight τ i : ℝ) ≤ L * ∑ᶠ i ∈ S, (zetaMult (g i) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hSf,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hpt i (hSf.mem_toFinset.mp hi)
  have hshift := fillDz_log_shift hv hY.le
  have hl3 : 0 ≤ Real.log (v + 3) := Real.log_nonneg (by linarith)
  calc ∑ᶠ i ∈ S, (Aweight τ i : ℝ)
      ≤ L * (C0 * Real.log (v + 3)) := hsum.trans (mul_le_mul_of_nonneg_left hwin hL0)
    _ = C1 * C0 * Real.log (v + Y + 4) * Real.log (v + 3) := by ring
    _ ≤ C1 * C0 * ((1 + Real.log (Y + 2) / Real.log 3) * Real.log (v + 3)) * Real.log (v + 3) := by
        apply mul_le_mul_of_nonneg_right _ hl3
        exact mul_le_mul_of_nonneg_left hshift (mul_nonneg hC1 hC0)
    _ = C1 * C0 * (1 + Real.log (Y + 2) / Real.log 3) * Real.log (v + 3) ^ 2 := by ring

end GoldbachBoundaries.Phi2Proof
