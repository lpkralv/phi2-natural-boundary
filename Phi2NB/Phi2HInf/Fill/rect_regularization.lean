import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.Fill.negative_line
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.rect_regularization`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

lemma kernelL_zero_pole {x : ℝ} (hx : 0 < x) :
    (kernelL x - fun z => c0 / (z - 0)) =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) := by
  let φ : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * Gamma (z + 1) * negLogDerivZeta z
  have hd : DifferentiableAt ℂ φ 0 := by
    apply DifferentiableAt.mul
    · exact (TIdentity.differentiableAt_ofReal_cpow_neg hx 0).mul
        ((TIdentity.differentiableAt_Gamma_of_re_pos
          (z := (0 : ℂ) + 1) (by norm_num)).comp (0 : ℂ)
          (show DifferentiableAt ℂ (fun z : ℂ => z + 1) 0 by fun_prop))
    · exact differentiableAt_negLogDerivZeta (by norm_num)
        (zeta_ne_zero_negative_strip (by norm_num) (by norm_num))
  have hφ : φ 0 = c0 := by simp [φ, c0]
  have hb : dslope φ 0 =O[𝓝[≠] (0 : ℂ)] (1 : ℂ → ℂ) :=
    ((continuousAt_dslope_same.mpr hd).tendsto.isBigO_one ℂ).mono nhdsWithin_le_nhds
  apply hb.congr' _ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  rw [dslope_of_ne _ hz0, slope_def_field, hφ]
  simp only [φ, Pi.sub_apply, kernelL, Gamma_add_one _ hz0, sub_zero]
  field_simp

lemma rect_kernelL_regularized {x T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hside : ∀ b ∈ Icc (-(1 / 2 : ℝ)) 2,
      riemannZeta (b + T * I) ≠ 0 ∧ riemannZeta (b - T * I) ≠ 0) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < T}.Finite ∧
      RectangleIntegral' (kernelL x) (((-(1 / 2) : ℝ) : ℂ) - I * T) (((2 : ℝ) : ℂ) + I * T) =
        c0 + 1 / (x : ℂ) +
          ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < T}, -(zeroCoef ρ * (x : ℂ) ^ (-ρ)) := by
  classical
  let Z : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| < T}
  have hZ : Z.Finite := (M1.finite_zeros_abs_im_le T).subset (fun ρ hρ => ⟨hρ.1, hρ.2.le⟩)
  let S : Finset ℂ := insert 0 (insert 1 hZ.toFinset)
  let R : ℂ → ℂ := fun p => if p = 0 then c0 else if p = 1 then 1 / (x : ℂ)
    else -(zeroCoef p * (x : ℂ) ^ (-p))
  have hzero : (0 : ℂ) ∉ hZ.toFinset := by
    intro h
    have h0 := ((hZ.mem_toFinset).mp h).1.2.1
    norm_num at h0
  have hone : (1 : ℂ) ∉ hZ.toFinset := by
    intro h
    have h1 := ((hZ.mem_toFinset).mp h).1.2.2
    norm_num at h1
  have hS : ∀ p ∈ S, -(1 / 2 : ℝ) < p.re ∧ p.re < 2 ∧ |p.im| < T := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · norm_num [hT]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · norm_num [hT]
    have hp := (hZ.mem_toFinset).mp hp
    exact ⟨by linarith [hp.1.2.1], by linarith [hp.1.2.2], hp.2⟩
  have hf : DifferentiableOn ℂ (kernelL x)
      (Icc (-(1 / 2 : ℝ)) 2 ×ℂ Icc (-T) T \ (S : Set ℂ)) := by
    rintro z ⟨hzR, hzS⟩
    obtain ⟨⟨hzlo, hzhi⟩, ⟨himlo, himhi⟩⟩ := mem_reProdIm.mp hzR
    have hz0 : z ≠ 0 := by intro he; apply hzS; simp [S, he]
    have hz1 : z ≠ 1 := by intro he; apply hzS; simp [S, he]
    have hζ : riemannZeta z ≠ 0 := by
      by_cases h0 : z.re ≤ 0
      · exact zeta_ne_zero_negative_strip hzlo h0
      by_cases h1 : 1 ≤ z.re
      · exact riemannZeta_ne_zero_of_one_le_re h1
      intro hz
      have hzN : z ∈ NontrivialZeros := ⟨hz, lt_of_not_ge h0, lt_of_not_ge h1⟩
      by_cases hlt : |z.im| < T
      · apply hzS
        simp only [S, Finset.mem_coe, Finset.mem_insert]
        exact Or.inr (Or.inr ((hZ.mem_toFinset).mpr ⟨hzN, hlt⟩))
      have habs : |z.im| = T := le_antisymm (abs_le.mpr ⟨himlo, himhi⟩) (not_lt.mp hlt)
      rcases (abs_eq hT.le).mp habs with him | him
      · apply (hside z.re ⟨hzlo, hzhi⟩).1
        have he : (z.re : ℂ) + T * I = z := by apply Complex.ext <;> simp [him]
        rwa [he]
      · apply (hside z.re ⟨hzlo, hzhi⟩).2
        have he : (z.re : ℂ) - T * I = z := by apply Complex.ext <;> simp [him]
        rwa [he]
    have hG : DifferentiableAt ℂ Gamma z := by
      apply differentiableAt_Gamma
      intro n hn
      cases n with
      | zero => exact hz0 (by simpa using hn)
      | succ n =>
        have he := congrArg Complex.re hn
        norm_num at he
        linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ((TIdentity.differentiableAt_ofReal_cpow_neg hx z).mul
      (hG.mul (differentiableAt_negLogDerivZeta hz1 hζ))).differentiableWithinAt
  have hpole : ∀ p ∈ S, (kernelL x - fun z => R p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    by_cases hp0 : p = 0
    · subst p
      simpa only [R, if_pos rfl] using kernelL_zero_pole hx
    by_cases hp1 : p = 1
    · subst p
      simpa [R] using FillA.kernelL_sub_pole_isBigO hx
    have hpZ : p ∈ Z := by
      simpa only [S, Finset.mem_insert, hp0, hp1, false_or, hZ.mem_toFinset] using hp
    have hres := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hpZ.1).1
    have hmer := meromorphicAt_negLogDerivZeta p
    have hord := hres.neg_one_le_meromorphicOrderAt hmer
    have hg : AnalyticAt ℂ (fun w : ℂ => (x : ℂ) ^ (-w) * Gamma w) p := by
      refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re})
        (fun w hw => ((TIdentity.differentiableAt_ofReal_cpow_neg hx w).mul
          (TIdentity.differentiableAt_Gamma_of_re_pos hw)).differentiableWithinAt)
        ((isOpen_lt continuous_const continuous_re).mem_nhds hpZ.1.2.1)
    convert M4b.isBigO_mul_sub_residue hmer hord hres hg using 1
    funext z
    simp only [Pi.sub_apply, kernelL, R, if_neg hp0, if_neg hp1, zeroCoef]
    ring
  refine ⟨hZ, ?_⟩
  rw [M5.rectangleIntegral'_eq_sum_of_simplePoles_rect S R (by norm_num) hT.le hS hf hpole]
  rw [Finset.sum_insert (by simp [hzero]), Finset.sum_insert hone]
  simp only [R, if_pos rfl, if_neg one_ne_zero]
  rw [finsum_mem_eq_finite_toFinset_sum _ hZ]
  simp only [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : p ≠ 0 := by intro he; subst p; exact hzero hp
  have hp1 : p ≠ 1 := by intro he; subst p; exact hone hp
  simp only [if_neg hp0, if_neg hp1]

end GoldbachBoundaries.Phi2HInf
