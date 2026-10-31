import Phi2NB.Phi2.Fill.BCommon

/-! The residue theorem for `kernelL t` on a rectangle: `rect_kernelL`. Apply
`M5.rectangleIntegral'_eq_sum_of_simplePoles_rect` on `[2/5, 3/4] × [-Y', Y']` with `S` the zeros with `|γ| < Y'`. Off
`S` the closed rectangle has no zero of `ζ` (RH puts a zero on `Re = 1/2`; one with `|γ| = Y'` would sit on a
horizontal side, excluded by `hside`), and `kernelL t = (t^{-w}Γ(w)) ψ(w)` is holomorphic there. At `ρ ∈ S` the
principal part is `t^{-ρ}Γ(ρ)(-m(ρ))/(w - ρ)` (`M4b.isBigO_mul_sub_residue`,
`hasResidue_negLogDerivZeta_of_mem_nontrivialZeros`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Residue theorem on a rectangle of height `Y'`** (RH): if no zero lies on the horizontal sides, the boundary
integral of `kernelL t` over `[2/5, 3/4] × [-Y', Y']` is the sum of the residues `-a_ρ t^{-ρ}` at the zeros with
`|γ| < Y'` (finitely many). The only poles of `Γψ` in the closed rectangle are these zeros (RH; `ζ(x) ≠ 0` on `(0,1)`,
`riemannZeta_ne_zero_of_mem_Ioo`), each simple for `ψ` with residue `-m(ρ)`. -/
theorem rect_kernelL (hRH : RiemannHypothesis) {t Y' : ℝ} (ht : 0 < t) (hY' : 0 < Y')
    (hside : ∀ x ∈ Icc (2 / 5 : ℝ) (3 / 4), riemannZeta (x + Y' * I) ≠ 0 ∧ riemannZeta (x - Y' * I) ≠ 0) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'}.Finite ∧
      RectangleIntegral' (kernelL t) (((2 / 5 : ℝ) : ℂ) - I * Y') (((3 / 4 : ℝ) : ℂ) + I * Y') =
        ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'}, -(zeroCoef ρ * (t : ℂ) ^ (-ρ)) := by
  classical
  set Z : Set ℂ := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'} with hZ
  have hZfin : Z.Finite := (M1.finite_zeros_abs_im_le Y').subset fun ρ hρ => ⟨hρ.1, hρ.2.le⟩
  refine ⟨hZfin, ?_⟩
  have hre : ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ => sigmaFinite_re_eq_half hRH hρ
  set S : Finset ℂ := hZfin.toFinset with hSdef
  set A : ℂ → ℂ := fun p => -(zeroCoef p * (t : ℂ) ^ (-p)) with hA
  have hσ : (2 / 5 : ℝ) ≤ 3 / 4 := by norm_num
  have hS : ∀ p ∈ S, (2 / 5 : ℝ) < p.re ∧ p.re < 3 / 4 ∧ |p.im| < Y' := by
    intro p hp
    rw [hSdef, Set.Finite.mem_toFinset] at hp
    rw [hre p hp.1]
    exact ⟨by norm_num, by norm_num, hp.2⟩
  have hf : DifferentiableOn ℂ (kernelL t) (Icc (2 / 5 : ℝ) (3 / 4) ×ℂ Icc (-Y') Y' \ (S : Set ℂ)) := by
    rintro z ⟨hzR, hzS⟩
    rw [mem_reProdIm] at hzR
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hzR
    have hz0 : 0 < z.re := by linarith
    have hz1 : z ≠ 1 := fun h => by rw [h, one_re] at hx2; linarith
    have hζ : riemannZeta z ≠ 0 := by
      intro hz
      have hzN : z ∈ NontrivialZeros := ⟨hz, hz0, by linarith⟩
      have hzre := hre z hzN
      by_cases hlt : |z.im| < Y'
      · exact hzS (by rw [hSdef, Finset.mem_coe, Set.Finite.mem_toFinset]; exact ⟨hzN, hlt⟩)
      · have habs : |z.im| = Y' := le_antisymm (abs_le.mpr ⟨hy1, hy2⟩) (not_lt.mp hlt)
        have hg := hside (1 / 2) ⟨by norm_num, by norm_num⟩
        rcases (abs_eq hY'.le).mp habs with him | him
        · apply hg.1
          have : z = ((1 / 2 : ℝ) : ℂ) + Y' * I := by
            apply Complex.ext <;> simp [hzre, him]
          rw [← this]; exact hz
        · apply hg.2
          have : z = ((1 / 2 : ℝ) : ℂ) - Y' * I := by
            apply Complex.ext <;> simp [hzre, him]
          rw [← this]; exact hz
    have h1 := TIdentity.differentiableAt_ofReal_cpow_neg ht z
    have h2 : DifferentiableAt ℂ Gamma z := TIdentity.differentiableAt_Gamma_of_re_pos hz0
    have h3 := differentiableAt_negLogDerivZeta hz1 hζ
    have : DifferentiableAt ℂ (kernelL t) z := by
      have := h1.mul (h2.mul h3)
      exact this
    exact this.differentiableWithinAt
  have hpole : ∀ p ∈ S, (kernelL t - fun z => A p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    have hpN : p ∈ NontrivialZeros := by
      rw [hSdef, Set.Finite.mem_toFinset] at hp; exact hp.1
    have hp0 : 0 < p.re := by rw [hre p hpN]; norm_num
    have hres := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hpN).1
    have hmer := meromorphicAt_negLogDerivZeta p
    have hord := hres.neg_one_le_meromorphicOrderAt hmer
    have hg : AnalyticAt ℂ (fun w : ℂ => (t : ℂ) ^ (-w) * Gamma w) p := by
      refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re})
        (fun w hw => ((TIdentity.differentiableAt_ofReal_cpow_neg ht w).mul
          (TIdentity.differentiableAt_Gamma_of_re_pos hw)).differentiableWithinAt)
        ((isOpen_lt continuous_const continuous_re).mem_nhds hp0)
    have hB := M4b.isBigO_mul_sub_residue hmer hord hres hg
    convert hB using 1
    funext z
    simp only [Pi.sub_apply, kernelL, hA, zeroCoef]
    ring
  have hrect := M5.rectangleIntegral'_eq_sum_of_simplePoles_rect (σ := 2 / 5) (σ' := 3 / 4) (T := Y')
    (f := kernelL t) S A hσ hY'.le hS hf hpole
  rw [hrect, finsum_mem_eq_finite_toFinset_sum _ hZfin]

end GoldbachBoundaries.Phi2Proof
