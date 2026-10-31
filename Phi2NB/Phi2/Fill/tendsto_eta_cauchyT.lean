import Phi2NB.Phi2.Proof.M3Base

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The radial limit of the Cauchy transform** (RH, (RiemannVonMangoldt)): for every real `τ`, the atom's series converges
absolutely, and `η · cauchyT(1 + iτ + η) → μ{τ}` as `η ↓ 0`. Under RH, `1 + iτ + η - ρ - ρ' = η + i(τ - γ - γ')`, so each
term times `η` tends to `a_ρ a_ρ'` if `γ + γ' = τ` and to `0` otherwise, and is bounded by `|a_ρ a_ρ'|`. Dominated
convergence (`tendsto_tsum_of_dominated_convergence`), then `tsum_subtype` to restrict to `pairIdx τ`.
Uses: `summable_norm_pair`, `sigmaFinite_re_eq_half`. -/
theorem tendsto_eta_cauchyT (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (τ : ℝ) :
    Summable (fun p : pairIdx τ => zeroCoef p.1.1 * zeroCoef p.1.2) ∧
      Tendsto (fun η : ℝ => (η : ℂ) * cauchyT (1 + τ * I + η)) (𝓝[>] 0) (𝓝 (pairAtom τ)) := by
  classical
  let A (p : NontrivialZeros × NontrivialZeros) : ℂ := zeroCoef p.1 * zeroCoef p.2
  let F (η : ℝ) (p : NontrivialZeros × NontrivialZeros) : ℂ :=
    (η : ℂ) * (A p / (1 + τ * I + η - p.1 - p.2))
  let L (p : NontrivialZeros × NontrivialZeros) : ℂ :=
    if (p.1 : ℂ) + p.2 = 1 + τ * I then A p else 0
  have hsumA : Summable (fun p => ‖A p‖) := summable_norm_pair hRH hRvM
  refine ⟨hsumA.of_norm.subtype _, ?_⟩
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim : ∀ p, Tendsto (fun η : ℝ => F η p) (𝓝[>] 0) (𝓝 (L p)) := by
    intro p
    by_cases hp : (p.1 : ℂ) + p.2 = 1 + τ * I
    · have he (η : ℝ) : 1 + τ * I + η - p.1 - p.2 = (η : ℂ) := by
        linear_combination -hp
      have hev : (fun η : ℝ => F η p) =ᶠ[𝓝[>] 0] fun _ => A p := by
        filter_upwards [self_mem_nhdsWithin] with η hηpos
        dsimp [F]
        rw [he]
        exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hηpos))
      simpa only [L, if_pos hp] using tendsto_const_nhds.congr' hev.symm
    · have hd : (1 + τ * I - p.1 - p.2 : ℂ) ≠ 0 := by
        intro he
        apply hp
        linear_combination -he
      have hden : Tendsto (fun η : ℝ => 1 + τ * I + η - p.1 - p.2)
          (𝓝[>] 0) (𝓝 (1 + τ * I - p.1 - p.2)) := by
        simpa using (((tendsto_const_nhds (x := 1 + τ * I)).add hη).sub_const (p.1 : ℂ)).sub_const (p.2 : ℂ)
      simpa only [F, L, if_neg hp, zero_mul, Pi.div_apply] using
        hη.mul ((tendsto_const_nhds (x := A p)).div hden hd)
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ p, ‖F η p‖ ≤ ‖A p‖ := by
    filter_upwards [self_mem_nhdsWithin] with η hηpos p
    have hre : (1 + τ * I + η - p.1 - p.2 : ℂ).re = η := by
      simp only [sub_re, add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      rw [sigmaFinite_re_eq_half hRH p.1.2, sigmaFinite_re_eq_half hRH p.2.2]
      ring
    have hnorm : η ≤ ‖(1 + τ * I + η - p.1 - p.2 : ℂ)‖ := by
      simpa only [hre] using Complex.re_le_norm (1 + τ * I + η - p.1 - p.2 : ℂ)
    have hnormpos : 0 < ‖(1 + τ * I + η - p.1 - p.2 : ℂ)‖ := lt_of_lt_of_le hηpos hnorm
    dsimp [F]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hηpos.le]
    calc η * (‖A p‖ / ‖(1 + τ * I + η - p.1 - p.2 : ℂ)‖) =
        ‖A p‖ * (η / ‖(1 + τ * I + η - p.1 - p.2 : ℂ)‖) := by ring
      _ ≤ ‖A p‖ * 1 := mul_le_mul_of_nonneg_left ((div_le_one hnormpos).mpr hnorm) (norm_nonneg _)
      _ = ‖A p‖ := mul_one _
  have hT := tendsto_tsum_of_dominated_convergence hsumA hlim hbound
  have hL : (∑' p, L p) = pairAtom τ := by
    symm
    exact tsum_subtype {p : NontrivialZeros × NontrivialZeros | (p.1 : ℂ) + p.2 = 1 + τ * I} A
  rw [hL] at hT
  exact hT.congr (fun η => by simp only [F, A, cauchyT, tsum_mul_left])

end GoldbachBoundaries.Phi2Proof
