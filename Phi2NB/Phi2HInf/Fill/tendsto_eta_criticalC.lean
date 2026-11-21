import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.critical_basic
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.tendsto_eta_criticalC`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem tendsto_eta_criticalC (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) (τ : ℝ) :
    Summable (fun p : criticalPairIdx τ =>
      zeroCoef (criticalVal p.1.1) * zeroCoef (criticalVal p.1.2)) ∧
    Tendsto (fun η : ℝ => (η : ℂ) * criticalC (1 + τ * I + η))
      (𝓝[>] 0) (𝓝 (criticalAtom τ)) := by
  classical
  let A (p : CriticalZero × CriticalZero) : ℂ := zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2)
  let F (η : ℝ) (p : CriticalZero × CriticalZero) : ℂ :=
    (η : ℂ) * (A p / (1 + τ * I + η - criticalVal p.1 - criticalVal p.2))
  let L (p : CriticalZero × CriticalZero) : ℂ :=
    if criticalVal p.1 + criticalVal p.2 = 1 + τ * I then A p else 0
  have hsumA : Summable (fun p => ‖A p‖) := summable_norm_critical_pair hZ1 hZ2 hStir
  refine ⟨hsumA.of_norm.subtype _, ?_⟩
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim : ∀ p, Tendsto (fun η : ℝ => F η p) (𝓝[>] 0) (𝓝 (L p)) := by
    intro p
    by_cases hp : criticalVal p.1 + criticalVal p.2 = 1 + τ * I
    · have he (η : ℝ) : 1 + τ * I + η - criticalVal p.1 - criticalVal p.2 = (η : ℂ) := by
        linear_combination -hp
      have hev : (fun η : ℝ => F η p) =ᶠ[𝓝[>] 0] fun _ => A p := by
        filter_upwards [self_mem_nhdsWithin] with η hηpos
        dsimp [F]
        rw [he]
        exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hηpos))
      simpa only [L, ite_eq_left hp] using tendsto_const_nhds.congr' hev.symm
    · have hd : (1 + τ * I - criticalVal p.1 - criticalVal p.2 : ℂ) ≠ 0 := by
        intro he
        apply hp
        linear_combination -he
      have hden : Tendsto (fun η : ℝ => 1 + τ * I + η - criticalVal p.1 - criticalVal p.2)
          (𝓝[>] 0) (𝓝 (1 + τ * I - criticalVal p.1 - criticalVal p.2)) := by
        simpa using (((tendsto_const_nhds (x := 1 + τ * I)).add hη).sub_const (criticalVal p.1)).sub_const (criticalVal p.2)
      simpa only [F, L, ite_eq_right hp, zero_mul, Pi.div_apply] using
        hη.mul ((tendsto_const_nhds (x := A p)).div hden hd)
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ p, ‖F η p‖ ≤ ‖A p‖ := by
    filter_upwards [self_mem_nhdsWithin] with η hηpos p
    have hre : (1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ).re = η := by
      simp only [sub_re, add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      rw [show (criticalVal p.1).re = 1 / 2 from p.1.2,
        show (criticalVal p.2).re = 1 / 2 from p.2.2]
      ring
    have hnorm : η ≤ ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖ := by
      simpa only [hre] using Complex.re_le_norm (1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)
    have hnormpos : 0 < ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖ := lt_of_lt_of_le hηpos hnorm
    dsimp [F]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hηpos.le]
    calc η * (‖A p‖ / ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖) =
        ‖A p‖ * (η / ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖) := by ring
      _ ≤ ‖A p‖ * 1 := mul_le_mul_of_nonneg_left ((div_le_one hnormpos).mpr hnorm) (norm_nonneg _)
      _ = ‖A p‖ := mul_one _
  have hT := tendsto_tsum_of_dominated_convergence hsumA hlim hbound
  have hL : (∑' p, L p) = criticalAtom τ := by
    symm
    exact tsum_subtype {p : CriticalZero × CriticalZero | criticalVal p.1 + criticalVal p.2 = 1 + τ * I} A
  rw [hL] at hT
  exact hT.congr (fun η => by simp only [F, A, criticalC, tsum_mul_left])

end GoldbachBoundaries.Phi2HInf
