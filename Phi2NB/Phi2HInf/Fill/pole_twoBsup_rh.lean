import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.Statements
import Phi2NB.HInfSupport.Phi2.Proof.M2Explicit
import Phi2NB.HInfSupport.Statements
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.pairCat_geometry
import Phi2NB.Phi2HInf.Fill.pole_twoBsup
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M1Regularization
import Phi2NB.Phi2HInf.ZetaNoZeroIoo

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.pole_twoBsup_rh`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries Paper2 Phi2Proof

theorem analyticAt_cauchy_of_gap {ι : Type} (a p : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (E : Finset ι) (hgap : ∀ w ∈ ball z r, ∀ i, i ∉ E → d ≤ ‖w - p i‖)
    (hne : ∀ i ∈ E, p i ≠ z) :
    AnalyticAt ℂ (fun w => ∑' i, a i / (w - p i)) z := by
  classical
  let f (i : ι) (w : ℂ) := a i / (w - p i)
  have htail : DifferentiableOn ℂ (fun w => ∑' i : {i // i ∉ E}, f i.1 w) (ball z r) := by
    apply Complex.differentiableOn_tsum_of_summable_norm ((ha.subtype _).div_const d)
    · intro i w hw
      exact (differentiableWithinAt_const _).div (differentiableWithinAt_id.sub_const _)
        (norm_pos_iff.mp (hd.trans_le (hgap w hw i.1 i.2)))
    · exact isOpen_ball
    · intro i w hw
      dsimp [f]
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hgap w hw i.1 i.2)
  have hhead : AnalyticAt ℂ (fun w => ∑ i ∈ E, f i w) z := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (hne i hi).symm)
  have hm := hhead.add (htail.analyticOnNhd isOpen_ball z (mem_ball_self hr))
  apply hm.congr
  filter_upwards [ball_mem_nhds z hr] with w hw
  have hs : Summable (fun i => f i w) := by
    apply (ha.div_const d).of_norm_bounded_eventually
    have hev : ∀ᶠ i in cofinite, i ∉ E := E.finite_toSet.compl_mem_cofinite
    filter_upwards [hev] with i hi
    dsimp [f]
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hgap w hw i hi)
  exact hs.sum_add_tsum_subtype_compl E

theorem analyticAt_C_of_not_pairSum (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {s : ℂ} (hs : 1 < s.re)
    (hcat : ∀ p : NontrivialZeros × NontrivialZeros, (p.1 : ℂ) + p.2 ≠ s) :
    AnalyticAt ℂ C s := by
  let r := (s.re - 1) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hsub : closedBall s r ⊆ HH := by
    intro w hw
    have hh : ‖w - s‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hre := (abs_re_le_norm (w - s)).trans hh
    rw [sub_re, abs_le] at hre
    change 1 < w.re
    dsimp [r] at *
    linarith [hre.1]
  obtain ⟨E, d, hd, hgap⟩ := pairCat_denominator_bound hH (isCompact_closedBall s r) hsub
  have ha := summable_norm_zeroCoef_hinf hZ1 hZ2 hStir
  have han := analyticAt_cauchy_of_gap (z := s)
    (fun p : NontrivialZeros × NontrivialZeros => zeroCoef p.1 * zeroCoef p.2)
    (fun p => (p.1 : ℂ) + p.2)
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
      (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hr hd E
    (by
      intro w hw p hp
      simpa only [sub_add_eq_sub_sub] using hgap w (ball_subset_closedBall hw) p hp)
    (fun p _ => hcat p)
  change AnalyticAt ℂ (fun w => ∑' p : NontrivialZeros × NontrivialZeros,
    zeroCoef p.1 * zeroCoef p.2 / (w - p.1 - p.2)) s
  simpa only [sub_add_eq_sub_sub] using han

theorem analyticAt_Phi2cHInf_of_not_pole (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {s : ℂ} (hs : 1 < s.re) (hP : s ∉ phi2Poles)
    (hcat : ∀ p : NontrivialZeros × NontrivialZeros, (p.1 : ℂ) + p.2 ≠ s) :
    AnalyticAt ℂ Phi2cHInf s := by
  have hM := analyticAt_M0_of_not_mem_phi2Poles hZ1 hZ2 hStir hs hP
  have hA := (differentiableOn_A hZ1 hZ2 hZ3 hStir).analyticOnNhd
    (isOpen_halfPlane _) s (show s ∈ halfPlane (1 / 2) by change 1 / 2 < s.re; linarith)
  have hC := analyticAt_C_of_not_pairSum hH hZ1 hZ2 hStir hs hcat
  have hΓ := differentiable_one_div_Gamma.analyticAt s
  have hm := hM.add ((hC.add hA).mul hΓ)
  convert hm using 1
  ext z
  simp only [Phi2cHInf, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv]

theorem exists_trivial_of_riemannZeta_eq_zero_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0)
    (hre : s.re ≤ 0) : ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hwre : 1 ≤ (1 - s).re := by
    rw [sub_re, one_re]
    linarith
  have hwn : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    rw [neg_re, natCast_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : 1 - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hz] at hfe
  have hζw := riemannZeta_ne_zero_of_one_le_re hwre
  have hΓw := Complex.Gamma_ne_zero hwn
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero two_ne_zero hπ h.1
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h two_ne_zero
          · exact absurd h hpow
        · exact absurd h hΓw
      · exact h
    · exact absurd h hζw
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hsk : s = -2 * (k : ℂ) := by
    have h2 : (Real.pi : ℂ) * (s + 2 * (k : ℂ)) = 0 := by linear_combination -2 * hk
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hπ
    · linear_combination h
  have hkre : s.re = -2 * (k : ℝ) := by
    rw [hsk]
    simp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hs0 (by rw [hsk]; simp)
  have hknn : 0 ≤ k := by
    have h : (0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast h
  have h1 : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  have h2 : ((((k - 1).toNat : ℕ) : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by rw [h1]
  push_cast at h2
  refine ⟨(k - 1).toNat, ?_⟩
  rw [h2, hsk]
  ring

theorem riemannHypothesis_iff_nontrivialZeros :
    RiemannHypothesis ↔ ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ hρ
    exact re_eq_half_of_mem_nontrivialZeros hRH hρ
  · intro h s hz htriv _
    refine h s ⟨hz, ?_, ?_⟩
    · by_contra hre
      exact htriv (exists_trivial_of_riemannZeta_eq_zero_of_re_nonpos hz (not_lt.mp hre))
    · by_contra hre
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hre) hz

theorem analyticAt_Phi2cHInf_real_of_RH (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) {x : ℝ} (hx1 : 1 < x) (hx2 : x < 2) :
    AnalyticAt ℂ Phi2cHInf x := by
  have hs : 1 < (x : ℂ).re := by rw [ofReal_re]; exact hx1
  refine analyticAt_Phi2cHInf_of_not_pole (hinf_of_RH hRH) (Z1_of_RH hRH) hZ2 hZ3 hStir hs
    (ofReal_not_mem_phi2Poles hζ hx1 hx2) ?_
  intro p hp
  have hre := congrArg Complex.re hp
  simp only [add_re, ofReal_re] at hre
  have h1 := re_eq_half_of_mem_nontrivialZeros hRH p.1.2
  have h2 := re_eq_half_of_mem_nontrivialZeros hRH p.2.2
  linarith

theorem riemannHypothesis_iff_analyticAt_Phi2cHInf_real (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x := by
  constructor
  · intro hRH x hx1 hx2
    exact analyticAt_Phi2cHInf_real_of_RH hRH hZ2 hZ3 hStir hζ hx1 hx2
  · intro h
    rw [riemannHypothesis_iff_nontrivialZeros]
    by_contra hnot
    push Not at hnot
    obtain ⟨x, hx1, hx2, hx⟩ := not_analyticAt_Phi2cHInf_twoBsup hH hZ1 hZ2 hZ3 hStir hζ hnot
    exact hx (h x hx1 hx2)

end GoldbachBoundaries.Phi2HInf
