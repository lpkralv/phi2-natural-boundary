import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.ResidueAPI
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.pairCat_geometry
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.hasResidue_C`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem hasResidue_cauchy_of_gap {ι : Type} (a p : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (E : Finset ι) (hgap : ∀ w ∈ ball z r, ∀ i, i ∉ E → d ≤ ‖w - p i‖) :
    HasResidue (fun w => ∑' i, a i / (w - p i)) z (∑' i : {i // p i = z}, a i.1) := by
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
  have hterm (i : ι) : HasResidue (f i) z (if p i = z then a i else 0) := by
    by_cases hi : p i = z
    · simpa only [f, hi, if_pos] using hasResidue_div_sub z (a i)
    · rw [if_neg hi]
      exact hasResidue_zero_of_analyticAt (analyticAt_const.div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (Ne.symm hi)))
  have hhead : HasResidue (fun w => ∑ i ∈ E, f i w) z
      (∑ i ∈ E, if p i = z then a i else 0) := by
    unfold HasResidue
    simp_rw [Finset.mul_sum]
    exact tendsto_finsetSum E (fun i _ => hterm i)
  have hres := hhead.add_analyticAt (htail.analyticOnNhd isOpen_ball z (mem_ball_self hr))
  have heq : (∑' i : {i // p i = z}, a i.1) = ∑ i ∈ E, if p i = z then a i else 0 := by
    trans ∑' i, if p i = z then a i else 0
    · exact tsum_subtype {i | p i = z} a
    apply tsum_eq_sum
    intro i hi
    have hne : p i ≠ z := by
      intro h
      have hg := hgap z (mem_ball_self hr) i hi
      rw [h, sub_self, norm_zero] at hg
      exact (not_le_of_gt hd) hg
    simp [hne]
  rw [heq]
  apply hres.congr
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [ball_mem_nhds z hr] with w hw
  have hs : Summable (fun i => f i w) := by
    apply (ha.div_const d).of_norm_bounded_eventually
    have hev : ∀ᶠ i in cofinite, i ∉ E := E.finite_toSet.compl_mem_cofinite
    filter_upwards [hev] with i hi
    dsimp [f]
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hgap w hw i hi)
  exact hs.sum_add_tsum_subtype_compl E

theorem hasResidue_C (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {s : ℂ} (hs : s ∈ HH) : HasResidue C s (collisionAtom s) := by
  change 1 < s.re at hs
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
  have hres := hasResidue_cauchy_of_gap (z := s)
    (fun p : NontrivialZeros × NontrivialZeros => zeroCoef p.1 * zeroCoef p.2)
    (fun p => (p.1 : ℂ) + p.2)
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
      (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hr hd E
    (by
      intro w hw p hp
      simpa only [sub_add_eq_sub_sub] using hgap w (ball_subset_closedBall hw) p hp)
  change HasResidue (fun w => ∑' p : NontrivialZeros × NontrivialZeros,
    zeroCoef p.1 * zeroCoef p.2 / (w - p.1 - p.2)) s (collisionAtom s)
  simpa only [collisionAtom, collisionIdx, sub_add_eq_sub_sub] using hres

end GoldbachBoundaries.Phi2HInf
