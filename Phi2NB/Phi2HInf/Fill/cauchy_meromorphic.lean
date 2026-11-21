import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.pairCat_geometry
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.cauchy_meromorphic`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem meromorphicAt_cauchy_of_gap {ι : Type} (a p : ι → ℂ)
    (ha : Summable (fun i => ‖a i‖)) {z : ℂ} {r d : ℝ} (hr : 0 < r) (hd : 0 < d)
    (E : Finset ι) (hgap : ∀ w ∈ ball z r, ∀ i, i ∉ E → d ≤ ‖w - p i‖) :
    MeromorphicAt (fun w => ∑' i, a i / (w - p i)) z := by
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
  have hhead : MeromorphicAt (fun w => ∑ i ∈ E, f i w) z := by
    apply MeromorphicAt.fun_sum
    intro i hi
    exact analyticAt_const.meromorphicAt.div
      ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have hm := hhead.add ((htail.analyticOnNhd isOpen_ball z (mem_ball_self hr)).meromorphicAt)
  apply hm.congr
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

theorem meromorphicOn_C_hinf (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    MeromorphicOn C HH := by
  intro s hs
  let r := (s.re - 1) / 2
  have hr : 0 < r := by change 1 < s.re at hs; dsimp [r]; linarith
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
  have hm := meromorphicAt_cauchy_of_gap (z := s)
    (fun p : NontrivialZeros × NontrivialZeros => zeroCoef p.1 * zeroCoef p.2)
    (fun p => (p.1 : ℂ) + p.2)
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
      (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hr hd E
    (by
      intro w hw p hp
      simpa only [sub_add_eq_sub_sub] using hgap w (ball_subset_closedBall hw) p hp)
  change MeromorphicAt (fun w => ∑' p : NontrivialZeros × NontrivialZeros,
    zeroCoef p.1 * zeroCoef p.2 / (w - p.1 - p.2)) s
  simpa only [sub_add_eq_sub_sub] using hm

theorem meromorphicOn_L (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    MeromorphicOn L univ := by
  classical
  intro s _
  have hfin : {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ |s.im| + 2}.Finite := by
    refine ((M1.finite_zeros_abs_im_le (|s.im| + 2)).preimage
      (Subtype.val_injective (p := fun ρ : ℂ => ρ ∈ NontrivialZeros)).injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, hρ⟩
  apply meromorphicAt_cauchy_of_gap (fun ρ : NontrivialZeros => zeroCoef ρ)
    (fun ρ => ρ) (summable_norm_zeroCoef_hinf hZ1 hZ2 hStir)
    (r := 1) (d := 1) one_pos one_pos hfin.toFinset
  intro w hw ρ hρ
  have hfar : |s.im| + 2 < |(ρ : ℂ).im| := by
    simpa only [hfin.mem_toFinset, mem_setOf_eq, not_le] using hρ
  have hnear : ‖w - s‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
  have him : |w.im| < |s.im| + 1 := by
    have ht := abs_sub_abs_le_abs_sub w.im s.im
    have hn := abs_im_le_norm (w - s)
    rw [sub_im] at hn
    linarith
  have ht := abs_sub_abs_le_abs_sub (ρ : ℂ).im w.im
  have hn := abs_im_le_norm (w - (ρ : ℂ))
  rw [sub_im, abs_sub_comm] at hn
  linarith

end GoldbachBoundaries.Phi2HInf
