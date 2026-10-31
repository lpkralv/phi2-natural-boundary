import Phi2NB.Paper2.Defs
import Phi2NB.Defs
import Phi2NB.ZetaRealNonvanishing
import Phi2NB.SigmaFinite
import Phi2NB.SigmaMeromorphic
import Phi2NB.TIdentity.Assembly
import Phi2NB.Density
import Phi2NB.TBoundary
import Mathlib.MeasureTheory.Group.Prod
import Phi2NB.TIdentity.Basic
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.Module.Cardinality
import Phi2NB.Paper2.M1.Fill.BCommon
import Phi2NB.TIdentity.G8d_ContourShift
import Phi2NB.Paper2.M1.Fill.sum_zetaMult_window_le
import Phi2NB.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles
import Phi2NB.Paper2.M2.Fill.ncard_zeros_im_Icc_le
import Phi2NB.Paper2.M2.Fill.zetaMult_le_log
import Phi2NB.Paper2.M2.Fill.ACommon
import PrimeNumberTheoremAnd.Consequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Phi2NB.Paper2.M4b.Fill.BCommon
import Phi2NB.Paper2.M4b.Fill.isBigO_mul_sub_residue
import Phi2NB.Paper2.M5.Fill.order_residue_of_codiscrete_line
import Phi2NB.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep
import Phi2NB.Paper2.M5.Fill.exists_sep_height
import Phi2NB.Paper2.M5.Fill.QCommon

/-! The residue theorem on a rectangle with finitely many simple poles. If `f` is holomorphic on the closed rectangle
`[σ, σ'] × [-T, T]` off a finite set `S` of interior points, and `f - A p/(s - p)` is bounded near each `p ∈ S`, then
the normalised rectangle integral `RectangleIntegral'` of `f` is `∑_{p ∈ S} A p`. Write `f = g + ∑_{p ∈ S} A p/(s - p)`.
The principal parts integrate to `∑ A p` (PNT+'s residue theorem on rectangles, term by term). The rest `g` is
holomorphic on the rectangle off `S` and bounded near each point of `S`; filling in its limits there (Riemann's
removable singularity theorem) gives a function holomorphic on the closed rectangle that agrees with `g` on the
border, so Cauchy's theorem gives `0`. All differentiability assumptions are on the closed rectangle only. -/
noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M5
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem rectangleIntegral'_eq_sum_of_simplePoles_rect {σ σ' T : ℝ} {f : ℂ → ℂ} (S : Finset ℂ) (A : ℂ → ℂ)
    (hσ : σ ≤ σ') (hT : 0 ≤ T) (hS : ∀ p ∈ S, σ < p.re ∧ p.re < σ' ∧ |p.im| < T)
    (hf : DifferentiableOn ℂ f (Icc σ σ' ×ℂ Icc (-T) T \ (S : Set ℂ)))
    (hpole : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f ((σ : ℂ) - I * T) ((σ' : ℂ) + I * T) = ∑ p ∈ S, A p := by
  classical
  set z : ℂ := (σ : ℂ) - I * T with hz
  set w : ℂ := (σ' : ℂ) + I * T with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = -T := by simp [hz]
  have hwre : w.re = σ' := by simp [hw]
  have hwim : w.im = T := by simp [hw]
  have hTT : -T ≤ T := by linarith
  have hzw_re : z.re ≤ w.re := by rw [hzre, hwre]; exact hσ
  have hzw_im : z.im ≤ w.im := by rw [hzim, hwim]; exact hTT
  have hRstrip : Rectangle z w ⊆ Icc σ σ' ×ℂ Icc (-T) T := by
    intro x hx
    rw [Rectangle, hzre, hzim, hwre, hwim, uIcc_of_le hσ, uIcc_of_le hTT] at hx
    exact mem_reProdIm.mpr (mem_reProdIm.mp hx)
  have hnotB : ∀ p ∈ S, p ∉ RectangleBorder z w := by
    intro p hp hpB
    obtain ⟨h1, h2, h3⟩ := hS p hp
    rw [abs_lt] at h3
    simp only [RectangleBorder, hzre, hzim, hwre, hwim, mem_union, mem_reProdIm,
      mem_singleton_iff] at hpB
    rcases hpB with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩ <;> linarith
  have hBsub : ∀ x ∈ RectangleBorder z w, x ∈ Icc σ σ' ×ℂ Icc (-T) T \ (S : Set ℂ) := fun x hx =>
    ⟨hRstrip (rectangleBorder_subset_rectangle z w hx), fun hxS => hnotB x hxS hx⟩
  have hpnhds : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    rw [abs_lt] at h3
    rw [rectangle_mem_nhds_iff, hzre, hzim, hwre, hwim, uIoo_of_lt (h1.trans h2),
      uIoo_of_lt (by linarith)]
    exact mem_reProdIm.mpr ⟨⟨h1, h2⟩, h3⟩
  -- the principal part
  set P : ℂ → ℂ := fun s => ∑ p ∈ S, A p / (s - p) with hPdef
  have hPcont : ∀ p ∈ S, ContinuousOn (fun s => A p / (s - p)) (RectangleBorder z w) := by
    intro p hp s hs
    have hsp : s - p ≠ 0 := sub_ne_zero.mpr fun h => hnotB p hp (h ▸ hs)
    exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const) hsp).continuousWithinAt
  have hPint : RectangleIntegral' P z w = ∑ p ∈ S, A p := by
    rw [hPdef, rectangleIntegral'_finset_sum_D S _ hPcont]
    exact Finset.sum_congr rfl fun p hp => ResidueTheoremInRectangle hzw_re hzw_im (hpnhds p hp)
  have hPdiff : DifferentiableOn ℂ P (S : Set ℂ)ᶜ := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    have : ∀ p ∈ S, DifferentiableAt ℂ (fun s => A p / (s - p)) s := fun p hp =>
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (sub_ne_zero.mpr fun h => hs (h ▸ hp))
    exact DifferentiableAt.fun_sum this
  -- the rest
  set g : ℂ → ℂ := fun s => f s - P s with hgdef
  have hgdiff : DifferentiableOn ℂ g (Icc σ σ' ×ℂ Icc (-T) T \ (S : Set ℂ)) :=
    hf.sub (hPdiff.mono fun s hs => hs.2)
  have hadd : RectangleIntegral' f z w = RectangleIntegral' g z w + RectangleIntegral' P z w := by
    have hgB : RectangleBorderIntegrable g z w := (hgdiff.continuousOn.mono hBsub).rectangleBorder_integrable
    have hPB : RectangleBorderIntegrable P z w :=
      (continuousOn_finsetSum S hPcont).rectangleBorder_integrable
    have hfe : g + P = f := by funext s; simp [hgdef]
    calc RectangleIntegral' f z w = RectangleIntegral' (g + P) z w := by rw [hfe]
      _ = _ := by unfold RectangleIntegral'; rw [RectangleBorderIntegrable.add hgB hPB, smul_add]
  -- fill in the removable singularities of `g`
  set gt : ℂ → ℂ := fun s => if s ∈ S then limUnder (𝓝[≠] s) g else g s with hgtdef
  have hgt : DifferentiableOn ℂ gt (Rectangle z w) := by
    intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨h1, h2, -⟩ := hS x hxS
      have hsplit : g = (f - fun s => A x / (s - x)) - fun s => ∑ q ∈ S.erase x, A q / (s - q) := by
        funext s
        simp only [hgdef, hPdef, Pi.sub_apply]
        rw [← Finset.add_sum_erase S _ hxS]
        ring
      have hcont : ContinuousAt (fun s => ∑ q ∈ S.erase x, A q / (s - q)) x :=
        tendsto_finsetSum (S.erase x) fun q hq =>
          (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
            (sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm) :
            ContinuousAt (fun s => A q / (s - q)) x)
      have hbig : g =O[𝓝[≠] x] (1 : ℂ → ℂ) := by
        rw [hsplit]
        exact (hpole x hxS).sub ((hcont.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ)
      obtain ⟨U, hU, hUb⟩ := IsBigO_to_BddAbove hbig
      have hV : U ∩ Rectangle z w ∩ ((S.erase x : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 x :=
        inter_mem (inter_mem hU (hpnhds x hxS))
          ((S.erase x).finite_toSet.isClosed.compl_mem_nhds (by simp))
      obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
      have hball_notS : ∀ y ∈ ball x r, y ≠ x → y ∉ S := by
        intro y hy hyx hyS
        exact (hrV hy).2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyx, hyS⟩))
      have hd : DifferentiableOn ℂ g (ball x r \ {x}) := by
        refine hgdiff.mono fun y hy => ⟨?_, hball_notS y hy.1 hy.2⟩
        exact hRstrip (hrV hy.1).1.2
      have hb : BddAbove (norm ∘ g '' (ball x r \ {x})) :=
        hUb.mono (image_mono (sdiff_subset_sdiff_left fun y hy => (hrV hy).1.1))
      have hupd := differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds x hr) hd hb
      have heq : gt =ᶠ[𝓝 x] Function.update g x (limUnder (𝓝[≠] x) g) := by
        filter_upwards [ball_mem_nhds x hr] with y hy
        by_cases hyx : y = x
        · rw [hyx]; simp [hgtdef, hxS]
        · simp [hgtdef, hyx, hball_notS y hy hyx]
      exact ((hupd.differentiableAt (ball_mem_nhds x hr)).congr_of_eventuallyEq
        heq).differentiableWithinAt
    · have hSc : (S : Set ℂ)ᶜ ∈ 𝓝 x := S.finite_toSet.isClosed.compl_mem_nhds hxS
      have h1 : DifferentiableWithinAt ℂ g (Rectangle z w) x := by
        refine (hgdiff x ⟨hRstrip hx, hxS⟩).mono_of_mem_nhdsWithin ?_
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        exact ⟨_, hSc, fun y hy => ⟨hRstrip hy.2, hy.1⟩⟩
      refine h1.congr_of_eventuallyEq ?_ (by simp [hgtdef, hxS])
      filter_upwards [nhdsWithin_le_nhds hSc] with y hy
      have hy' : y ∉ S := hy
      simp [hgtdef, hy']
  have hg0 : RectangleIntegral' g z w = 0 := by
    have hcongr : RectangleIntegral g z w = RectangleIntegral gt z w := by
      apply RectangleIntegral_congr
      intro y hy
      have hyS : y ∉ S := fun h => hnotB y h hy
      simp [hgtdef, hyS]
    unfold RectangleIntegral'
    rw [hcongr, HolomorphicOn.vanishesOnRectangle hgt subset_rfl, smul_zero]
  rw [hadd, hg0, hPint, zero_add]

end GoldbachBoundaries.Paper2.M5
