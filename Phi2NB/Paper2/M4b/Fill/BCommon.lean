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

/-!
# Simple poles: the numerator of a function with a residue

* `exists_numerator_of_simplePole`: at a pole of order `≥ -1` with residue `R`, `(z - p) f(z)` agrees on `𝓝[≠] p`
  with a function `H` differentiable at `p` with `H p = R`.
* `isBigO_mul_sub_of_numerator`: then `g f - g(p) H(p)/(z - p)` is bounded near `p` (it is the slope of `g H`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- At a pole of order `≥ -1` with residue `R`, `(z - p) f(z)` is, near `p`, a function differentiable at `p`
with value `R`. -/
lemma exists_numerator_of_simplePole {f : ℂ → ℂ} {p R : ℂ} (hf : MeromorphicAt f p)
    (hord : -1 ≤ meromorphicOrderAt f p) (hres : HasResidue f p R) :
    ∃ H : ℂ → ℂ, DifferentiableAt ℂ H p ∧ H p = R ∧ ∀ᶠ z in 𝓝[≠] p, (z - p) * f z = H z := by
  have key : ∀ H : ℂ → ℂ, DifferentiableAt ℂ H p → (∀ᶠ z in 𝓝[≠] p, (z - p) * f z = H z) →
      ∃ H : ℂ → ℂ, DifferentiableAt ℂ H p ∧ H p = R ∧ ∀ᶠ z in 𝓝[≠] p, (z - p) * f z = H z := by
    intro H hH hev
    refine ⟨H, hH, ?_, hev⟩
    have h1 : Tendsto H (𝓝[≠] p) (𝓝 (H p)) := hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[≠] p) (𝓝 R) := (tendsto_congr' hev).mp hres
    exact tendsto_nhds_unique h1 h2
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    refine key (fun _ => 0) (differentiableAt_const _) ?_
    filter_upwards [htop] with z hz
    simp [hz]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨φ, hφ, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    have hn1 : -1 ≤ n := by
      rw [← hn] at hord
      have : ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := by simpa using hord
      exact_mod_cast this
    refine key (fun z => (z - p) ^ (n + 1).toNat * φ z)
      (((differentiableAt_id.sub_const p).pow _).mul hφ.differentiableAt) ?_
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hzp
    have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
    rw [hz, smul_eq_mul, ← mul_assoc]
    congr 1
    have hnat : ((n + 1).toNat : ℤ) = n + 1 := Int.toNat_of_nonneg (by omega)
    rw [← zpow_natCast, hnat, zpow_add_one₀ hzp']
    ring

/-- If `(z - p) F(z) = H(z)` near `p` with `H` differentiable at `p`, and `g` is differentiable at `p`, then
`g F - g(p) H(p)/(z - p)` is bounded on `𝓝[≠] p`: it is the slope of `g H` at `p`. -/
lemma isBigO_mul_sub_of_numerator {F g H : ℂ → ℂ} {p : ℂ} (hH : DifferentiableAt ℂ H p)
    (hg : DifferentiableAt ℂ g p) (hev : ∀ᶠ z in 𝓝[≠] p, (z - p) * F z = H z) :
    (fun z => g z * F z - g p * H p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (hg.mul hH).hasDerivAt)
  refine (hslope.isBigO_one ℂ).congr' ?_ EventuallyEq.rfl
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
  rw [slope_def_field]
  have hF : F z = H z / (z - p) := by rw [← hz]; field_simp
  rw [hF]
  simp only [Pi.mul_apply]
  field_simp

end GoldbachBoundaries.Paper2.M4b
