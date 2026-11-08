import Phi2NB.PhiR.Proof.M1Mellin

/-! `exists_RR` (step M4). The remainder `RRraw r` has a holomorphic version on `σ > r - 3/2` (RH).

Explicit version: with `Z = dslope g 1`, `g = update ((w - 1) ζ(w)) 1 1` (entire, so `Z(w) = ζ(w) - 1/(w-1)` off `1`
is entire), and `dslope (1/Γ) r` (entire),
`R(s) = K_r(s)/Γ(s) + A_r (dslope (1/Γ) r s - Z(s - r + 1)/(r-1)!)`,
which equals `RRraw r s` for `s ≠ r` because `1/Γ(r) = 1/(r-1)!`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillC

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- `(w - 1) ζ(w)`, with the value `1` at `w = 1`. -/
def zetaRes : ℂ → ℂ := Function.update (fun w => (w - 1) * riemannZeta w) 1 1

/-- `(w - 1) ζ(w)` (with value `1` at `1`) is entire. -/
theorem differentiable_zetaRes : Differentiable ℂ zetaRes := by
  have hoff : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ zetaRes w := by
    intro w hw
    have hd : DifferentiableAt ℂ (fun w => (w - 1) * riemannZeta w) w :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hw] with z hz
    simp [zetaRes, Function.update_of_ne hz]
  intro w
  by_cases hw : w = 1
  · subst hw
    have hcont : ContinuousAt zetaRes 1 := by
      unfold zetaRes
      rw [continuousAt_update_same]
      exact riemannZeta_residue_one
    have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ zetaRes z := by
      filter_upwards [self_mem_nhdsWithin] with z hz using hoff z hz
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hev hcont).differentiableAt
  · exact hoff w hw

/-- `ζ(w) - 1/(w - 1)` continued across `w = 1`: `dslope zetaRes 1`, entire. -/
theorem differentiable_dslope_zetaRes : Differentiable ℂ (dslope zetaRes 1) := by
  have h := (Complex.differentiableOn_dslope (f := zetaRes) (s := univ) (c := 1) univ_mem).mpr
    differentiable_zetaRes.differentiableOn
  exact fun w => (h w (mem_univ _)).differentiableAt univ_mem

theorem dslope_zetaRes_of_ne {w : ℂ} (hw : w ≠ 1) :
    dslope zetaRes 1 w = riemannZeta w - 1 / (w - 1) := by
  have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  rw [dslope_of_ne _ hw, slope_def_field, zetaRes, Function.update_of_ne hw, Function.update_self]
  field_simp

theorem differentiable_inv_Gamma : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
  have h := differentiable_one_div_Gamma
  intro z
  exact (h z).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp)

theorem differentiable_dslope_inv_Gamma (c : ℂ) : Differentiable ℂ (dslope (fun z : ℂ => (Gamma z)⁻¹) c) := by
  have h := (Complex.differentiableOn_dslope (f := fun z : ℂ => (Gamma z)⁻¹) (s := univ) (c := c)
    univ_mem).mpr differentiable_inv_Gamma.differentiableOn
  exact fun w => (h w (mem_univ _)).differentiableAt univ_mem

/-- `Γ(r) = (r - 1)!` for `r ≥ 1`. -/
theorem Gamma_natCast_eq_factorial {r : ℕ} (hr : 1 ≤ r) : Gamma (r : ℂ) = ((r - 1).factorial : ℂ) := by
  have h := Complex.Gamma_nat_eq_factorial (r - 1)
  have hc : (((r - 1 : ℕ) : ℂ) + 1) = (r : ℂ) := by rw [Nat.cast_sub hr]; ring
  rwa [hc] at h

/-- **The remainder has a holomorphic version on `σ > r - 3/2`** (RH). -/
theorem exists_RR' (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      ∀ s ∈ halfPlane ((r : ℝ) - 3 / 2), s ≠ (r : ℂ) → R s = RRraw r s := by
  refine ⟨fun s => KR r s * (Gamma s)⁻¹ + (cA r : ℂ) *
    (dslope (fun z : ℂ => (Gamma z)⁻¹) (r : ℂ) s - dslope zetaRes 1 (s - r + 1) / ((r - 1).factorial : ℂ)),
    ?_, ?_⟩
  · have hK := differentiableOn_KR hRH hr
    have hZ : Differentiable ℂ fun s : ℂ => dslope zetaRes 1 (s - r + 1) :=
      differentiable_dslope_zetaRes.comp ((differentiable_id.sub_const _).add_const _)
    refine (hK.mul differentiable_inv_Gamma.differentiableOn).add
      (DifferentiableOn.const_mul ?_ _)
    exact ((differentiable_dslope_inv_Gamma _).sub (hZ.div_const _)).differentiableOn
  · intro s _ hs
    have hsr : s - (r : ℂ) ≠ 0 := sub_ne_zero.mpr hs
    have hw : s - r + 1 ≠ 1 := by
      intro h; apply hsr; linear_combination h
    have hfact : ((r - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    dsimp only
    rw [dslope_zetaRes_of_ne hw, dslope_of_ne _ hs, slope_def_field, Gamma_natCast_eq_factorial (by omega),
      RRraw]
    have e : s - (r : ℂ) + 1 - 1 = s - r := by ring
    rw [e]
    field_simp
    ring

end GoldbachBoundaries.PhiRProof.FillC
