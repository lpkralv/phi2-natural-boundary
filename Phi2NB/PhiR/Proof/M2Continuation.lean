import Phi2NB.PhiR.Proof.M1Mellin
import Phi2NB.PhiR.Fill.analyticOnNhd_PhiRc
import Phi2NB.PhiR.Fill.hasResidue_PhiRc

/-!
# Step M2: the continuation of `Φ_r` to `σ > r - 1`, its poles and residues

Under RH, `PhiRc r = f₄ · Phi2c(· - r + 2) + rest` is meromorphic on `σ > r - 1`
(first paragraph of the proof of Theorem 7.1): `f₄ = C(r,2)Γ(s-r+2)/Γ(s)` is holomorphic and non-zero on `σ > r - 2`, `rest`
is meromorphic on `σ > r - 3/2`, and `Phi2c(· - r + 2)` is meromorphic on `σ > r - 1` (`Phi2Proof.phi2_continuation`).
Its poles there are `r` (residue `1/(r-1)!`) and `r - 1 + ρ` (residue `-r m(ρ) Γ(ρ)/Γ(ρ + r - 1)`), all simple.

Lemmas proved in `Fill/`: `analyticOnNhd_PhiRc`, `hasResidue_PhiRc`. Proved in this file: `meromorphicAt_Gamma`, `analyticAt_phiRCoef`,
`phiRCoef_ne_zero`, `meromorphicOn_phiRRest`, `meromorphicOn_PhiRc`, `phiRPoles_subset_halfPlane`,
`phiR_continuation`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- `Γ` is meromorphic at every point (`Γ = (1/Γ)⁻¹`, `1/Γ` entire). -/
theorem meromorphicAt_Gamma (s : ℂ) : MeromorphicAt Gamma s := by
  have h : MeromorphicAt (fun z : ℂ => ((Gamma z)⁻¹)⁻¹) s :=
    ((differentiable_one_div_Gamma.analyticAt s).meromorphicAt.congr
      (Filter.Eventually.of_forall fun z => by simp)).inv
  exact h.congr (Filter.Eventually.of_forall fun z => by simp)

/-- `1/Γ` is analytic everywhere. -/
theorem analyticAt_inv_Gamma (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => (Gamma z)⁻¹) s :=
  (differentiable_one_div_Gamma.analyticAt s).congr (Filter.Eventually.of_forall fun z => by simp)

/-- `Γ` is analytic at every `s` with `Re s > 0`. -/
theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  -- `Γ` is differentiable on the open set `{Re > 0}`, hence analytic there
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gamma {z : ℂ | 0 < z.re} := fun z hz => by
    refine (Complex.differentiableAt_Gamma z fun m h => ?_).differentiableWithinAt
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    have hz' : 0 < z.re := hz
    linarith
  exact hd.analyticAt (hU.mem_nhds hs)

/-- **`f₄` is analytic on `σ > r - 2`**: `Γ(s - r + 2)` with `Re(s - r + 2) > 0`, and `1/Γ` entire. -/
theorem analyticAt_phiRCoef {r : ℕ} {s : ℂ} (hs : (r : ℝ) - 2 < s.re) : AnalyticAt ℂ (phiRCoef r) s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => Gamma (z - r + 2)) s := by
    refine AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - r + 2) ?_ (by fun_prop)
    exact analyticAt_Gamma_of_re_pos (by simp; linarith)
  exact (analyticAt_const.mul h1).mul (analyticAt_inv_Gamma s)

/-- **`f₄` has no zeros on `σ > r - 2`** for `r ≥ 2`: `C(r,2) ≠ 0`, `Γ` has no zeros, and
`Γ(s) ≠ 0` is finite for `Re s > 0`. -/
theorem phiRCoef_ne_zero {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) - 2 < s.re) : phiRCoef r s ≠ 0 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hC : (cC r : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, cC]
    have : 0 < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  have h1 : Gamma (s - r + 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  exact mul_ne_zero (mul_ne_zero hC h1) (inv_ne_zero h2)

/-- **The rest is meromorphic on `σ > r - 3/2`** (RH): `Γ(s-r+1)` and `ψ(s-r+1)` are meromorphic on `ℂ`,
`A_r/(s-r)` is rational, `K_r` is holomorphic there (`differentiableOn_KR`), `1/Γ` is entire. -/
theorem meromorphicOn_phiRRest (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (phiRRest r) (halfPlane ((r : ℝ) - 3 / 2)) := by
  intro s hs
  have hK : AnalyticAt ℂ (KR r) s :=
    (differentiableOn_KR hRH hr).analyticAt ((isOpen_halfPlane _).mem_nhds hs)
  have hG1 : MeromorphicAt (fun z : ℂ => Gamma (z - r + 1)) s :=
    MeromorphicAt.comp_analyticAt (f := Gamma) (g := fun z : ℂ => z - r + 1) (meromorphicAt_Gamma _)
      (by fun_prop)
  have hψ : MeromorphicAt (fun z : ℂ => negLogDerivZeta (z - r + 1)) s :=
    MeromorphicAt.comp_analyticAt (f := negLogDerivZeta) (g := fun z : ℂ => z - r + 1)
      (meromorphicAt_negLogDerivZeta _) (by fun_prop)
  have hA : MeromorphicAt (fun z : ℂ => (cA r : ℂ) / (z - r)) s :=
    (MeromorphicAt.const _ s).div (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact ((((MeromorphicAt.const _ s).mul hG1).mul hψ).add hA |>.add hK.meromorphicAt).mul
    (analyticAt_inv_Gamma s).meromorphicAt

/-- **`PhiRc r` is meromorphic on `σ > r - 1`** (RH): `Phi2c` is meromorphic on `ℍ`
(`phi2_continuation`), so `Phi2c(s - r + 2)` is meromorphic where `Re(s - r + 2) > 1`. -/
theorem meromorphicOn_PhiRc (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (PhiRc r) (halfPlane ((r : ℝ) - 1)) := by
  intro s hs
  have hs' : (r : ℝ) - 1 < s.re := hs
  have hP2 : MeromorphicAt (fun z : ℂ => Phi2c (z - r + 2)) s := by
    refine MeromorphicAt.comp_analyticAt (f := Phi2c) (g := fun z : ℂ => z - r + 2) ?_ (by fun_prop)
    refine (phi2_continuation hRH).1 _ ?_
    show 1 < (s - r + 2).re
    simp; linarith
  have hR : MeromorphicAt (phiRRest r) s := meromorphicOn_phiRRest hRH hr s (by
    show (r : ℝ) - 3 / 2 < s.re; linarith)
  exact ((analyticAt_phiRCoef (by linarith)).meromorphicAt.mul hP2).add hR

/-- The pole set lies in `σ > r - 1`, unconditionally (`Re(r - 1 + ρ) = r - 1 + Re ρ`). -/
theorem phiRPoles_subset_halfPlane (r : ℕ) : phiRPoles r ⊆ halfPlane ((r : ℝ) - 1) := by
  rintro s (hs | ⟨ρ, hρ, rfl⟩)
  · rw [mem_singleton_iff.mp hs]
    show (r : ℝ) - 1 < ((r : ℂ)).re
    simp
  · show (r : ℝ) - 1 < (((r : ℂ) - 1) + ρ).re
    simp only [add_re, sub_re, natCast_re, one_re]
    linarith [hρ.2.1]

/-- **`PhiRc r` is analytic on `σ > r - 1` off the poles** (RH). For `s` there with `s ≠ r`, `s ≠ r - 1 + ρ`:
`f₄` is analytic (`analyticAt_phiRCoef`); `s - r + 2 ∈ ℍ ∖ phi2Poles`, so `Phi2c(s - r + 2)` is analytic
(`phi2_continuation`); `Γ(s - r + 1)` is analytic (`Re > 0`); `ψ(s - r + 1)` is analytic
(`s - r + 1 ≠ 1`, and `ζ(s - r + 1) ≠ 0`: a zero with real part in `(0,1)` is in `NontrivialZeros`, and `ζ ≠ 0` on
`Re ≥ 1`; the argument of `Phi2Proof.analyticAt_negLogDerivZeta_sub_one`); `A_r/(s - r)` is analytic; `K_r` is
holomorphic (`differentiableOn_KR`). -/
theorem analyticOnNhd_PhiRc (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    AnalyticOnNhd ℂ (PhiRc r) (halfPlane ((r : ℝ) - 1) \ phiRPoles r) :=
  FillB.analyticOnNhd_PhiRc' hRH hr

/-- **Residues of `PhiRc r`** (RH): residue `1/(r-1)!` at `r` and `-r m(ρ) Γ(ρ)/Γ(ρ + r - 1)` at `r - 1 + ρ`, all
non-zero.
Proof, with the `HasResidue` algebra of `ResidueAPI` (`mul_continuousAt'`, `add`, `sub`, `add_analyticAt`,
`comp_sub_const`), as in `Phi2Proof.phi2_continuation`, after writing `PhiRc` as
`(C Γ(s-r+2) Phi2c(s-r+2) + B Γ(s-r+1) ψ(s-r+1) + A/(s-r) + K(s)) · Γ(s)⁻¹`:
* at `s = r`: `Phi2c(s-r+2)` has residue `1` (`phi2_continuation`, translated), `ψ(s-r+1)` residue `1`
  (`hasResidue_negLogDerivZeta_one`), `A/(s-r)` residue `A`; the other factors are continuous with `Γ(2) = Γ(1) = 1`,
  so the bracket has residue `C + B + A = 1`, times `Γ(r)⁻¹ = 1/(r-1)!` (`Complex.Gamma_nat_eq_factorial`);
* at `s = r - 1 + ρ`: `Phi2c(s-r+2)` has residue `-2m(ρ)/ρ`, `ψ(s-r+1)` residue `-m(ρ)`
  (`hasResidue_negLogDerivZeta_of_mem_nontrivialZeros`); with `Γ(ρ+1) = ρΓ(ρ)` the bracket has residue
  `-2C m(ρ)Γ(ρ) - B m(ρ)Γ(ρ) = -r m(ρ) Γ(ρ)`; times `Γ(r - 1 + ρ)⁻¹`.
Non-zero: `(r-1)! ≠ 0`; `m(ρ) ≥ 1`, `Γ(ρ) ≠ 0`, `Γ(ρ + r - 1) ≠ 0` finite (`Re > 0`). The two clauses of
`HasPhiRResidues` do not conflict (`Re(r - 1 + ρ) < r`). -/
theorem hasResidue_PhiRc (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue (PhiRc r) α (res α)) ∧ HasPhiRResidues r res ∧
      ∀ α ∈ phiRPoles r, res α ≠ 0 :=
  FillB.hasResidue_PhiRc' hRH hr

/-- **The continuation and its poles** (RH; from the lemmas above, as `Phi2Proof.phi2_continuation`):
`PhiRc r` is meromorphic on `σ > r - 1`, equals `Φ_r` on `σ > r`, is analytic off `phiRPoles r`, and has a simple
pole with the residues of `HasPhiRResidues` at each point of `phiRPoles r`. -/
theorem phiR_continuation (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (PhiRc r) (halfPlane ((r : ℝ) - 1)) ∧ EqOn (PhiRc r) (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ (PhiRc r) (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt (PhiRc r) α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue (PhiRc r) α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0 := by
  obtain ⟨res, hres, hHas, hne⟩ := hasResidue_PhiRc hRH hr
  have hmero := meromorphicOn_PhiRc hRH hr
  refine ⟨hmero, fun s hs => (PhiR_eq_PhiRc hr hs).symm, analyticOnNhd_PhiRc hRH hr, ?_,
    res, hres, hHas, hne⟩
  intro α hα
  rw [(hres α hα).meromorphicOrderAt_eq_neg_one (hmero α (phiRPoles_subset_halfPlane r hα)) (hne α hα)]
  rfl

end GoldbachBoundaries.PhiRProof
