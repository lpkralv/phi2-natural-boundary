import Phi2NB.Phi2.Proof.Defs
import Phi2NB.TIdentity.Assembly
import Phi2NB.Phi2.Fill.ACommon
import Phi2NB.Phi2.Fill.differentiable_e1L_E2L
import Phi2NB.Phi2.Fill.FL_eq_verticalIntegral'
import Phi2NB.Phi2.Fill.verticalIntegral'_kernelL_shift
import Phi2NB.Phi2.Fill.norm_hL_le
import Phi2NB.Phi2.Fill.phi2_identity

/-!
# The continuation of `Φ₂` to `ℍ`

Under RH, `Φ₂(s) = 2ψ(s-1)/(s-1) - 1/(Γ(s)(s-2)) + H(s)` on `σ > 2`, with `H = Hphi2` holomorphic on `ℍ`; hence
`Phi2c = phi2Main + Hphi2` is meromorphic on `ℍ`, with simple poles exactly at `2` and `1 + ρ`.

With `F = FL`, `h = hL = F - 1/t`: the Mellin transforms give `Γ(z)ψ(z) = 1/(z-1) + m₁(z) + e₁(z)` (`Re z > 1`) and
`Γ(s)Φ₂(s) = 1/(s-2) + 2 m₁(s-1) + R(s) + E₂(s)` (`Re s > 2`), with no RH. Eliminating `m₁(s-1)` and dividing by
`Γ(s) = (s-1)Γ(s-1)` gives the identity. `E₂`, `e₁` and `1/Γ` are entire, so `H` is holomorphic on `ℍ` as soon as
`R(s) = ∫_0^1 h(t)² t^{s-1} dt` is. RH enters only through `norm_hL_le`, `|h(t)| ≤ C_b t^{-b}` for `1/2 < b < 1`
(shift of the inverse Mellin line to `Re w = b`, using the bound `TIdentity.norm_negLogDerivZeta_le_log` for `ψ`),
which makes `R` holomorphic on `σ > 2b`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-! ## Lemmas proved in `Fill/`

One file per lemma, imported above: `differentiable_e1L_E2L`, `FL_eq_verticalIntegral'`,
`verticalIntegral'_kernelL_shift`, `norm_hL_le`, `phi2_identity`. -/

/-- **`R` is holomorphic on `ℍ`** (RH): near `s ∈ ℍ`, `|hL(t)|² ≤ C t^{-2b}` on `(0, 1]` for some `b ∈ (1/2, 1)`
with `2b < Re s` (`norm_hL_le`). -/
theorem differentiableOn_RrL (hRH : RiemannHypothesis) : DifferentiableOn ℂ RrL HH := by
  intro s hs
  have hs1 : 1 < s.re := hs
  set b : ℝ := min ((1 + s.re) / 4) (3 / 4) with hbdef
  have hb : 1 / 2 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h2b : 2 * b < s.re := by
    have : b ≤ (1 + s.re) / 4 := min_le_left _ _
    linarith
  obtain ⟨hcont, C, hC⟩ := norm_hL_le hRH hb hb1
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ((hL t ^ 2 : ℝ) : ℂ))
      (volume.restrict (Ioc 0 1)) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((hcont.mono Ioc_subset_Ioi_self).pow 2)).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖((hL t ^ 2 : ℝ) : ℂ)‖ ≤ C ^ 2 * t ^ (-(2 * b)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : |hL t| ^ 2 ≤ (C * t ^ (-b)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC t ht0) 2
    rw [sq_abs] at h1
    calc hL t ^ 2 ≤ (C * t ^ (-b)) ^ 2 := h1
      _ = C ^ 2 * t ^ (-(2 * b)) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ (-b)) 2, ← Real.rpow_mul ht0.le]
        ring_nf
  have hD := TIdentity.differentiableOn_integral_Ioc_cpow hmeas hbound
  exact (hD.differentiableAt ((isOpen_halfPlane _).mem_nhds h2b)).differentiableWithinAt

/-- **`H` is holomorphic on `ℍ`** (RH): `E₂`, `e₁(· - 1)` and `1/Γ` are entire and `R` is holomorphic on `ℍ`. -/
theorem differentiableOn_Hphi2 (hRH : RiemannHypothesis) : DifferentiableOn ℂ Hphi2 HH := by
  obtain ⟨hd1, hd2⟩ := differentiable_e1L_E2L
  have he : Differentiable ℂ fun s : ℂ => e1L (s - 1) := hd1.comp (differentiable_id.sub_const 1)
  exact (((hd2.differentiableOn).sub ((he.const_mul 2).differentiableOn)).add
    (differentiableOn_RrL hRH)).mul differentiable_one_div_Gamma.differentiableOn

/-- `phi2Main` is meromorphic on `ℂ`. -/
theorem meromorphicOn_phi2Main : MeromorphicOn phi2Main univ := by
  intro s _
  have h1 : MeromorphicAt (fun s : ℂ => negLogDerivZeta (s - 1)) s :=
    MeromorphicAt.comp_analyticAt (f := negLogDerivZeta) (g := fun s : ℂ => s - 1)
      (meromorphicAt_negLogDerivZeta (s - 1)) (by fun_prop)
  have hG : MeromorphicAt (fun s : ℂ => (Gamma s)⁻¹) s :=
    (differentiable_one_div_Gamma.analyticAt s).meromorphicAt.congr
      (Filter.Eventually.of_forall fun z => by simp)
  have h2 : MeromorphicAt (fun s : ℂ => 1 / (Gamma s * (s - 2))) s := by
    have : (fun s : ℂ => 1 / (Gamma s * (s - 2))) = fun s => (Gamma s)⁻¹ * (s - 2)⁻¹ := by
      funext z; rw [one_div, mul_inv]
    rw [this]
    exact hG.mul (analyticAt_id.sub analyticAt_const).meromorphicAt.inv
  have h3 : MeromorphicAt (fun s : ℂ => s - 1) s := (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact ((MeromorphicAt.const 2 s |>.mul h1).div h3).sub h2

/-- `ψ(s - 1)` is analytic at every `s` with `Re s > 1` off `{2} ∪ {1 + ρ}` (no RH): a zero of `ζ` with
`0 < Re w < 1` is a non-trivial zero by definition, and `ζ ≠ 0` on `Re w ≥ 1`. -/
theorem analyticAt_negLogDerivZeta_sub_one {s : ℂ} (hs : s ∈ HH) (hP : s ∉ phi2Poles) :
    AnalyticAt ℂ (fun s : ℂ => negLogDerivZeta (s - 1)) s := by
  have hs1 : 1 < s.re := hs
  have h2 : s - 1 ≠ 1 := fun h => hP (Or.inl (by rw [mem_singleton_iff]; linear_combination h))
  have hz : riemannZeta (s - 1) ≠ 0 := by
    intro hz
    by_cases hre : 1 ≤ (s - 1).re
    · exact riemannZeta_ne_zero_of_one_le_re hre hz
    · refine hP (Or.inr ⟨s - 1, ⟨hz, ?_, ?_⟩, by ring⟩)
      · simp; linarith
      · linarith [not_le.mp hre]
  exact AnalyticAt.comp (g := negLogDerivZeta) (f := fun s : ℂ => s - 1)
    (analyticAt_negLogDerivZeta h2 hz) (analyticAt_id.sub analyticAt_const)

/-- **The continuation and its poles** (RH): `Phi2c` is meromorphic on `ℍ`, equals `Φ₂` on `σ > 2`, is analytic off
`{2} ∪ {1 + ρ}`, and has a simple pole with residue `1` at `2` and `-2m(ρ)/ρ` at `1 + ρ`. RH is used only for
`differentiableOn_Hphi2`; `ψ(s-1)` is analytic on `σ > 1` off `{2} ∪ {1 + ρ}` unconditionally (a zero of `ζ` with
`0 < Re < 1` is in `NontrivialZeros` by definition, `ζ ≠ 0` on `Re ≥ 1`). -/
theorem phi2_continuation (hRH : RiemannHypothesis) :
    MeromorphicOn Phi2c HH ∧ EqOn Phi2c Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ Phi2c (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt Phi2c α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue Phi2c α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0 := by
  classical
  have hHan : AnalyticOnNhd ℂ Hphi2 HH := (differentiableOn_Hphi2 hRH).analyticOnNhd (isOpen_halfPlane 1)
  have hGinv : ∀ s, AnalyticAt ℂ (fun s => (Gamma s)⁻¹) s := fun s =>
    (differentiable_one_div_Gamma.analyticAt s).congr (Filter.Eventually.of_forall fun z => by simp)
  have hterm2 : (fun s : ℂ => 1 / (Gamma s * (s - 2))) = fun s => (Gamma s)⁻¹ * (s - 2)⁻¹ := by
    funext s; rw [one_div, mul_inv]
  have hPHH : ∀ α ∈ phi2Poles, α ∈ HH := by
    rintro α (h | ⟨ρ, hρ, rfl⟩)
    · rw [mem_singleton_iff.mp h]; norm_num [halfPlane]
    · show 1 < (1 + ρ).re
      simp only [add_re, one_re]; linarith [hρ.2.1]
  have hmeroF : MeromorphicOn Phi2c HH := fun s hs =>
    (meromorphicOn_phi2Main s (mem_univ s)).add (hHan s hs).meromorphicAt
  -- residues
  set resF : ℂ → ℂ := fun α => if α = 2 then 1 else -(2 * (zetaMult (α - 1) : ℂ)) / (α - 1) with hresF
  have hne1 : ∀ ρ ∈ NontrivialZeros, (1 + ρ : ℂ) ≠ 2 := by
    intro ρ hρ h
    have := congrArg Complex.re h
    simp only [add_re, one_re] at this
    norm_num at this
    linarith [hρ.2.2]
  have hρ0 : ∀ ρ ∈ NontrivialZeros, ρ ≠ 0 := by
    rintro ρ hρ rfl; simp [NontrivialZeros] at hρ
  have hResF : ∀ α ∈ phi2Poles, HasResidue Phi2c α (resF α) := by
    intro α hα
    have hαH := hPHH α hα
    have hH : AnalyticAt ℂ Hphi2 α := hHan α hαH
    rcases hα with h2 | ⟨ρ, hρ, rfl⟩
    · rw [mem_singleton_iff] at h2
      subst h2
      have h1 : HasResidue (fun s => negLogDerivZeta (s - 1)) 2 1 := by
        have := hasResidue_negLogDerivZeta_one.comp_sub_const 1
        rwa [one_add_one_eq_two] at this
      have hc : ContinuousAt (fun s : ℂ => 2 / (s - 1)) 2 :=
        continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by norm_num)
      have h1' : HasResidue (fun s => 2 * negLogDerivZeta (s - 1) / (s - 1)) 2 2 := by
        have := h1.mul_continuousAt' hc
        convert this using 1
        · funext s; ring
        · norm_num
      have h3 := (h1'.sub hasResidue_one_div_Gamma_mul_sub_two).add_analyticAt hH
      have : resF 2 = 2 - 1 := by simp [hresF]; norm_num
      rw [this]
      exact h3
    · have h1 : HasResidue (fun s => negLogDerivZeta (s - 1)) (1 + ρ) (-(zetaMult ρ : ℂ)) := by
        have := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).1.comp_sub_const 1
        rwa [add_comm] at this
      have hc : ContinuousAt (fun s : ℂ => 2 / (s - 1)) (1 + ρ) :=
        continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by simpa using hρ0 ρ hρ)
      have h1' : HasResidue (fun s => 2 * negLogDerivZeta (s - 1) / (s - 1)) (1 + ρ)
          (-(2 * (zetaMult ρ : ℂ)) / ρ) := by
        have := h1.mul_continuousAt' hc
        convert this using 1
        · funext s; ring
        · simp only [add_sub_cancel_left]; ring
      have h2 : HasResidue (fun s => 1 / (Gamma s * (s - 2))) (1 + ρ) 0 := by
        rw [hterm2]
        exact hasResidue_zero_of_analyticAt
          ((hGinv _).mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (hne1 ρ hρ))))
      have h3 := (h1'.sub h2).add_analyticAt hH
      have : resF (1 + ρ) = -(2 * (zetaMult ρ : ℂ)) / ρ - 0 := by
        simp [hresF, hne1 ρ hρ]
      rw [this]
      exact h3
  have hresF_ne : ∀ α ∈ phi2Poles, resF α ≠ 0 := by
    rintro α (h2 | ⟨ρ, hρ, rfl⟩)
    · rw [mem_singleton_iff.mp h2]; simp [hresF]
    · have hm := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).2
      have hm' : (zetaMult ρ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [hresF, hne1 ρ hρ, ↓reduceIte, add_sub_cancel_left]
      exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero two_ne_zero hm')) (hρ0 ρ hρ)
  refine ⟨hmeroF, fun s hs => (phi2_identity hs).symm, ?_, ?_, resF, hResF, ⟨by simp [hresF], ?_⟩,
    hresF_ne⟩
  · -- analytic off the poles
    rintro s ⟨hs, hsP⟩
    have hs2 : s ≠ 2 := fun h => hsP (Or.inl (by rw [h]; rfl))
    have hs1' : s - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [show 1 < s.re from hs]
    have ht2 : AnalyticAt ℂ (fun s : ℂ => 1 / (Gamma s * (s - 2))) s := by
      rw [hterm2]
      exact (hGinv s).mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs2))
    exact (((analyticAt_const.mul (analyticAt_negLogDerivZeta_sub_one hs hsP)).div
      (analyticAt_id.sub analyticAt_const) hs1').sub ht2).add (hHan s hs)
  · intro α hα
    rw [(hResF α hα).meromorphicOrderAt_eq_neg_one (hmeroF α (hPHH α hα)) (hresF_ne α hα)]
    rfl
  · intro ρ hρ
    simp [hresF, hne1 ρ hρ]

end GoldbachBoundaries.Phi2Proof
