import Phi2NB.PhiR.Fill.BCommon

/-!
# `hasResidue_PhiRc` (step M2)

`PhiRc r s = f₄(s) Phi2c(s - r + 2) + (B Γ(s-r+1) ψ(s-r+1) + A/(s-r) + K(s)) Γ(s)⁻¹`. Residues, with the
`HasResidue` algebra:

* at `s = r`: `Phi2c(s - r + 2)` has residue `1` (translated from `2`), times `f₄(r) = C Γ(2)/Γ(r)`;
  `ψ(s - r + 1)` has residue `1`, times `B Γ(1)`; `A/(s - r)` has residue `A`; `K` is analytic. Total
  `(C + B + A)/Γ(r) = 1/(r-1)!`.
* at `s = r - 1 + ρ`: `Phi2c(s - r + 2)` has residue `-2m(ρ)/ρ`, times `f₄ = C Γ(1+ρ)/Γ(s) = C ρ Γ(ρ)/Γ(s)`;
  `ψ(s - r + 1)` has residue `-m(ρ)`, times `B Γ(ρ)`; `A/(s - r)` and `K` are analytic. Total
  `-m(ρ) Γ(ρ) (2C + B)/Γ(s) = -r m(ρ) Γ(ρ)/Γ(s)`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillB

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.PhiRProof

/-- The residue function: `1/(r-1)!` at `r`, `-r m(ρ) Γ(ρ)/Γ(ρ + r - 1)` at `r - 1 + ρ` (written with
`ρ = α - (r - 1)`). -/
def fillB_resR (r : ℕ) (α : ℂ) : ℂ :=
  if α = (r : ℂ) then 1 / ((r - 1).factorial : ℂ)
  else -((r : ℂ) * (zetaMult (α - ((r : ℂ) - 1)) : ℂ)) * Gamma (α - ((r : ℂ) - 1)) /
    Gamma ((α - ((r : ℂ) - 1)) + ((r : ℂ) - 1))

/-- Transport a residue along a pointwise equality of functions and an equality of values. -/
theorem fillB_hasResidue_of_eq {f g : ℂ → ℂ} {a c c' : ℂ} (h : HasResidue f a c) (hf : ∀ z, f z = g z)
    (hc : c = c') : HasResidue g a c' := by
  have : f = g := funext hf
  subst this hc
  exact h

/-- The `Phi2c` term: if `Phi2c` has residue `c` at `α - r + 2`, then `f₄(s) Phi2c(s - r + 2)` has residue
`c f₄(α)` at `α` (for `Re α > r - 2`, where `f₄` is analytic). -/
theorem fillB_hasResidue_T1 {r : ℕ} {α c : ℂ} (hα : (r : ℝ) - 2 < α.re)
    (h : HasResidue Phi2c (α - r + 2) c) :
    HasResidue (fun z => phiRCoef r z * Phi2c (z - r + 2)) α (c * phiRCoef r α) := by
  have h1 := h.comp_sub_const ((r : ℂ) - 2)
  rw [show α - r + 2 + ((r : ℂ) - 2) = α by ring] at h1
  have h2 := h1.mul_continuousAt' (fillB_analyticAt_phiRCoef hα).continuousAt
  refine fillB_hasResidue_of_eq h2 (fun z => ?_) rfl
  rw [show z - ((r : ℂ) - 2) = z - r + 2 by ring]
  ring

/-- The `ψ` term: if `ψ` has residue `c` at `α - r + 1`, then `ψ(s - r + 1)` has residue `c` at `α`. -/
theorem fillB_hasResidue_psi_shift {r : ℕ} {α c : ℂ} (h : HasResidue negLogDerivZeta (α - r + 1) c) :
    HasResidue (fun z => negLogDerivZeta (z - r + 1)) α c := by
  have h1 := h.comp_sub_const ((r : ℂ) - 1)
  rw [show α - r + 1 + ((r : ℂ) - 1) = α by ring] at h1
  refine fillB_hasResidue_of_eq h1 (fun z => ?_) rfl
  rw [show z - ((r : ℂ) - 1) = z - r + 1 by ring]

/-- The rest: on `σ > r - 1` (RH), from the residues `cψ` of `ψ(s - r + 1)` and `cA'` of `A/(s - r)` at `α`,
`phiRRest r` has residue `(cψ B Γ(α - r + 1) + cA') Γ(α)⁻¹`. -/
theorem fillB_hasResidue_phiRRest (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) {α cψ cA' : ℂ}
    (hα : (r : ℝ) - 1 < α.re) (hψ : HasResidue (fun z => negLogDerivZeta (z - r + 1)) α cψ)
    (hA : HasResidue (fun z => (cA r : ℂ) / (z - r)) α cA') :
    HasResidue (phiRRest r) α ((cψ * ((cB r : ℂ) * Gamma (α - r + 1)) + cA') * (Gamma α)⁻¹) := by
  have hG1 : ContinuousAt (fun z : ℂ => (cB r : ℂ) * Gamma (z - r + 1)) α :=
    (analyticAt_const.mul (AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - r + 1)
      (fillB_analyticAt_Gamma_of_re_pos (by simp; linarith)) (by fun_prop))).continuousAt
  have hK : AnalyticAt ℂ (KR r) α :=
    (differentiableOn_KR hRH hr).analyticAt ((isOpen_halfPlane _).mem_nhds
      (show (r : ℝ) - 3 / 2 < α.re by linarith))
  have h := (((hψ.mul_continuousAt' hG1).add' hA).add_analyticAt hK).mul_continuousAt'
    (fillB_analyticAt_inv_Gamma α).continuousAt
  refine fillB_hasResidue_of_eq h (fun z => ?_) rfl
  simp only [phiRRest]
  ring

/-- `Γ(2) = 1`. -/
theorem fillB_Gamma_two : Gamma (2 : ℂ) = 1 := by
  have h := Gamma_add_one 1 one_ne_zero
  rw [Gamma_one, mul_one, one_add_one_eq_two] at h
  exact h

/-- **Residues of `PhiRc r`** (RH). Statement of `PhiRProof.hasResidue_PhiRc`, verbatim. -/
theorem hasResidue_PhiRc' (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue (PhiRc r) α (res α)) ∧ HasPhiRResidues r res ∧
      ∀ α ∈ phiRPoles r, res α ≠ 0 := by
  obtain ⟨-, -, -, -, res2, hres2, ⟨hres2_two, hres2_rho⟩, -⟩ := phi2_continuation hRH
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hne : ∀ ρ ∈ NontrivialZeros, ((r : ℂ) - 1) + ρ ≠ (r : ℂ) := by
    intro ρ hρ h
    have := congrArg Complex.re h
    simp at this
    linarith [hρ.2.2]
  have hsub : ∀ ρ : ℂ, ((r : ℂ) - 1) + ρ - ((r : ℂ) - 1) = ρ := fun ρ => by ring
  refine ⟨fillB_resR r, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro α (hα | ⟨ρ, hρ, rfl⟩)
    · rw [mem_singleton_iff] at hα
      subst hα
      have hre : (r : ℝ) - 1 < ((r : ℂ)).re := by simp
      have hP2 : HasResidue Phi2c ((r : ℂ) - r + 2) 1 := by
        rw [show (r : ℂ) - r + 2 = 2 by ring, ← hres2_two]
        exact hres2 2 (Or.inl (mem_singleton 2))
      have hψ : HasResidue negLogDerivZeta ((r : ℂ) - r + 1) 1 := by
        rw [show (r : ℂ) - r + 1 = 1 by ring]
        exact hasResidue_negLogDerivZeta_one
      have hT1 := fillB_hasResidue_T1 (by linarith) hP2
      have hT2 := fillB_hasResidue_phiRRest hRH hr hre (fillB_hasResidue_psi_shift hψ)
        (hasResidue_div_sub (r : ℂ) (cA r : ℂ))
      refine fillB_hasResidue_of_eq (hT1.add' hT2) (fun z => rfl) ?_
      have hF : ((r - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [fillB_resR, ite_eq_left rfl, phiRCoef, show (r : ℂ) - r + 2 = 2 by ring,
        show (r : ℂ) - r + 1 = 1 by ring, Gamma_one, fillB_Gamma_two,
        fillB_Gamma_natCast (by omega)]
      linear_combination (((r - 1).factorial : ℂ))⁻¹ * fillB_cC_add_cB_add_cA r
    · have hρ0 : ρ ≠ 0 := fun h => by
        have := hρ.2.1
        rw [h] at this
        simp at this
      have hre : (r : ℝ) - 1 < (((r : ℂ) - 1) + ρ).re := by simp; linarith [hρ.2.1]
      have hP2 : HasResidue Phi2c (((r : ℂ) - 1) + ρ - r + 2) (-(2 * (zetaMult ρ : ℂ)) / ρ) := by
        rw [show ((r : ℂ) - 1) + ρ - r + 2 = 1 + ρ by ring, ← hres2_rho ρ hρ]
        exact hres2 _ (Or.inr ⟨ρ, hρ, rfl⟩)
      have hψ : HasResidue negLogDerivZeta (((r : ℂ) - 1) + ρ - r + 1) (-(zetaMult ρ : ℂ)) := by
        rw [show ((r : ℂ) - 1) + ρ - r + 1 = ρ by ring]
        exact (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).1
      have hA : HasResidue (fun z => (cA r : ℂ) / (z - r)) (((r : ℂ) - 1) + ρ) 0 :=
        hasResidue_zero_of_analyticAt (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr (hne ρ hρ)))
      have hT1 := fillB_hasResidue_T1 (by linarith) hP2
      have hT2 := fillB_hasResidue_phiRRest hRH hr hre (fillB_hasResidue_psi_shift hψ) hA
      refine fillB_hasResidue_of_eq (hT1.add' hT2) (fun z => rfl) ?_
      have hinv : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ0
      rw [fillB_resR, ite_eq_right (hne ρ hρ), hsub, phiRCoef,
        show ((r : ℂ) - 1) + ρ - r + 2 = ρ + 1 by ring, show ((r : ℂ) - 1) + ρ - r + 1 = ρ by ring,
        Gamma_add_one ρ hρ0, show ρ + ((r : ℂ) - 1) = ((r : ℂ) - 1) + ρ by ring]
      linear_combination
        (-2 * (zetaMult ρ : ℂ) * (cC r : ℂ) * Gamma ρ * (Gamma (((r : ℂ) - 1) + ρ))⁻¹) * hinv +
        (-(zetaMult ρ : ℂ) * Gamma ρ * (Gamma (((r : ℂ) - 1) + ρ))⁻¹) * fillB_two_cC_add_cB r
  · rw [fillB_resR, ite_eq_left rfl]
  · intro ρ hρ
    rw [fillB_resR, ite_eq_right (hne ρ hρ), hsub]
  · rintro α (hα | ⟨ρ, hρ, rfl⟩)
    · rw [mem_singleton_iff] at hα
      subst hα
      rw [fillB_resR, ite_eq_left rfl]
      exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    · rw [fillB_resR, ite_eq_right (hne ρ hρ), hsub]
      have hm : (zetaMult ρ : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (by have := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).2; omega)
      have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hG : Gamma ρ ≠ 0 := Gamma_ne_zero_of_re_pos hρ.2.1
      have hG' : Gamma (ρ + ((r : ℂ) - 1)) ≠ 0 :=
        Gamma_ne_zero_of_re_pos (by simp; linarith [hρ.2.1])
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hr0 hm)) hG) hG'

end GoldbachBoundaries.PhiRProof.FillB
