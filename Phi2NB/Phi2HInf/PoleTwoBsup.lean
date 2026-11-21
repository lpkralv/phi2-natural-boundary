import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.ResidueAPI
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.phi2_hinf_continuation
import Phi2NB.Phi2HInf.Fill.pole_twoBsup
import Phi2NB.Phi2HInf.Fill.pole_twoBsup_rh
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.ZetaNoZeroIoo

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.PoleTwoBsup`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Phi2Proof

theorem phi2_hinf_pole_twoBsup (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    (1 / 2 < Bsup ∧ Bsup < 1) ∧
    ({ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) ∧
    (collisionAtom (2 * (Bsup : ℂ)) =
        ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
          ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) ∧
      0 < (collisionAtom (2 * (Bsup : ℂ))).re ∧ (collisionAtom (2 * (Bsup : ℂ))).im = 0) ∧
    HasResidue Phi2cHInf (2 * (Bsup : ℂ))
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    (0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re ∧
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).im = 0) ∧
    meromorphicOrderAt Phi2cHInf (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) ∧
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ)) :=
  hasResidue_Phi2cHInf_twoBsup hH hZ1 hZ2 hZ3 hStir hζ hoff

theorem phi2_hinf_pole_twoBsup' (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    (1 / 2 < Bsup ∧ Bsup < 1) ∧
    ({ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) ∧
    (collisionAtom (2 * (Bsup : ℂ)) =
        ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
          ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) ∧
      0 < (collisionAtom (2 * (Bsup : ℂ))).re ∧ (collisionAtom (2 * (Bsup : ℂ))).im = 0) ∧
    HasResidue Phi2cHInf (2 * (Bsup : ℂ))
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    (0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re ∧
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).im = 0) ∧
    meromorphicOrderAt Phi2cHInf (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) ∧
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ)) :=
  phi2_hinf_pole_twoBsup hH hZ1 hZ2 hZ3 hStir zetaNoZeroIoo hoff

theorem phi2_hinf_pole_twoBsup_of_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    HasResidue F (2 * (Bsup : ℂ)) (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    meromorphicOrderAt F (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨⟨hB1, -⟩, -, -, hres, -, hord, -⟩ :=
    phi2_hinf_pole_twoBsup hH hZ1 hZ2 hZ3 hStir hζ hoff
  obtain ⟨hmero, heq⟩ := phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir
  have hs : (2 * (Bsup : ℂ)) ∈ HH := by
    change 1 < (2 * (Bsup : ℂ)).re
    simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero]
    linarith
  have hev := eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hmero heq hFΦ hs
  exact ⟨hres.congr hev.symm, by rw [meromorphicOrderAt_congr hev, hord]⟩

theorem phi2_hinf_rh_iff_no_real_pole (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x :=
  riemannHypothesis_iff_analyticAt_Phi2cHInf_real hH hZ1 hZ2 hZ3 hStir hζ

theorem phi2_hinf_rh_iff_no_real_pole' (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x :=
  phi2_hinf_rh_iff_no_real_pole hH hZ1 hZ2 hZ3 hStir zetaNoZeroIoo

theorem phi2_hinf_rh_iff_no_real_pole_of_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → 0 ≤ meromorphicOrderAt F x := by
  obtain ⟨hmero, heq⟩ := phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir
  constructor
  · intro hRH x hx1 hx2
    have hs : (x : ℂ) ∈ HH := by
      change 1 < (x : ℂ).re
      rw [ofReal_re]
      exact hx1
    rw [meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hmero heq hFΦ hs)]
    exact (analyticAt_Phi2cHInf_real_of_RH hRH hZ2 hZ3 hStir hζ hx1 hx2).meromorphicOrderAt_nonneg
  · intro h
    rw [riemannHypothesis_iff_nontrivialZeros]
    by_contra hnot
    push Not at hnot
    obtain ⟨⟨hB1, hB2⟩, -⟩ := phi2_hinf_pole_twoBsup hH hZ1 hZ2 hZ3 hStir hζ hnot
    have hord := (phi2_hinf_pole_twoBsup_of_continuation hH hZ1 hZ2 hZ3 hStir hζ hnot F hF hFΦ).2
    have hx := h (2 * Bsup) (by linarith) (by linarith)
    have hcast : ((2 * Bsup : ℝ) : ℂ) = 2 * (Bsup : ℂ) := by push_cast; rfl
    rw [hcast, hord] at hx
    exact absurd hx (by decide)

end GoldbachBoundaries.Phi2HInf
