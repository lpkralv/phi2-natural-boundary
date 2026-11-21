import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon
import Phi2NB.HInfSupport.Paper2.M1.Skeleton
import Phi2NB.HInfSupport.Paper2.M2.Fill.Binf_eq_half_of_Hinf
import Phi2NB.HInfSupport.Statements
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.analyticOn_M0_strip
import Phi2NB.Phi2HInf.Fill.hasResidue_C
import Phi2NB.Phi2HInf.Fill.phi2_hinf_continuation
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M1Regularization
import Phi2NB.Phi2HInf.ZetaNoZeroIoo

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.pole_twoBsup`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries Paper2 Phi2Proof

theorem analyticAt_M0_of_not_mem_phi2Poles (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {s : ℂ} (hs : 1 < s.re) (hP : s ∉ phi2Poles) : AnalyticAt ℂ M0 s := by
  have hs2 : s ≠ 2 := fun h => hP (Or.inl (mem_singleton_iff.mpr h))
  have hs10 : s - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re, one_re, zero_re] at hr
    linarith
  have hψ := analyticAt_negLogDerivZeta_sub_one hs hP
  have hΓ := differentiable_one_div_Gamma.analyticAt s
  have hm := (((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (2 : ℂ)) s).mul hψ).div
    (analyticAt_id.sub analyticAt_const) hs10).sub
    (hΓ.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs2)))
  have hL := analyticAt_L_hinf hZ1 hZ2 hStir hs
  convert hm.sub (((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => 2 * c0) s).mul hL).mul hΓ) using 1
  ext z
  simp only [M0, phi2Main, Pi.sub_apply, Pi.mul_apply, Pi.inv_apply,
    id_eq, div_eq_mul_inv, mul_inv, one_mul]

theorem ofReal_not_mem_phi2Poles (hζ : ZetaNoZeroIoo) {x : ℝ} (hx1 : 1 < x) (hx2 : x < 2) :
    (x : ℂ) ∉ phi2Poles := by
  rintro (h | ⟨ρ, hρ, hsum⟩)
  · have hr := congrArg Complex.re (mem_singleton_iff.mp h)
    simp only [ofReal_re, re_ofNat] at hr
    linarith
  · have hρx : ρ = ((x - 1 : ℝ) : ℂ) := by
      push_cast
      linear_combination -hsum
    refine hζ (x - 1) (by linarith) (by linarith) ?_
    rw [← hρx]
    exact hρ.1

theorem hasResidue_Phi2cHInf_of_not_mem_phi2Poles (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {s : ℂ} (hs : 1 < s.re) (hP : s ∉ phi2Poles) :
    HasResidue Phi2cHInf s (collisionAtom s / Gamma s) := by
  have hM := analyticAt_M0_of_not_mem_phi2Poles hZ1 hZ2 hStir hs hP
  have hA := (differentiableOn_A hZ1 hZ2 hZ3 hStir).analyticOnNhd
    (isOpen_halfPlane _) s (show s ∈ halfPlane (1 / 2) by change 1 / 2 < s.re; linarith)
  have hC := (hasResidue_C hH hZ1 hZ2 hStir hs).add_analyticAt hA
  have hΓ : ContinuousAt (fun z : ℂ => 1 / Gamma z) s := by
    simpa only [one_div] using differentiable_one_div_Gamma.continuous.continuousAt (x := s)
  have hres := (hasResidue_zero_of_analyticAt hM).add' (hC.mul_continuousAt' hΓ)
  change HasResidue (fun z => M0 z + (C z + A z) / Gamma z) s (collisionAtom s / Gamma s)
  simpa only [div_eq_mul_inv, one_mul, zero_add] using hres

theorem exists_rightZero_of_offLine (hZ1 : Z1) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ NontrivialZeros, 1 / 2 < ρ.re := by
  obtain ⟨ρ, hρ, hne⟩ := hoff
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨1 - conj ρ, (hZ1 ρ hρ).2.1, ?_⟩
    simp only [sub_re, one_re, conj_re]
    linarith
  · exact ⟨ρ, hρ, h⟩

theorem Bsup_attained_of_offLine (hH : Hinf) (hZ1 : Z1) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty := by
  obtain ⟨ρ, hρ, hre⟩ := exists_rightZero_of_offLine hZ1 hoff
  have hB : Binf < Bsup := by
    rw [M2.Binf_eq_half_of_Hinf hZ1 hH]
    exact hre.trans_le (M1.re_le_Bsup hρ)
  exact M1.lem_B_iv_proof hZ1 hB

theorem collision_twoBsup_iff (p : NontrivialZeros × NontrivialZeros) :
    (p.1 : ℂ) + p.2 = 2 * (Bsup : ℂ) ↔ (p.1 : ℂ).re = Bsup ∧ (p.2 : ℂ) = conj (p.1 : ℂ) := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [add_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero] at hre
    simp only [add_im, mul_im, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, zero_mul,
      add_zero] at him
    have h1 := M1.re_le_Bsup p.1.2
    have h2 := M1.re_le_Bsup p.2.2
    have hr1 : (p.1 : ℂ).re = Bsup := by linarith
    refine ⟨hr1, Complex.ext ?_ ?_⟩
    · rw [conj_re]; linarith
    · rw [conj_im]; linarith
  · rintro ⟨hr, hc⟩
    rw [hc, Complex.add_conj, hr]
    push_cast
    ring

def collisionTwoBsupEquiv :
    collisionIdx (2 * (Bsup : ℂ)) ≃ {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup} where
  toFun p := ⟨p.1.1, ((collision_twoBsup_iff p.1).1 p.2).1⟩
  invFun ρ := ⟨(ρ.1, ⟨conj (ρ.1 : ℂ), conj_mem_nontrivialZeros ρ.1.2⟩),
    (collision_twoBsup_iff _).2 ⟨ρ.2, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact ((collision_twoBsup_iff p.1).1 p.2).2.symm
  right_inv _ := rfl

theorem zeroCoef_mul_zeroCoef_conj {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    zeroCoef ρ * zeroCoef (conj ρ) = (((zetaMult ρ : ℝ) ^ 2 * ‖Gamma ρ‖ ^ 2 : ℝ) : ℂ) := by
  have hnorm : Gamma ρ * conj (Gamma ρ) = ((‖Gamma ρ‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]
  simp only [zeroCoef, zetaMult_conj hρ, Complex.Gamma_conj]
  push_cast
  linear_combination ((zetaMult ρ : ℂ)) ^ 2 * hnorm

theorem collisionAtom_twoBsup :
    collisionAtom (2 * (Bsup : ℂ)) =
      ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
        ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) := by
  unfold collisionAtom
  rw [← collisionTwoBsupEquiv.symm.tsum_eq, Complex.ofReal_tsum]
  refine tsum_congr fun ρ => ?_
  exact zeroCoef_mul_zeroCoef_conj ρ.1.2

theorem collisionAtom_twoBsup_pos
    (hfin : {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite)
    (hne : {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) :
    0 < ∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
      ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) := by
  have hfin' : Finite {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} := hfin.to_subtype
  have hfin'' : Finite {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup} :=
    Finite.of_injective
      (fun ρ => (⟨ρ.1.1, ρ.1.2, ρ.2⟩ : {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}))
      (fun a b h => by
        have h' : (a.1.1 : ℂ) = b.1.1 :=
          congrArg (fun x : {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} => (x : ℂ)) h
        exact Subtype.ext (Subtype.ext h'))
  obtain ⟨ρ₀, hρ₀, hre₀⟩ := hne
  have hterm : ∀ ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
      0 < (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 := by
    intro ρ
    have hm : (0 : ℝ) < zetaMult (ρ : ℂ) := by exact_mod_cast one_le_zetaMult ρ.1.2
    have hΓ : 0 < ‖Gamma (ρ : ℂ)‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos ρ.1.2.2.1)
    positivity
  exact Summable.tsum_pos Summable.of_finite (fun ρ => (hterm ρ).le) ⟨⟨ρ₀, hρ₀⟩, hre₀⟩ (hterm _)

theorem hasResidue_Phi2cHInf_twoBsup (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
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
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ)) := by
  obtain ⟨hB1, hB2, hfin, hne⟩ := Bsup_attained_of_offLine hH hZ1 hoff
  have hpos := collisionAtom_twoBsup_pos hfin hne
  have hatom := collisionAtom_twoBsup
  have hcast : (2 * (Bsup : ℂ)) = ((2 * Bsup : ℝ) : ℂ) := by push_cast; rfl
  have hs : 1 < (2 * (Bsup : ℂ)).re := by
    rw [hcast, ofReal_re]
    linarith
  have hP : (2 * (Bsup : ℂ)) ∉ phi2Poles := by
    rw [hcast]
    exact ofReal_not_mem_phi2Poles hζ (by linarith) (by linarith)
  have hres := hasResidue_Phi2cHInf_of_not_mem_phi2Poles hH hZ1 hZ2 hZ3 hStir hs hP
  have hΓpos : 0 < Real.Gamma (2 * Bsup) := Real.Gamma_pos_of_pos (by linarith)
  have hquot : collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ)) =
      (((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
        ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2)) / Real.Gamma (2 * Bsup) : ℝ) : ℂ) := by
    rw [hatom, hcast, Complex.Gamma_ofReal, ofReal_div]
  have hquotpos : 0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re := by
    rw [hquot, ofReal_re]
    exact div_pos hpos hΓpos
  have hquotne : collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ)) ≠ 0 := by
    intro h
    rw [h, zero_re] at hquotpos
    exact lt_irrefl 0 hquotpos
  have hmero : MeromorphicAt Phi2cHInf (2 * (Bsup : ℂ)) :=
    (phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir).1 _ hs
  refine ⟨⟨hB1, hB2⟩, ⟨hfin, hne⟩, ⟨hatom, ?_, ?_⟩, hres, ⟨hquotpos, ?_⟩,
    hres.meromorphicOrderAt_eq_neg_one hmero hquotne, ?_⟩
  · rw [hatom, ofReal_re]
    exact hpos
  · rw [hatom, ofReal_im]
  · rw [hquot, ofReal_im]
  · intro han
    exact hquotne (hres.unique (hasResidue_zero_of_analyticAt han))

theorem not_analyticAt_Phi2cHInf_twoBsup (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    ∃ x : ℝ, 1 < x ∧ x < 2 ∧ ¬ AnalyticAt ℂ Phi2cHInf x := by
  obtain ⟨⟨hB1, hB2⟩, -, -, -, -, -, hnot⟩ :=
    hasResidue_Phi2cHInf_twoBsup hH hZ1 hZ2 hZ3 hStir hζ hoff
  refine ⟨2 * Bsup, by linarith, by linarith, ?_⟩
  have hcast : ((2 * Bsup : ℝ) : ℂ) = 2 * (Bsup : ℂ) := by push_cast; rfl
  rw [hcast]
  exact hnot

end GoldbachBoundaries.Phi2HInf
