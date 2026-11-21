import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.Statements
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.phi2_hinf_continuation
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M2Catalogue
import Phi2NB.Phi2HInf.Proof.M3Cone

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.interior_poles`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

lemma exists_right_zero_high (hZ1 : Z1) (hinf : rightZeros.Infinite) (T : ℝ) :
    ∃ ρ ∈ rightZeros, T < ρ.im := by
  obtain ⟨ρ, hρ, hsmall⟩ := (hinf.sdiff (M1.finite_zeros_abs_im_le T)).nonempty
  have hlarge : T < |ρ.im| := by
    by_contra h
    exact hsmall ⟨hρ.1, not_lt.mp h⟩
  rcases le_or_gt 0 ρ.im with hpos | hneg
  · exact ⟨ρ, hρ, by rwa [abs_of_nonneg hpos] at hlarge⟩
  · refine ⟨conj ρ, ⟨(hZ1 ρ hρ.1).1.1, by simpa using hρ.2⟩, ?_⟩
    simpa only [conj_im, abs_of_neg hneg] using hlarge

lemma exists_right_pair_near (hH : Hinf) (hZ1 : Z1) (hL : ZLittlewood)
    (hinf : rightZeros.Infinite) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ HH, dist s (1 + (y : ℂ) * I) < ε ∧ Nonempty (collisionIdx s) := by
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨T, hT⟩ := ((hH δ hδ).image (fun z : ℂ => z.im)).bddAbove
  have hupper (ρ : ℂ) (hρ : ρ ∈ NontrivialZeros) (ht : T < ρ.im) :
      ρ.re ≤ 1 / 2 + δ := by
    by_contra h
    exact (not_le_of_gt ht) (hT (mem_image_of_mem _ ⟨hρ, lt_of_not_ge h⟩))
  obtain ⟨Y, hY⟩ := M5.exists_ordinate_in_interval hL (show 0 < ε / 2 by positivity)
  obtain ⟨ρ, hρ, hρT⟩ := exists_right_zero_high hZ1 hinf
    (max T (max (T - y + ε / 4) (Y - y + ε / 4)))
  have hρT' : T < ρ.im := (le_max_left _ _).trans_lt hρT
  have hρT'' : T < ρ.im + y - ε / 4 := by
    have := (le_max_left (T - y + ε / 4) (Y - y + ε / 4)).trans (le_max_right T _)
    linarith
  have hρY : Y ≤ ρ.im + y - ε / 4 := by
    have := (le_max_right (T - y + ε / 4) (Y - y + ε / 4)).trans (le_max_right T _)
    linarith
  obtain ⟨q, hq, hqlo, hqhi⟩ := hY (ρ.im + y - ε / 4) hρY
  have hqT : T < q.im := hρT''.trans hqlo
  have hqright : ∃ q' ∈ NontrivialZeros, q'.im = q.im ∧ 1 / 2 ≤ q'.re := by
    by_cases h : 1 / 2 ≤ q.re
    · exact ⟨q, hq, rfl, h⟩
    · exact ⟨1 - conj q, (hZ1 q hq).2.1, by simp, by
        simp only [sub_re, one_re, conj_re]
        linarith⟩
  obtain ⟨q', hq', hqi, hqr⟩ := hqright
  have hρup := hupper ρ hρ.1 hρT'
  have hqup := hupper q' hq' (by rwa [hqi])
  let s := conj ρ + q'
  have hsre : 1 < s.re := by simp only [s, add_re, conj_re]; linarith [hρ.2]
  refine ⟨s, hsre, ?_, ⟨⟨(⟨conj ρ, (hZ1 ρ hρ.1).1.1⟩, ⟨q', hq'⟩), rfl⟩⟩⟩
  rw [dist_eq_norm]
  have hre : |(s - (1 + (y : ℂ) * I)).re| ≤ 2 * δ := by
    simp only [sub_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
      ofReal_im, I_im, zero_mul, sub_self, add_zero, s, conj_re]
    rw [abs_of_nonneg (by linarith [hρ.2])]
    linarith
  have him : |(s - (1 + (y : ℂ) * I)).im| < ε / 4 := by
    simp only [sub_im, add_im, one_im, mul_im, ofReal_re, I_im, mul_one,
      ofReal_im, I_re, mul_zero, add_zero, zero_add, s, conj_im, hqi]
    rw [abs_lt]
    constructor <;> linarith
  calc ‖s - (1 + (y : ℂ) * I)‖ ≤
      |(s - (1 + (y : ℂ) * I)).re| + |(s - (1 + (y : ℂ) * I)).im| :=
        norm_le_abs_re_add_abs_im _
    _ < 2 * δ + ε / 4 := add_lt_add_of_le_of_lt hre him
    _ < ε := by dsimp [δ]; linarith

lemma finite_low_collision (X Y : ℝ) :
    {s : ℂ | |s.im| ≤ Y ∧ ∃ p : collisionIdx s,
      |(p.1.1 : ℂ).im| ≤ X ∨ |(p.1.2 : ℂ).im| ≤ X}.Finite := by
  let Z : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ |X| + |Y|}
  have hZ : Z.Finite := M1.finite_zeros_abs_im_le _
  refine ((hZ.prod hZ).image (fun p : ℂ × ℂ => p.1 + p.2)).subset ?_
  rintro s ⟨hs, p, hp⟩
  have him : (p.1.1 : ℂ).im + (p.1.2 : ℂ).im = s.im := by
    simpa using congrArg Complex.im p.2
  have hb : |(p.1.1 : ℂ).im| ≤ |X| + |Y| ∧ |(p.1.2 : ℂ).im| ≤ |X| + |Y| := by
    rcases hp with h | h
    · have he : (p.1.2 : ℂ).im = s.im - (p.1.1 : ℂ).im := by linarith
      have := abs_sub s.im (p.1.1 : ℂ).im
      rw [← he] at this
      constructor <;> linarith [le_abs_self X, le_abs_self Y, abs_nonneg Y]
    · have he : (p.1.1 : ℂ).im = s.im - (p.1.2 : ℂ).im := by linarith
      have := abs_sub s.im (p.1.2 : ℂ).im
      rw [← he] at this
      constructor <;> linarith [le_abs_self X, le_abs_self Y, abs_nonneg Y]
  exact ⟨((p.1.1 : ℂ), (p.1.2 : ℂ)), ⟨⟨p.1.1.2, hb.1⟩, ⟨p.1.2.2, hb.2⟩⟩, p.2⟩

lemma exists_interior_pole_near (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (hinf : rightZeros.Infinite)
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ HH, dist s (1 + (y : ℂ) * I) < ε ∧ meromorphicOrderAt Phi2cHInf s = -1 := by
  let z : ℂ := 1 + (y : ℂ) * I
  let Y := |y| + 1
  have hY : 0 < Y := by dsimp [Y]; positivity
  obtain ⟨X, hXY, hX⟩ := collisionAtom_ne_zero_of_large hH hZ1 hZ2 hStir hY
  let E : Set ℂ := {s | |s.im| ≤ Y ∧ ∃ p : collisionIdx s,
    |(p.1.1 : ℂ).im| ≤ X ∨ |(p.1.2 : ℂ).im| ≤ X}
  have hE : E.Finite := finite_low_collision X Y
  let U := (E \ {z})ᶜ ∩ {s : ℂ | s.re < 1 + (1 - Bsup)} ∩ {s : ℂ | |s.im| < Y}
  have hU : IsOpen U := (((hE.sdiff (t := {z})).isClosed.isOpen_compl).inter
    (isOpen_lt continuous_re continuous_const)).inter
      (isOpen_lt (continuous_im.abs) continuous_const)
  have hzU : z ∈ U := by
    refine ⟨⟨by simp, ?_⟩, ?_⟩
    · change z.re < 1 + (1 - Bsup)
      simp only [z, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
        ofReal_im, I_im, zero_mul, sub_self, add_zero]
      linarith [lem_B_iii hH]
    · change |z.im| < Y
      simp [z, Y]
  obtain ⟨d, hd, hdu⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨s, hs, hsd, hrep⟩ := exists_right_pair_near hH hZ1 hL hinf y (lt_min hε hd)
  have hsU := hdu (show s ∈ ball z d from lt_of_lt_of_le hsd (min_le_right _ _))
  have hsne : s ≠ z := by
    intro he
    have : 1 < s.re := hs
    simp [he, z] at this
  have hsE : s ∉ E := fun he => hsU.1.1 ⟨he, hsne⟩
  have hatom : collisionAtom s ≠ 0 := hX s hsU.2.le hrep (by
    intro p
    constructor <;> by_contra h
    · exact hsE ⟨hsU.2.le, p, Or.inl (not_lt.mp h)⟩
    · exact hsE ⟨hsU.2.le, p, Or.inr (not_lt.mp h)⟩)
  have hres := hasResidue_Phi2cHInf hH hZ1 hZ2 hZ3 hStir hs hsU.1.2
  have hmer := (phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir).1 s hs
  exact ⟨s, hs, hsd.trans_le (min_le_left _ _), hres.meromorphicOrderAt_eq_neg_one hmer
    (div_ne_zero hatom (Gamma_ne_zero_of_re_pos (by have : 1 < s.re := hs; linarith)))⟩

end GoldbachBoundaries.Phi2HInf
