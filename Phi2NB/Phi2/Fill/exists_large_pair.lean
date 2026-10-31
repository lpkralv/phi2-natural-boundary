import Phi2NB.Phi2.Proof.M3Radial
import Phi2NB.Phi2.Fill.norm_bKer
import Phi2NB.Phi2.Fill.norm_bKer_le
import Phi2NB.Phi2.Fill.bKer_cone
import Phi2NB.Phi2.Fill.sum_bKer_ne_zero
import Phi2NB.Phi2.Fill.pairAtom_eq_two_tsum
import Phi2NB.Phi2.Fill.Aidx_bin_le
import Phi2NB.Phi2.Fill.pairAtom_neg
import Phi2NB.Phi2.Fill.pairAtom_ne_zero_of_large
import Phi2NB.TBoundary

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Large pairs in every interval** (RH, Littlewood): for every `H` and `a < b` there is `τ ∈ (a, b)` with a
representation `ρ + ρ' = 1 + iτ` whose ordinates both have modulus `> H`. Take a zero `1/2 + iu` with `u` large
(`exists_nontrivialZero_im_gt`, `Density.lean`) and a zero `1/2 + iv` with `v - u ∈ (a, b)`
(`M5.exists_ordinate_in_interval`); the pair is `(1/2 + iv, 1/2 - iu)` (`conj_mem_nontrivialZeros`). -/
theorem exists_large_pair (hRH : RiemannHypothesis) (hL : LittlewoodGap) (H : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ τ ∈ Ioo a b, ∃ p : pairIdx τ, H < |(p.1.1 : ℂ).im| ∧ H < |(p.1.2 : ℂ).im| := by
  obtain ⟨Y₀, hY₀⟩ := M5.exists_ordinate_in_interval hL (sub_pos.mpr hab)
  obtain ⟨ρ, hρ, hu⟩ := exists_nontrivialZero_im_gt (max (Y₀ - a) (max H (H - a)))
  have huY : Y₀ ≤ ρ.im + a := by linarith [le_max_left (Y₀ - a) (max H (H - a))]
  have huH : H < ρ.im := lt_of_le_of_lt (le_trans (le_max_left H (H - a)) (le_max_right _ _)) hu
  have huHa : H - a < ρ.im := lt_of_le_of_lt (le_trans (le_max_right H (H - a)) (le_max_right _ _)) hu
  obtain ⟨ρ', hρ', hvlo, hvhi⟩ := hY₀ (ρ.im + a) huY
  refine ⟨ρ'.im - ρ.im, ⟨by linarith, by linarith⟩, ?_⟩
  have heq : ρ' + conj ρ = 1 + (ρ'.im - ρ.im : ℝ) * I := by
    apply Complex.ext
    · simp only [add_re, conj_re, one_re, mul_re, ofReal_re, I_re, ofReal_im,
        I_im, mul_zero, zero_mul, sub_self, add_zero]
      rw [sigmaFinite_re_eq_half hRH hρ', sigmaFinite_re_eq_half hRH hρ]
      norm_num
    · simp [sub_eq_add_neg]
  refine ⟨⟨(⟨ρ', hρ'⟩, ⟨conj ρ, conj_mem_nontrivialZeros hρ⟩), heq⟩, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith : H < ρ'.im) (le_abs_self _)
  · simpa only [conj_im, abs_neg] using lt_of_lt_of_le huH (le_abs_self ρ.im)

end GoldbachBoundaries.Phi2Proof
