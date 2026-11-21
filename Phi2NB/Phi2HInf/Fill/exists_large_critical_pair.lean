import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Fill.critical_basic
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.exists_large_critical_pair`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2

theorem exists_large_critical_pair (hZ1 : Z1) (hL : ZLittlewood) (hfin : offLineZeros.Finite)
    (H : ℝ) {a b : ℝ} (hab : a < b) :
    ∃ τ ∈ Ioo a b, ∃ p : criticalPairIdx τ,
      H < |(criticalVal p.1.1).im| ∧ H < |(criticalVal p.1.2).im| := by
  obtain ⟨T, hT⟩ := eventually_critical hfin
  let H' := max H T
  obtain ⟨Y₀, hY₀⟩ := M5.exists_ordinate_in_interval hL (sub_pos.mpr hab)
  obtain ⟨ρ, hρ, hu⟩ := exists_nontrivialZero_im_gt (max (Y₀ - a) (max H' (H' - a)))
  have huY : Y₀ ≤ ρ.im + a := by linarith [le_max_left (Y₀ - a) (max H' (H' - a))]
  have huH : H' < ρ.im := lt_of_le_of_lt (le_trans (le_max_left H' (H' - a)) (le_max_right _ _)) hu
  have huHa : H' - a < ρ.im := lt_of_le_of_lt (le_trans (le_max_right H' (H' - a)) (le_max_right _ _)) hu
  obtain ⟨ρ', hρ', hvlo, hvhi⟩ := hY₀ (ρ.im + a) huY
  have hρcrit : ρ.re = 1 / 2 := hT ⟨ρ, hρ⟩
    (by linarith [le_max_right H T, le_abs_self ρ.im])
  have hρ'crit : ρ'.re = 1 / 2 := hT ⟨ρ', hρ'⟩
    (by linarith [le_max_right H T, le_abs_self ρ'.im])
  refine ⟨ρ'.im - ρ.im, ⟨by linarith, by linarith⟩, ?_⟩
  have heq : ρ' + conj ρ = 1 + (ρ'.im - ρ.im : ℝ) * I := by
    apply Complex.ext
    · simp [hρcrit, hρ'crit]
      <;> norm_num
    · simp [sub_eq_add_neg]
  let r : CriticalZero := ⟨⟨ρ', hρ'⟩, hρ'crit⟩
  let q : CriticalZero := ⟨⟨conj ρ, (hZ1 ρ hρ).1.1⟩, by simpa using hρcrit⟩
  refine ⟨⟨(r, q), heq⟩, ?_, ?_⟩
  · change H < |ρ'.im|
    linarith [le_max_left H T, le_abs_self ρ'.im]
  · change H < |(conj ρ).im|
    simp only [conj_im, abs_neg]
    linarith [le_max_left H T, le_abs_self ρ.im]

end GoldbachBoundaries.Phi2HInf
