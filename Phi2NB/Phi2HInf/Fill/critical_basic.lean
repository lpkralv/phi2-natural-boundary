import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.summable_norm_zeroCoef_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.critical_basic`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem finite_offLineZeros (hZ1 : Z1) (hfin : rightZeros.Finite) : offLineZeros.Finite := by
  have hsub : offLineZeros ⊆ rightZeros ∪ (fun z : ℂ => 1 - conj z) '' rightZeros := by
    intro ρ hρ
    rcases lt_or_gt_of_ne hρ.2 with hlt | hgt
    · right
      refine ⟨1 - conj ρ, ⟨(hZ1 ρ hρ.1).2.1, ?_⟩, ?_⟩
      · simp only [sub_re, one_re, conj_re]
        linarith
      · simp
    · exact Or.inl ⟨hρ.1, hgt⟩
  exact (hfin.union (hfin.image _)).subset hsub

theorem eventually_critical (hfin : offLineZeros.Finite) :
    ∃ T : ℝ, ∀ ρ : NontrivialZeros, T < |(ρ : ℂ).im| → (ρ : ℂ).re = 1 / 2 := by
  obtain ⟨T, hT⟩ := (hfin.image (fun z : ℂ => |z.im|)).bddAbove
  refine ⟨T, ?_⟩
  intro ρ hρ
  by_contra hne
  have hh := hT (Set.mem_image_of_mem (fun z : ℂ => |z.im|)
    (show (ρ : ℂ) ∈ offLineZeros from ⟨ρ.2, hne⟩))
  exact (not_le_of_gt hρ) hh

theorem summable_norm_critical_pair (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    Summable (fun p : CriticalZero × CriticalZero =>
      ‖zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2)‖) := by
  have hs : Summable (fun ρ : CriticalZero => ‖zeroCoef (criticalVal ρ)‖) :=
    (summable_norm_zeroCoef_hinf hZ1 hZ2 hStir).subtype _
  exact Summable.mul_norm (f := fun ρ : CriticalZero => zeroCoef (criticalVal ρ))
    (g := fun ρ : CriticalZero => zeroCoef (criticalVal ρ)) hs hs

theorem finite_exceptional_critical (H Y : ℝ) :
    {τ : ℝ | |τ| ≤ Y ∧ ∃ p : criticalPairIdx τ,
      |(criticalVal p.1.1).im| ≤ H ∨ |(criticalVal p.1.2).im| ≤ H}.Finite := by
  let S : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ |H| + |Y|}
  have hS : S.Finite := M1.finite_zeros_abs_im_le (|H| + |Y|)
  refine ((hS.prod hS).image (fun p : ℂ × ℂ => p.1.im + p.2.im)).subset ?_
  rintro τ ⟨hτ, p, hp⟩
  have him : (criticalVal p.1.1).im + (criticalVal p.1.2).im = τ := by
    have := congrArg Complex.im p.2
    simpa using this
  have hbounds : |(criticalVal p.1.1).im| ≤ |H| + |Y| ∧ |(criticalVal p.1.2).im| ≤ |H| + |Y| := by
    rcases hp with h | h
    · constructor
      · linarith [le_abs_self H, abs_nonneg Y]
      · have he : (criticalVal p.1.2).im = τ - (criticalVal p.1.1).im := by linarith
        rw [he]
        have := abs_sub τ (criticalVal p.1.1).im
        linarith [le_abs_self H, le_abs_self Y]
    · constructor
      · have he : (criticalVal p.1.1).im = τ - (criticalVal p.1.2).im := by linarith
        rw [he]
        have := abs_sub τ (criticalVal p.1.2).im
        linarith [le_abs_self H, le_abs_self Y]
      · linarith [le_abs_self H, abs_nonneg Y]
  exact ⟨((criticalVal p.1.1), (criticalVal p.1.2)), ⟨⟨p.1.1.1.2, hbounds.1⟩, ⟨p.1.2.1.2, hbounds.2⟩⟩, him⟩

end GoldbachBoundaries.Phi2HInf
