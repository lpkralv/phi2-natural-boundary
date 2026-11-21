import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.critical_basic
import Phi2NB.Phi2HInf.Fill.differentiableOn_criticalC
import Phi2NB.Phi2HInf.Fill.exists_large_critical_pair
import Phi2NB.Phi2HInf.Fill.tendsto_eta_criticalC
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M4Critical

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.critical_boundary`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem exists_tau_criticalAtom_ne_zero (hZ1 : Z1) (hZ2 : Z2) (hL : ZLittlewood)
    (hStir : StirlingStrip) (hfin : offLineZeros.Finite) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, τ ≠ y ∧ |τ - y| < ε ∧ criticalAtom τ ≠ 0 := by
  set Y : ℝ := |y| + ε with hYdef
  have hY : 0 < Y := by positivity
  obtain ⟨H, hYH, hH⟩ := criticalAtom_ne_zero_of_large hZ1 hZ2 hStir hY
  set E := {τ : ℝ | |τ| ≤ Y ∧ ∃ p : criticalPairIdx τ, |(criticalVal p.1.1).im| ≤ H ∨ |(criticalVal p.1.2).im| ≤ H}
  have hE : (E ∪ {0, y}).Finite := (finite_exceptional_critical H Y).union (by simp)
  obtain ⟨a', b', hab', hsub⟩ :=
    exists_Ioo_subset_diff_finite (a := y - ε) (b := y + ε) (by linarith) hE
  obtain ⟨τ, hτ, p, hp1, hp2⟩ := exists_large_critical_pair hZ1 hL hfin H hab'
  have hτ' := hsub hτ
  have hτI : τ ∈ Ioo (y - ε) (y + ε) := hτ'.1
  have hτE : τ ∉ E ∪ {0, y} := hτ'.2
  have hτy : τ ≠ y := fun h => hτE (Or.inr (by simp [h]))
  have hτ0 : τ ≠ 0 := fun h => hτE (Or.inr (by simp [h]))
  have habs : |τ - y| < ε := abs_sub_lt_iff.mpr ⟨by linarith [hτI.2], by linarith [hτI.1]⟩
  have hτY : |τ| ≤ Y := by
    rw [hYdef]
    have := abs_sub_abs_le_abs_sub τ y
    linarith
  refine ⟨τ, hτy, habs, hH τ hτY ⟨p⟩ fun q => ?_⟩
  by_contra hq
  apply hτE
  refine Or.inl ⟨hτY, q, ?_⟩
  rcases not_and_or.mp hq with h | h
  · exact Or.inl (not_lt.mp h)
  · exact Or.inr (not_lt.mp h)

theorem criticalC_natural_boundary (hZ1 : Z1) (hZ2 : Z2) (hL : ZLittlewood)
    (hStir : StirlingStrip) (hfin : offLineZeros.Finite) :
    IsNaturalBoundary criticalC HH lineOne := by
  intro s hs
  have hre : s.re = 1 := hs
  have heq : s = 1 + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [heq]
  apply M5.noMeromorphicExtensionAt_of_line_blowup
    (differentiableOn_criticalC hZ1 hZ2 hStir)
  intro ε hε
  obtain ⟨τ, hne, hlt, hAtom⟩ := exists_tau_criticalAtom_ne_zero hZ1 hZ2 hL hStir hfin s.im hε
  exact ⟨τ, hne, hlt, criticalAtom τ, hAtom, (tendsto_eta_criticalC hZ1 hZ2 hStir τ).2⟩

end GoldbachBoundaries.Phi2HInf
