import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.BoundaryLemma
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.critical_basic
import Phi2NB.Phi2HInf.Fill.critical_boundary
import Phi2NB.Phi2HInf.Fill.critical_decomposition
import Phi2NB.Phi2HInf.Fill.interior_poles
import Phi2NB.Phi2HInf.Fill.phi2_hinf_continuation
import Phi2NB.Phi2HInf.Proof.Defs
import Phi2NB.Phi2HInf.Proof.M4Critical

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Proof.M5Boundary`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem exists_interior_poles_accum (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (hinf : rightZeros.Infinite) (y : ℝ) :
    ∃ s : ℕ → ℂ, Function.Injective s ∧ Tendsto s atTop (𝓝 (1 + y * I)) ∧
      ∀ n, s n ∈ HH ∧ meromorphicOrderAt Phi2cHInf (s n) = -1 := by
  classical
  let z : ℂ := 1 + (y : ℂ) * I
  let P : Set ℂ := {s | s ∈ HH ∧ meromorphicOrderAt Phi2cHInf s = -1}
  let D : Set ℝ := (fun s => dist s z) '' P
  have hnear (ε : ℝ) (hε : 0 < ε) : ∃ s ∈ P, dist s z < ε := by
    obtain ⟨s, hs, hd, hp⟩ := exists_interior_pole_near hH hZ1 hZ2 hZ3 hL hStir hinf y hε
    exact ⟨s, ⟨hs, hp⟩, hd⟩
  have hglb : IsGLB D 0 := by
    constructor
    · rintro d ⟨s, hs, rfl⟩
      exact dist_nonneg
    · intro a ha
      by_contra hn
      obtain ⟨s, hs, hsd⟩ := hnear a (lt_of_not_ge hn)
      exact (not_le_of_gt hsd) (ha ⟨s, hs, rfl⟩)
  have hzero : 0 ∉ D := by
    rintro ⟨s, hs, he⟩
    have hsz : s = z := dist_eq_zero.mp he
    have hre : 1 < s.re := hs.1
    simp [hsz, z] at hre
  have hne : D.Nonempty := by
    obtain ⟨s, hs, -⟩ := hnear 1 one_pos
    exact ⟨dist s z, s, hs, rfl⟩
  obtain ⟨u, hu, -, hlim, hmem⟩ := hglb.exists_seq_strictAnti_tendsto_of_notMem hzero hne
  choose s hs he using hmem
  refine ⟨s, ?_, ?_, hs⟩
  · intro m n hmn
    apply hu.injective
    rw [← he m, ← he n, hmn]
  · apply tendsto_iff_dist_tendsto_zero.mpr
    change Tendsto (fun n => dist (s n) z) atTop (𝓝 0)
    simpa only [he] using hlim

theorem boundary_infinite_case (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (hinf : rightZeros.Infinite)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) : IsNaturalBoundary F HH lineOne := by
  obtain ⟨hmero, heq⟩ := phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir
  intro z hz
  have hzre : z.re = 1 := hz
  have hzeq : z = 1 + (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hzre]
  obtain ⟨s, -, hlim, hp⟩ := exists_interior_poles_accum hH hZ1 hZ2 hZ3 hL hStir hinf z.im
  rw [← hzeq] at hlim
  apply noMeromorphicExtensionAt_of_poles_in_every_ball (isOpen_halfPlane 1)
  intro ε hε
  obtain ⟨n, hn⟩ := (hlim.eventually (ball_mem_nhds z hε)).exists
  refine ⟨s n, (hp n).1, ?_, hn, ?_⟩
  · intro he
    have hre : 1 < (s n).re := (hp n).1
    rw [he, hzre] at hre
    exact lt_irrefl _ hre
  · rw [meromorphicOrderAt_congr
      (eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hmero heq hFΦ (hp n).1), (hp n).2]
    decide

theorem boundary_finite_case (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (hfin : rightZeros.Finite)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) : IsNaturalBoundary F HH lineOne := by
  obtain ⟨hmero, heq⟩ := phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir
  have hagree : F =ᶠ[codiscreteWithin HH] fun s => W s + (1 / Gamma s) * criticalC s := by
    have h := eventuallyEq_codiscreteWithin_of_nhdsNE fun a ha =>
      eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hmero heq hFΦ ha
    filter_upwards [h, Filter.self_mem_codiscreteWithin HH] with s hs hsH
    rw [hs, critical_decomposition hH hZ1 hZ2 hStir hsH]
    ring
  intro z hz
  apply (PhiRProof.FillC.noMeromorphicExtensionAt_iff_of_eq_add_mul'
    (isOpen_halfPlane (1 / 2)) (show z ∈ halfPlane (1 / 2) from by
      change 1 / 2 < z.re
      have : z.re = 1 := hz
      linarith)
    (meromorphicOn_W hZ1 hZ2 hZ3 hStir (finite_offLineZeros hZ1 hfin))
    (fun s _ => by simpa only [one_div] using differentiable_one_div_Gamma.analyticAt s)
    (fun s hs => one_div_ne_zero (Gamma_ne_zero_of_re_pos (by
      have : 1 / 2 < s.re := hs
      linarith))) hagree).mpr
  exact criticalC_natural_boundary hZ1 hZ2 hL hStir (finite_offLineZeros hZ1 hfin) z hz

theorem phi2_hinf_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) : IsNaturalBoundary F HH lineOne := by
  by_cases hfin : rightZeros.Finite
  · exact boundary_finite_case hH hZ1 hZ2 hZ3 hL hStir hfin F hF hFΦ
  · exact boundary_infinite_case hH hZ1 hZ2 hZ3 hL hStir hfin F hF hFΦ

end GoldbachBoundaries.Phi2HInf
