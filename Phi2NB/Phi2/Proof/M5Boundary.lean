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
import Phi2NB.Phi2.Fill.finite_exceptional
import Phi2NB.Phi2.Fill.exists_large_pair

/-!
# Density, finite exceptions and the natural boundary

In every interval, the sums `γ + γ'` with both ordinates large are dense (Littlewood's gap theorem, `LittlewoodGap`,
through `exists_ordinate_in_interval`), and the sums with a small ordinate are finitely many (`finite_exceptional`).
So, by the non-cancellation lemma `pairAtom_ne_zero_of_large`, `μ{τ} ≠ 0` on a set of `τ` accumulating at every real
point (`exists_tau_pairAtom_ne_zero`). With the radial limit `tendsto_eta_Hphi2`, every meromorphic extension of `H`
across the line has poles accumulating there (`M5.noMeromorphicExtensionAt_of_line_blowup`), and the meromorphic
`phi2Main` does not change that (`isNaturalBoundary_of_eventuallyEq_add`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas proved in `Fill/`

One file per lemma, imported above: `finite_exceptional`, `exists_large_pair`. -/

/-! ## Density -/

/-- An open interval minus a finite set contains an open interval. -/
theorem exists_Ioo_subset_diff_finite {a b : ℝ} (hab : a < b) {S : Set ℝ} (hS : S.Finite) :
    ∃ a' b', a' < b' ∧ Ioo a' b' ⊆ Ioo a b \ S := by
  have hopen : IsOpen (Ioo a b \ S) := isOpen_Ioo.sdiff hS.isClosed
  have hne : (Ioo a b \ S).Nonempty := ((Set.Ioo_infinite hab).sdiff hS).nonempty
  obtain ⟨a', b', h, hsub⟩ := hopen.exists_Ioo_subset hne
  exact ⟨a', b', h, hsub⟩

/-- **Density of the non-zero atoms** (RH, (RiemannVonMangoldt), Littlewood): near every real `y` there are `τ₀ ≠ y` with
`μ{τ₀} ≠ 0`. -/
theorem exists_tau_pairAtom_ne_zero (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hL : LittlewoodGap) (y : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ τ₀ : ℝ, τ₀ ≠ y ∧ |τ₀ - y| < ε ∧ pairAtom τ₀ ≠ 0 := by
  set Y : ℝ := |y| + ε with hYdef
  have hY : 0 < Y := by positivity
  obtain ⟨H, hYH, hH⟩ := pairAtom_ne_zero_of_large hRH hRvM hY
  set E := {τ : ℝ | |τ| ≤ Y ∧ ∃ p : pairIdx τ, |(p.1.1 : ℂ).im| ≤ H ∨ |(p.1.2 : ℂ).im| ≤ H}
  have hE : (E ∪ {0, y}).Finite := (finite_exceptional H Y).union (by simp)
  obtain ⟨a', b', hab', hsub⟩ :=
    exists_Ioo_subset_diff_finite (a := y - ε) (b := y + ε) (by linarith) hE
  obtain ⟨τ, hτ, p, hp1, hp2⟩ := exists_large_pair hRH hL H hab'
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
  refine ⟨τ, hτy, habs, hH τ hτ0 hτY ⟨p⟩ fun q => ?_⟩
  by_contra hq
  apply hτE
  refine Or.inl ⟨hτY, q, ?_⟩
  rcases not_and_or.mp hq with h | h
  · exact Or.inl (not_lt.mp h)
  · exact Or.inr (not_lt.mp h)

/-! ## The natural boundary -/

/-- Agreement on a punctured neighbourhood of every point of `S` is agreement off a discrete subset of `S`. -/
theorem eventuallyEq_codiscreteWithin_of_nhdsNE {f g : ℂ → ℂ} {S : Set ℂ}
    (h : ∀ a ∈ S, f =ᶠ[𝓝[≠] a] g) : f =ᶠ[codiscreteWithin S] g := by
  show {x | f x = g x} ∈ codiscreteWithin S
  rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  filter_upwards [h x hx] with y hy hy'
  exact hy'.2 hy

/-- Identity theorem on `ℍ`: if `F` and `F₀` are meromorphic on `ℍ`, `F₀ = G` on `σ > 2`, and `F = G` off a discrete
subset of `σ > 2`, then `F = F₀` on a punctured neighbourhood of every point of `ℍ`. -/
theorem eventuallyEq_nhdsNE_of_agree_halfPlane_two' {F F₀ G : ℂ → ℂ} (hF : MeromorphicOn F HH)
    (hF₀ : MeromorphicOn F₀ HH) (hF₀G : EqOn F₀ G (halfPlane 2))
    (hFG : F =ᶠ[codiscreteWithin (halfPlane 2)] G) {a : ℂ} (ha : a ∈ HH) :
    F =ᶠ[𝓝[≠] a] F₀ := by
  have h3 : (3 : ℂ) ∈ halfPlane 2 := by norm_num [halfPlane]
  have h3H : (3 : ℂ) ∈ HH := by norm_num [halfPlane]
  have hn3 : halfPlane 2 ∈ 𝓝 (3 : ℂ) := (isOpen_halfPlane 2).mem_nhds h3
  have hFG3 : F =ᶠ[𝓝[≠] (3 : ℂ)] G :=
    eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hFG hn3
  have hF₀G3 : F₀ =ᶠ[𝓝[≠] (3 : ℂ)] G :=
    Filter.mem_of_superset (nhdsWithin_le_nhds hn3) fun s hs => hF₀G hs
  have htop3 : meromorphicOrderAt (F - F₀) 3 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hFG3, hF₀G3] with s h1 h2
    simp [h1, h2]
  have htop : meromorphicOrderAt (F - F₀) a = ⊤ :=
    (hF.sub hF₀).meromorphicOrderAt_eq_top_of_isPreconnected (isPreconnected_halfPlane 1) h3H ha
      htop3
  rw [meromorphicOrderAt_eq_top_iff] at htop
  filter_upwards [htop] with s hs
  exact sub_eq_zero.mp hs

/-- **Adding a function meromorphic on `ℂ` keeps a natural boundary**: if `L` is a natural boundary of `H` (given
on `ℍ`), `D` is meromorphic on `ℂ`, and `F = D + H` off a discrete subset of `ℍ`, then `L` is a natural boundary of
`F`. (A meromorphic extension `f` of `F` gives the extension `f - D` of `H`.) -/
theorem isNaturalBoundary_of_eventuallyEq_add {F D H : ℂ → ℂ} {L : Set ℂ} (hH : IsNaturalBoundary H HH L)
    (hD : MeromorphicOn D univ) (hF : F =ᶠ[codiscreteWithin HH] fun s => D s + H s) :
    IsNaturalBoundary F HH L := by
  rintro z₀ hz₀ r hr ⟨f, hf, hfF⟩
  refine hH z₀ hz₀ r hr ⟨fun s => f s - D s, hf.sub (hD.mono_set (subset_univ _)), ?_⟩
  have h1 : F =ᶠ[codiscreteWithin (ball z₀ r ∩ HH)] fun s => D s + H s :=
    hF.filter_mono (Filter.codiscreteWithin_mono inter_subset_right)
  filter_upwards [hfF, h1] with s hs1 hs2
  rw [hs1, hs2]
  ring

/-- **`σ = 1` is a natural boundary of `H`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal), Littlewood): near every point `1 + iy` there
are `1 + iτ₀` with `η H(1 + iτ₀ + η) → μ{τ₀}/Γ(1 + iτ₀) ≠ 0`. -/
theorem Hphi2_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    IsNaturalBoundary Hphi2 HH lineOne := by
  intro s₁ hs₁
  have hs₁' : s₁.re = 1 := hs₁
  have hs₁eq : s₁ = 1 + (s₁.im : ℂ) * I := by
    apply Complex.ext <;> simp [hs₁']
  rw [hs₁eq]
  refine M5.noMeromorphicExtensionAt_of_line_blowup (differentiableOn_Hphi2 hRH) fun ε hε => ?_
  obtain ⟨τ₀, hne, hlt, hP⟩ := exists_tau_pairAtom_ne_zero hRH hRvM hL s₁.im hε
  have hΓ : Gamma (1 + τ₀ * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  exact ⟨τ₀, hne, hlt, pairAtom τ₀ / Gamma (1 + τ₀ * I), div_ne_zero hP hΓ,
    tendsto_eta_Hphi2 hRH hRvM hLD τ₀⟩

/-- **The natural boundary of `Φ₂`** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal), Littlewood): every meromorphic continuation of `Φ₂`
to `ℍ` has `σ = 1` as a natural boundary. -/
theorem phi2_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) (F : ℂ → ℂ)
    (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    IsNaturalBoundary F HH lineOne := by
  obtain ⟨hmero, heq, -⟩ := phi2_continuation hRH
  have hagree : F =ᶠ[codiscreteWithin HH] fun s => phi2Main s + Hphi2 s :=
    eventuallyEq_codiscreteWithin_of_nhdsNE fun a ha =>
      eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hmero heq hFΦ ha
  exact isNaturalBoundary_of_eventuallyEq_add (Hphi2_natural_boundary hRH hRvM hLD hL)
    meromorphicOn_phi2Main hagree

end GoldbachBoundaries.Phi2Proof
