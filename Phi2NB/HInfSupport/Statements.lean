import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.Statements`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

lemma ne_one_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 1 := by
  rintro rfl
  simp [NontrivialZeros] at hρ

theorem one_le_zetaMult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ zetaMult ρ := by
  have hne1 := ne_one_of_mem_nontrivialZeros hρ
  have han := analyticAt_riemannZeta hne1
  have hzero : riemannZeta ρ = 0 := hρ.1
  
  have hcd : riemannZeta ⁻¹' {0}ᶜ ∈ codiscreteWithin ({1} : Set ℂ)ᶜ := by
    refine AnalyticOnNhd.preimage_zero_mem_codiscreteWithin (x := 2)
      (fun z hz => analyticAt_riemannZeta hz) ?_ ?_ ?_
    · exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
    · norm_num
    · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hev : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    have hdisj := (mem_codiscreteWithin.mp hcd) ρ hne1
    have h1 : (({1} : Set ℂ)ᶜ \ riemannZeta ⁻¹' {0}ᶜ)ᶜ ∈ 𝓝[≠] ρ :=
      Filter.disjoint_principal_right.mp hdisj
    have h2 : ∀ᶠ z in 𝓝[≠] ρ, z ∈ ({1} : Set ℂ)ᶜ :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne1)
    filter_upwards [h1, h2] with z hz1 hz2 hz3
    exact hz1 ⟨hz2, by simpa using hz3⟩
  have hntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2 hev
  have hA0 : analyticOrderAt riemannZeta ρ ≠ 0 := fun h => (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold zetaMult
  rw [han.meromorphicOrderAt_eq] at hntop ⊢
  cases hO : analyticOrderAt riemannZeta ρ with
  | top => simp [hO] at hntop
  | coe n =>
    have hn : n ≠ 0 := fun h => hA0 (by simp [hO, h])
    rw [ENat.map_natCast, WithTop.untopD_coe]
    simp only [Int.toNat_natCast]
    omega

theorem re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 < ρ.re) : ρ.re = 1 / 2 := by
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hz

theorem re_eq_half_of_mem_nontrivialZeros (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) : ρ.re = 1 / 2 :=
  re_eq_half_of_RH hRH hρ.1 hρ.2.1

end GoldbachBoundaries
