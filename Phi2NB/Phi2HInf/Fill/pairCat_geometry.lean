import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.pairCat_geometry`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem locallyFinite_pairCat (hH : Hinf) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ HH) :
    {p : NontrivialZeros × NontrivialZeros | (p.1 : ℂ) + p.2 ∈ K}.Finite := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
  have hs₀H : 1 < s₀.re := hKH hs₀
  let δ := (s₀.re - 1) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let E := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 1 / 2 + δ < ρ.re}
  have hE : E.Finite := hH δ hδ
  obtain ⟨T, hT⟩ := (hE.image (fun ρ : ℂ => |ρ.im|)).bddAbove
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let Z : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ |T| + |R|}
  have hZ : Z.Finite := M1.finite_zeros_abs_im_le _
  have hZ' : {ρ : NontrivialZeros | (ρ : ℂ) ∈ Z}.Finite :=
    hZ.preimage Subtype.val_injective.injOn
  refine (hZ'.prod hZ').subset ?_
  intro p hp
  have hreal : s₀.re ≤ (p.1 : ℂ).re + (p.2 : ℂ).re := by simpa using hmin hp
  have him : |(p.1 : ℂ).im + (p.2 : ℂ).im| ≤ |R| := by
    have hh := (abs_im_le_norm ((p.1 : ℂ) + p.2)).trans (hR _ hp)
    simpa only [add_im] using hh.trans (le_abs_self R)
  have hhigh : (p.1 : ℂ) ∈ E ∨ (p.2 : ℂ) ∈ E := by
    by_cases h : 1 / 2 + δ < (p.1 : ℂ).re
    · exact Or.inl ⟨p.1.2, h⟩
    · right
      refine ⟨p.2.2, ?_⟩
      dsimp [δ] at *
      linarith
  have hlo : ∀ ρ ∈ E, |ρ.im| ≤ |T| := fun ρ hρ =>
    (hT (mem_image_of_mem _ hρ)).trans (le_abs_self T)
  have hbounds : |(p.1 : ℂ).im| ≤ |T| + |R| ∧ |(p.2 : ℂ).im| ≤ |T| + |R| := by
    rcases hhigh with h | h
    · have hh := hlo _ h
      have ht := abs_sub ((p.1 : ℂ).im + (p.2 : ℂ).im) (p.1 : ℂ).im
      simp only [add_sub_cancel_left] at ht
      constructor <;> linarith [abs_nonneg R]
    · have hh := hlo _ h
      have ht := abs_sub ((p.1 : ℂ).im + (p.2 : ℂ).im) (p.2 : ℂ).im
      simp only [add_sub_cancel_right] at ht
      constructor <;> linarith [abs_nonneg R]
  exact ⟨⟨p.1.2, hbounds.1⟩, ⟨p.2.2, hbounds.2⟩⟩

theorem pairCat_denominator_bound (hH : Hinf) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ HH) :
    ∃ E : Finset (NontrivialZeros × NontrivialZeros), ∃ d : ℝ, 0 < d ∧
      ∀ s ∈ K, ∀ p : NontrivialZeros × NontrivialZeros,
        p ∉ E → d ≤ ‖s - p.1 - p.2‖ := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, 1, one_pos, by simp⟩
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne continuous_re.continuousOn
  have hs₀H : 1 < s₀.re := hKH hs₀
  let d := min 1 ((s₀.re - 1) / 2)
  have hd : 0 < d := lt_min one_pos (by linarith)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdgap : d ≤ (s₀.re - 1) / 2 := min_le_right _ _
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let K' := closedBall (0 : ℂ) (R + 1) ∩ {z : ℂ | 1 + d ≤ z.re}
  have hK' : IsCompact K' := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const continuous_re)
  have hK'H : K' ⊆ HH := by
    intro z hz
    change 1 < z.re
    have := hz.2
    change 1 + d ≤ z.re at this
    linarith
  let hfin := locallyFinite_pairCat hH hK' hK'H
  refine ⟨hfin.toFinset, d, hd, ?_⟩
  intro s hs p hp
  by_contra hh
  have hclose : ‖s - ((p.1 : ℂ) + p.2)‖ < d := by simpa only [sub_add_eq_sub_sub] using lt_of_not_ge hh
  apply hp
  rw [hfin.mem_toFinset]
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    have ht := norm_le_norm_sub_add ((p.1 : ℂ) + p.2) s
    rw [norm_sub_rev] at ht
    linarith [hR s hs]
  · have hre := abs_re_le_norm (s - ((p.1 : ℂ) + p.2))
    rw [sub_re] at hre
    have := le_abs_self (s.re - ((p.1 : ℂ) + p.2).re)
    have hm : s₀.re ≤ s.re := hmin hs
    change 1 + d ≤ ((p.1 : ℂ) + p.2).re
    linarith

end GoldbachBoundaries.Phi2HInf
