import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.norm_bKer_asymp
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.bKer_cone_hinf`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf

theorem coneMargin_pos {B : ℝ} (hB : 1 / 2 ≤ B) (hB1 : B < 1) : 0 < coneMargin B := by
  unfold coneMargin
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

theorem norm_coneRotation (τ u : ℝ) : ‖coneRotation τ u‖ = 1 := by
  simp [coneRotation, Complex.norm_exp]

theorem rotated_bMain_re (b c τ u₀ u : ℝ) :
    (coneRotation τ u₀ * bMain b c τ u).re = bAmp b c τ u *
      Real.cos (τ * (Real.log u - Real.log u₀) + Real.pi * (b - c) / 2) := by
  have he : -((τ * Real.log u₀ : ℝ) : ℂ) * I +
      ((τ * Real.log u + Real.pi * (b - c) / 2 : ℝ) : ℂ) * I =
      ((τ * (Real.log u - Real.log u₀) + Real.pi * (b - c) / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold coneRotation bMain
  rw [mul_left_comm, ← exp_add, he]
  simp [Complex.exp_re]

theorem phase_window_bound {Y d : ℝ} (hY : 0 < Y) (hd : 0 < d)
    {τ u₀ u : ℝ} (hτ : |τ| ≤ Y) (h1 : 1 ≤ u₀)
    (hU : (4 * Y / d) ^ 2 ≤ u₀) (hu : u₀ ≤ u) (hw : u ≤ u₀ + Real.sqrt u₀) :
    |τ * (Real.log u - Real.log u₀)| ≤ d / 4 := by
  have hu₀ : 0 < u₀ := by linarith
  have hu' : 0 < u := hu₀.trans_le hu
  have hs : 0 < Real.sqrt u₀ := Real.sqrt_pos.2 hu₀
  have hs2 := Real.sq_sqrt hu₀.le
  have ht : 4 * Y / d ≤ Real.sqrt u₀ := by nlinarith [sq_nonneg (4 * Y / d - Real.sqrt u₀)]
  have ht' : 4 * Y ≤ Real.sqrt u₀ * d := (div_le_iff₀ hd).1 ht
  have hl0 : 0 ≤ Real.log u - Real.log u₀ := sub_nonneg.2 (Real.log_le_log hu₀ hu)
  have hl : Real.log u - Real.log u₀ ≤ (u - u₀) / u₀ := by
    rw [← Real.log_div hu'.ne' hu₀.ne']
    have hh := Real.log_le_sub_one_of_pos (div_pos hu' hu₀)
    convert hh using 1 <;> field_simp <;> ring
  have hl' : Real.log u - Real.log u₀ ≤ Real.sqrt u₀ / u₀ :=
    hl.trans (div_le_div_of_nonneg_right (by linarith) hu₀.le)
  calc
    |τ * (Real.log u - Real.log u₀)| = |τ| * (Real.log u - Real.log u₀) := by
      rw [abs_mul, abs_of_nonneg hl0]
    _ ≤ Y * (Real.sqrt u₀ / u₀) := mul_le_mul hτ hl' hl0 hY.le
    _ ≤ d / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      rw [← mul_div_assoc, div_mul_eq_mul_div]
      apply (div_le_iff₀ hu₀).2
      nlinarith [mul_le_mul_of_nonneg_right ht' hs.le]

theorem bMain_cone {B Y : ℝ} (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u₀ u : ℝ, U ≤ u₀ → u₀ ≤ u → u ≤ u₀ + Real.sqrt u₀ →
          Real.sin (3 * (Real.pi * (1 - B)) / 4) * bAmp b c τ u ≤
            (coneRotation τ u₀ * bMain b c τ u).re := by
  let d := Real.pi * (1 - B)
  have hd : 0 < d := mul_pos Real.pi_pos (sub_pos.2 hB1)
  have hdle : d ≤ Real.pi / 2 := by dsimp [d]; nlinarith [Real.pi_pos]
  refine ⟨max (Y + 1) ((4 * Y / d) ^ 2), le_max_left _ _, ?_⟩
  intro b hb c hc τ hτ u₀ u hU hu hw
  have h1 : 1 ≤ u₀ := by linarith [(le_max_left _ _).trans hU]
  have hpow := (le_max_right _ _).trans hU
  have hphase := phase_window_bound hY hd hτ h1 hpow hu hw
  have hsplit : |Real.pi * (b - c) / 2| ≤ Real.pi / 2 - d := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    have hab : |b - c| ≤ 2 * B - 1 := abs_le.mpr ⟨by linarith [hb.1, hc.2],
      by linarith [hb.2, hc.1]⟩
    dsimp [d]
    nlinarith [mul_le_mul_of_nonneg_left hab Real.pi_pos.le]
  have hθ : |τ * (Real.log u - Real.log u₀) + Real.pi * (b - c) / 2| ≤
      Real.pi / 2 - 3 * d / 4 := by
    have := abs_add_le (τ * (Real.log u - Real.log u₀)) (Real.pi * (b - c) / 2)
    linarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (abs_nonneg (τ * (Real.log u - Real.log u₀) + Real.pi * (b - c) / 2))
    (by linarith [Real.pi_pos] : Real.pi / 2 - 3 * d / 4 ≤ Real.pi) hθ
  rw [Real.cos_abs, Real.cos_pi_div_two_sub] at hcos
  rw [rotated_bMain_re, mul_comm]
  exact mul_le_mul_of_nonneg_left hcos (bAmp_pos (by linarith : 0 < u)).le

theorem cone_of_relative_error {w m r : ℂ} {a k k' e : ℝ}
    (ha : 0 ≤ a) (hk : 0 ≤ k) (hr : ‖r‖ = 1) (hm : ‖m‖ = a)
    (hc : k' * a ≤ (r * m).re) (he : ‖w - m‖ ≤ e * a)
    (hreserve : (1 + k) * e ≤ k' - k) : k * ‖w‖ ≤ (r * w).re := by
  have hn : ‖w‖ ≤ (1 + e) * a := by
    calc ‖w‖ ≤ ‖w - m‖ + ‖m‖ := norm_le_norm_sub_add _ _
      _ ≤ e * a + a := by rw [hm]; gcongr
      _ = (1 + e) * a := by ring
  have hre : (r * m).re - (r * w).re ≤ e * a := by
    calc (r * m).re - (r * w).re = (r * (m - w)).re := by simp; ring
      _ ≤ ‖r * (m - w)‖ := Complex.re_le_norm _
      _ = ‖w - m‖ := by rw [norm_mul, hr, one_mul, norm_sub_rev]
      _ ≤ e * a := he
  have hres := mul_le_mul_of_nonneg_right hreserve ha
  have hkn := mul_le_mul_of_nonneg_left hn hk
  nlinarith

theorem bKer_cone_hinf (hStir : StirlingStrip) {B Y : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u₀ u : ℝ, U ≤ u₀ → u₀ ≤ u → u ≤ u₀ + Real.sqrt u₀ →
          coneMargin B * ‖bKerH b c τ u‖ ≤ (coneRotation τ u₀ * bKerH b c τ u).re := by
  let k := coneMargin B
  let k' := Real.sin (3 * (Real.pi * (1 - B)) / 4)
  have hk : 0 < k := coneMargin_pos hB hB1
  have hkk : k < k' := by
    dsimp [k, k', coneMargin]
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
    · nlinarith [mul_pos Real.pi_pos (sub_pos.2 hB1)]
  obtain ⟨K, U₁, hK, hU₁, happrox⟩ := norm_bKer_asymp hStir hB hB1 hY
  obtain ⟨U₂, hU₂, hcone⟩ := bMain_cone hB hB1 hY
  refine ⟨max U₁ (max U₂ ((1 + k) * K / (k' - k))), hU₁.trans (le_max_left _ _), ?_⟩
  intro b hb c hc τ hτ u₀ u hU hu hw
  have hu₁ : U₁ ≤ u₀ := (le_max_left _ _).trans hU
  have hu₂ : U₂ ≤ u₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hU
  have hquot : (1 + k) * K / (k' - k) ≤ u :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans hU).trans hu
  have hu0 : 0 < u := by linarith [hU₁.trans hu₁]
  apply cone_of_relative_error (bAmp_pos hu0).le hk.le (norm_coneRotation τ u₀)
    (norm_bMain b c τ u hu0) (hcone b hb c hc τ hτ u₀ u hu₂ hu hw)
    (happrox b hb c hc τ hτ u (hu₁.trans hu))
  have hh := (div_le_iff₀ (sub_pos.2 hkk)).1 hquot
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hu0).2 (by nlinarith)

end GoldbachBoundaries.Phi2HInf
