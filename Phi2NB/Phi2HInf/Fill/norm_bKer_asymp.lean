import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.stirling_log
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.norm_bKer_asymp`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf

def stirlingMain (z : ℂ) : ℂ :=
  exp ((z - 1 / 2) * log z - z + (1 / 2) * log (2 * (Real.pi : ℂ)))

def stirlingPair (b c τ u : ℝ) : ℂ :=
  stirlingMain ((b : ℂ) + (u + τ : ℝ) * I) * stirlingMain ((c : ℂ) - (u : ℂ) * I)

theorem bAmp_pos {b c τ u : ℝ} (hu : 0 < u) : 0 < bAmp b c τ u := by
  unfold bAmp
  positivity

theorem norm_bMain (b c τ u : ℝ) (hu : 0 < u) : ‖bMain b c τ u‖ = bAmp b c τ u := by
  simp [bMain, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg (bAmp_pos (b := b) (c := c) (τ := τ) hu).le]

theorem stirling_exponent_error {z d w : ℂ} {M u : ℝ}
    (hM : 0 ≤ M) (hu : 1 ≤ u) (hMu : 2 * M ≤ u)
    (hz : ‖z‖ ≤ u + M) (hd : ‖d‖ ≤ M) (hw : ‖w‖ ≤ M / u) :
    ‖(z - 1 / 2) * (log (1 + w) - w) + (d - 1 / 2) * w‖ ≤
      ((M + 2) * M ^ 2 + (M + 1) * M) / u := by
  have hu0 : 0 < u := by linarith
  have hw2 : ‖w‖ ≤ 1 / 2 := hw.trans ((div_le_iff₀ hu0).2 (by linarith))
  have hz' : ‖z - 1 / 2‖ ≤ u + M + 1 := by
    calc ‖z - 1 / 2‖ ≤ ‖z‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ u + M + 1 := by norm_num; linarith
  have hd' : ‖d - 1 / 2‖ ≤ M + 1 := by
    calc ‖d - 1 / 2‖ ≤ ‖d‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ M + 1 := by norm_num; linarith
  have hz'' : u + M + 1 ≤ (M + 2) * u := by nlinarith
  calc
    ‖(z - 1 / 2) * (log (1 + w) - w) + (d - 1 / 2) * w‖ ≤
      ‖z - 1 / 2‖ * ‖log (1 + w) - w‖ + ‖d - 1 / 2‖ * ‖w‖ := by
        simpa only [norm_mul] using norm_add_le
          ((z - 1 / 2) * (log (1 + w) - w)) ((d - 1 / 2) * w)
    _ ≤ ((M + 2) * u) * (M / u) ^ 2 + (M + 1) * (M / u) := by
      gcongr
      · exact hz'.trans hz''
      · exact (log_ray_remainder hw2).trans (by gcongr)
    _ = ((M + 2) * M ^ 2 + (M + 1) * M) / u := by field_simp

theorem bMain_eq_exp (b c τ u : ℝ) (hu : 0 < u) :
    bMain b c τ u = exp (log (2 * (Real.pi : ℂ)) +
      ((b + c - 1) * Real.log u - Real.pi * u - Real.pi * τ / 2 : ℝ) +
      ((τ * Real.log u + Real.pi * (b - c) / 2 : ℝ) : ℂ) * I) := by
  unfold bMain bAmp
  rw [exp_add, exp_add, exp_log (by exact_mod_cast (mul_pos (by norm_num) Real.pi_pos).ne')]
  rw [Real.rpow_def_of_pos hu]
  push_cast
  rw [mul_assoc (2 * (Real.pi : ℂ)), ← exp_add]
  congr 2
  ring

theorem stirlingPair_asymp {B Y : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ K U : ℝ, 0 ≤ K ∧ Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u : ℝ, U ≤ u → ‖stirlingPair b c τ u - bMain b c τ u‖ ≤ K / u * bAmp b c τ u := by
  let M := Y + 2
  let D := (M + 2) * M ^ 2 + (M + 1) * M
  have hM : 0 ≤ M := by dsimp [M]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨4 * D, max (Y + 1) (max 1 (max (2 * M) (2 * D))), by positivity,
    le_max_left _ _, ?_⟩
  intro b hb c hc τ hτ u hu
  have hu1 : 1 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have huM : 2 * M ≤ u :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hu
  have huD : 2 * D ≤ u :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hu
  have hu0 : 0 < u := by linarith
  have huC : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu0.ne'
  have hbabs : |b| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hcabs : |c| ≤ 1 := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
  let d₁ : ℂ := b + (τ : ℂ) * I
  let d₂ : ℂ := c
  let z₁ : ℂ := (b : ℂ) + (u + τ : ℝ) * I
  let z₂ : ℂ := (c : ℂ) - (u : ℂ) * I
  let w₁ : ℂ := ((τ : ℂ) - (b : ℂ) * I) / u
  let w₂ : ℂ := (c : ℂ) * I / u
  have hd₁ : ‖d₁‖ ≤ M := by
    calc ‖d₁‖ ≤ ‖(b : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ ≤ M := by simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; dsimp [M]; linarith
  have hd₂ : ‖d₂‖ ≤ M := by
    change ‖(c : ℂ)‖ ≤ M
    simp only [Complex.norm_real, Real.norm_eq_abs]
    dsimp [M]; linarith
  have hw₁ : ‖w₁‖ ≤ M / u := by
    dsimp [w₁]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    apply div_le_div_of_nonneg_right _ hu0.le
    calc ‖(τ : ℂ) - (b : ℂ) * I‖ ≤ ‖(τ : ℂ)‖ + ‖(b : ℂ) * I‖ := norm_sub_le _ _
      _ ≤ M := by simp only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; dsimp [M]; linarith
  have hw₂ : ‖w₂‖ ≤ M / u := by
    dsimp [w₂]
    simpa only [norm_div, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hu0.le, d₂] using div_le_div_of_nonneg_right hd₂ hu0.le
  have hz₁ : ‖z₁‖ ≤ u + M := by
    have he : z₁ = (u : ℂ) * I + d₁ := by dsimp [z₁, d₁]; push_cast; ring
    rw [he]
    calc ‖(u : ℂ) * I + d₁‖ ≤ ‖(u : ℂ) * I‖ + ‖d₁‖ := norm_add_le _ _
      _ ≤ u + M := by simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hu0.le, add_comm] using add_le_add_left hd₁ u
  have hz₂ : ‖z₂‖ ≤ u + M := by
    calc ‖z₂‖ ≤ ‖(c : ℂ)‖ + ‖(u : ℂ) * I‖ := norm_sub_le _ _
      _ ≤ u + M := by simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hu0.le, d₂, add_comm] using add_le_add_right hd₂ u
  have hhalf : M / u ≤ 1 / 2 := (div_le_iff₀ hu0).2 (by linarith)
  have hf₁ : z₁ = (u : ℂ) * (I * (1 + w₁)) := by
    dsimp [z₁, w₁]; push_cast; field_simp; ring_nf; simp [I_sq]
  have hf₂ : z₂ = (u : ℂ) * (-I * (1 + w₂)) := by
    dsimp [z₂, w₂]; field_simp; ring_nf; simp [I_sq]
  have hl₁ := (log_ray_mul (hw₁.trans hhalf) hu0).1
  have hl₂ := (log_ray_mul (hw₂.trans hhalf) hu0).2
  rw [← hf₁] at hl₁
  rw [← hf₂] at hl₂
  let R₁ := (z₁ - 1 / 2) * (log (1 + w₁) - w₁) + (d₁ - 1 / 2) * w₁
  let R₂ := (z₂ - 1 / 2) * (log (1 + w₂) - w₂) + (d₂ - 1 / 2) * w₂
  have hR₁ : ‖R₁‖ ≤ D / u := stirling_exponent_error hM hu1 huM hz₁ hd₁ hw₁
  have hR₂ : ‖R₂‖ ≤ D / u := stirling_exponent_error hM hu1 huM hz₂ hd₂ hw₂
  have hR : ‖R₁ + R₂‖ ≤ 2 * D / u := by
    calc ‖R₁ + R₂‖ ≤ ‖R₁‖ + ‖R₂‖ := norm_add_le _ _
      _ ≤ D / u + D / u := add_le_add hR₁ hR₂
      _ = 2 * D / u := by ring
  have he : stirlingPair b c τ u = bMain b c τ u * exp (R₁ + R₂) := by
    rw [bMain_eq_exp b c τ u hu0, ← exp_add]
    unfold stirlingPair stirlingMain
    rw [← exp_add]
    congr 1
    change (z₁ - 1 / 2) * log z₁ - z₁ + 1 / 2 * log (2 * (Real.pi : ℂ)) +
      ((z₂ - 1 / 2) * log z₂ - z₂ + 1 / 2 * log (2 * (Real.pi : ℂ))) = _
    rw [hl₁, hl₂]
    dsimp [R₁, R₂, z₁, z₂, d₁, d₂, w₁, w₂]
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
    ring
  rw [he, ← mul_sub_one, norm_mul, norm_bMain b c τ u hu0]
  have hE := norm_exp_sub_one_le (hR.trans ((div_le_one hu0).2 huD))
  calc
    bAmp b c τ u * ‖exp (R₁ + R₂) - 1‖ ≤ bAmp b c τ u * (2 * (2 * D / u)) := by
      apply mul_le_mul_of_nonneg_left _ (bAmp_pos hu0).le
      exact hE.trans (mul_le_mul_of_nonneg_left hR (by norm_num))
    _ = 4 * D / u * bAmp b c τ u := by ring

theorem norm_mul_sub_mul_le_relative {a b x y : ℂ} {e : ℝ} (he : 0 ≤ e)
    (ha : ‖a - x‖ ≤ e * ‖x‖) (hb : ‖b - y‖ ≤ e * ‖y‖) :
    ‖a * b - x * y‖ ≤ (2 * e + e ^ 2) * ‖x * y‖ := by
  have hbn : ‖b‖ ≤ (1 + e) * ‖y‖ := by
    calc ‖b‖ ≤ ‖b - y‖ + ‖y‖ := norm_le_norm_sub_add b y
      _ ≤ e * ‖y‖ + ‖y‖ := by gcongr
      _ = (1 + e) * ‖y‖ := by ring
  calc
    ‖a * b - x * y‖ = ‖(a - x) * b + x * (b - y)‖ := by congr 1; ring
    _ ≤ ‖(a - x) * b‖ + ‖x * (b - y)‖ := norm_add_le _ _
    _ = ‖a - x‖ * ‖b‖ + ‖x‖ * ‖b - y‖ := by rw [norm_mul, norm_mul]
    _ ≤ (e * ‖x‖) * ((1 + e) * ‖y‖) + ‖x‖ * (e * ‖y‖) := by
      gcongr
    _ = (2 * e + e ^ 2) * ‖x * y‖ := by rw [norm_mul]; ring

theorem gammaPair_sub_stirlingPair (hStir : StirlingStrip) {B Y : ℝ}
    (hB : 1 / 2 ≤ B) (hY : 0 < Y) :
    ∃ K U : ℝ, 0 ≤ K ∧ Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u : ℝ, U ≤ u →
          ‖bKerH b c τ u - stirlingPair b c τ u‖ ≤ K / u * ‖stirlingPair b c τ u‖ := by
  obtain ⟨D, T, hD, hS⟩ := hStir (1 - B) B (by linarith)
  refine ⟨4 * D + 4 * D ^ 2, max (Y + 1) (max (2 * Y) (max (2 * T) 1)),
    by positivity, le_max_left _ _, ?_⟩
  intro b hb c hc τ hτ u hu
  have huY : Y + 1 ≤ u := (le_max_left _ _).trans hu
  have hu2Y : 2 * Y ≤ u := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hu
  have hu2T : 2 * T ≤ u :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hu
  have hu1 : 1 ≤ u :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hu
  have hu0 : 0 < u := by linarith
  have hτlo := (abs_le.mp hτ).1
  have hut : 0 < u + τ := by linarith
  have hhalf : u / 2 ≤ u + τ := by linarith
  have hTt : T ≤ u + τ := by linarith
  have hTu : T ≤ u := by linarith
  have he : 0 ≤ 2 * D / u := by positivity
  have hfirst : ‖Gamma ((b : ℂ) + (u + τ : ℝ) * I) -
      stirlingMain ((b : ℂ) + (u + τ : ℝ) * I)‖ ≤
      (2 * D / u) * ‖stirlingMain ((b : ℂ) + (u + τ : ℝ) * I)‖ := by
    have ht := hS ((b : ℂ) + (u + τ : ℝ) * I) (by simpa using hb.1)
      (by simpa using hb.2) (by simpa [abs_of_pos hut] using hTt)
    change _ ≤ D / |(((b : ℂ) + (u + τ : ℝ) * I).im)| * ‖stirlingMain _‖ at ht
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, abs_of_pos hut] at ht
    refine ht.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    apply (div_le_div_iff₀ hut hu0).2
    nlinarith
  have hsecond : ‖Gamma ((c : ℂ) - (u : ℂ) * I) -
      stirlingMain ((c : ℂ) - (u : ℂ) * I)‖ ≤
      (2 * D / u) * ‖stirlingMain ((c : ℂ) - (u : ℂ) * I)‖ := by
    have ht := hS ((c : ℂ) - (u : ℂ) * I) (by simpa using hc.1)
      (by simpa using hc.2) (by simpa [abs_of_pos hu0] using hTu)
    change _ ≤ D / |(((c : ℂ) - (u : ℂ) * I).im)| * ‖stirlingMain _‖ at ht
    simp only [sub_im, ofReal_im, mul_I_im, ofReal_re, zero_sub, abs_neg,
      abs_of_pos hu0] at ht
    refine ht.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact div_le_div_of_nonneg_right (by linarith) hu0.le
  have hp := norm_mul_sub_mul_le_relative he hfirst hsecond
  change ‖bKerH b c τ u - stirlingPair b c τ u‖ ≤
    (2 * (2 * D / u) + (2 * D / u) ^ 2) * ‖stirlingPair b c τ u‖ at hp
  refine hp.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hi : (1 / u : ℝ) ≤ 1 := (div_le_one hu0).2 hu1
  have hi0 : (0 : ℝ) ≤ 1 / u := by positivity
  have hi2 : (1 / u : ℝ) ^ 2 ≤ 1 / u := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hi2 (sq_nonneg (2 * D))
  simp only [div_eq_mul_inv, one_mul] at hh ⊢
  nlinarith [hh]

theorem norm_bKer_asymp (hStir : StirlingStrip) {B Y : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ K U : ℝ, 0 ≤ K ∧ Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u : ℝ, U ≤ u → ‖bKerH b c τ u - bMain b c τ u‖ ≤ K / u * bAmp b c τ u := by
  obtain ⟨K₁, U₁, hK₁, hU₁, h₁⟩ := gammaPair_sub_stirlingPair hStir hB hY
  obtain ⟨K₂, U₂, hK₂, hU₂, h₂⟩ := stirlingPair_asymp hB hB1 hY
  refine ⟨K₁ * (1 + K₂) + K₂, max U₁ U₂, by positivity,
    hU₁.trans (le_max_left _ _), ?_⟩
  intro b hb c hc τ hτ u hu
  have hu₁ := (le_max_left _ _).trans hu
  have hu₂ := (le_max_right _ _).trans hu
  have hu1 : 1 ≤ u := by linarith [hU₁.trans hu₁]
  have hu0 : 0 < u := by linarith
  have ha := h₁ b hb c hc τ hτ u hu₁
  have hb' := h₂ b hb c hc τ hτ u hu₂
  have hmain := norm_bMain b c τ u hu0
  have hAmp := (bAmp_pos (b := b) (c := c) (τ := τ) hu0).le
  have hn : ‖stirlingPair b c τ u‖ ≤ (1 + K₂) * bAmp b c τ u := by
    calc ‖stirlingPair b c τ u‖ ≤ ‖stirlingPair b c τ u - bMain b c τ u‖ +
        ‖bMain b c τ u‖ := norm_le_norm_sub_add _ _
      _ ≤ K₂ / u * bAmp b c τ u + bAmp b c τ u := by rw [hmain]; gcongr
      _ ≤ K₂ * bAmp b c τ u + bAmp b c τ u := by
        gcongr
        exact div_le_self hK₂ hu1
      _ = (1 + K₂) * bAmp b c τ u := by ring
  calc ‖bKerH b c τ u - bMain b c τ u‖ ≤
      ‖bKerH b c τ u - stirlingPair b c τ u‖ +
        ‖stirlingPair b c τ u - bMain b c τ u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K₁ / u) * ((1 + K₂) * bAmp b c τ u) + K₂ / u * bAmp b c τ u := by
      exact add_le_add (ha.trans (mul_le_mul_of_nonneg_left hn (by positivity))) hb'
    _ = (K₁ * (1 + K₂) + K₂) / u * bAmp b c τ u := by ring

end GoldbachBoundaries.Phi2HInf
