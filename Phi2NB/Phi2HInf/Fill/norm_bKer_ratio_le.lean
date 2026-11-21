import Phi2NB.PhiR.Statement
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.norm_bKer_asymp
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.norm_bKer_ratio_le`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf

theorem bAmp_ratio_le {b c b₀ c₀ τ u₀ u : ℝ} (hα : b + c = b₀ + c₀)
    (hα1 : b + c - 1 ≤ 1) (hu₀ : 1 ≤ u₀) (hu : u₀ ≤ u) :
    bAmp b c τ u ≤ (1 + u - u₀) * Real.exp (-Real.pi * (u - u₀)) * bAmp b₀ c₀ τ u₀ := by
  have hu₀0 : 0 < u₀ := by linarith
  have hu0 : 0 < u := hu₀0.trans_le hu
  have hratio : 1 ≤ u / u₀ := (one_le_div hu₀0).2 hu
  have hp : (u / u₀) ^ (b + c - 1) ≤ 1 + u - u₀ := by
    calc (u / u₀) ^ (b + c - 1) ≤ (u / u₀) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hratio hα1
      _ = u / u₀ := Real.rpow_one _
      _ ≤ 1 + u - u₀ := by
        apply (div_le_iff₀ hu₀0).2
        nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu₀)]
  have he : Real.exp (-Real.pi * u - Real.pi * τ / 2) =
      Real.exp (-Real.pi * (u - u₀)) * Real.exp (-Real.pi * u₀ - Real.pi * τ / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow : u ^ (b + c - 1) = (u / u₀) ^ (b + c - 1) * u₀ ^ (b + c - 1) := by
    rw [← Real.mul_rpow (div_nonneg hu0.le hu₀0.le) hu₀0.le, div_mul_cancel₀ _ hu₀0.ne']
  unfold bAmp
  rw [he, hpow, ← hα]
  have hh := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ 2 * Real.pi * Real.exp (-Real.pi * (u - u₀)) *
      Real.exp (-Real.pi * u₀ - Real.pi * τ / 2) * u₀ ^ (b + c - 1))
  nlinarith [hh]

theorem norm_bKer_ratio_le (hStir : StirlingStrip) {B Y : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ K U : ℝ, 0 < K ∧ Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B,
      ∀ b₀ ∈ Icc (1 - B) B, ∀ c₀ ∈ Icc (1 - B) B, b + c = b₀ + c₀ →
      ∀ τ : ℝ, |τ| ≤ Y → ∀ u₀ u : ℝ, U ≤ u₀ → u₀ ≤ u →
        ‖bKerH b c τ u‖ ≤ K * (1 + u - u₀) * Real.exp (-Real.pi * (u - u₀)) *
          ‖bKerH b₀ c₀ τ u₀‖ := by
  obtain ⟨K, U, hK, hU, happrox⟩ := norm_bKer_asymp hStir hB hB1 hY
  refine ⟨3, max U (2 * K), by norm_num, hU.trans (le_max_left _ _), ?_⟩
  intro b hb c hc b₀ hb₀ c₀ hc₀ hα τ hτ u₀ u hu₀ hu
  have hU₀ : U ≤ u₀ := (le_max_left _ _).trans hu₀
  have hK₀ : 2 * K ≤ u₀ := (le_max_right _ _).trans hu₀
  have hu₀1 : 1 ≤ u₀ := by linarith [hU.trans hU₀]
  have hu₀0 : 0 < u₀ := by linarith
  have hu0 : 0 < u := hu₀0.trans_le hu
  have herr : ∀ v : ℝ, u₀ ≤ v → K / v ≤ 1 / 2 := by
    intro v hv
    apply (div_le_iff₀ (hu₀0.trans_le hv)).2
    linarith
  have he := (happrox b hb c hc τ hτ u (hU₀.trans hu)).trans
    (mul_le_mul_of_nonneg_right (herr u hu) (bAmp_pos hu0).le)
  have he₀ := (happrox b₀ hb₀ c₀ hc₀ τ hτ u₀ hU₀).trans
    (mul_le_mul_of_nonneg_right (herr u₀ le_rfl) (bAmp_pos hu₀0).le)
  have hn : ‖bKerH b c τ u‖ ≤ (3 / 2) * bAmp b c τ u := by
    have hh := norm_le_norm_sub_add (bKerH b c τ u) (bMain b c τ u)
    rw [norm_bMain b c τ u hu0] at hh
    linarith
  have hn₀ : bAmp b₀ c₀ τ u₀ ≤ 2 * ‖bKerH b₀ c₀ τ u₀‖ := by
    have hh := norm_le_norm_sub_add (bMain b₀ c₀ τ u₀) (bKerH b₀ c₀ τ u₀)
    rw [norm_bMain b₀ c₀ τ u₀ hu₀0, norm_sub_rev] at hh
    linarith
  have hamp := bAmp_ratio_le (τ := τ) hα (by linarith [hb.2, hc.2]) hu₀1 hu
  have hfac : 0 ≤ (1 + u - u₀) * Real.exp (-Real.pi * (u - u₀)) := by
    apply mul_nonneg (by linarith) (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_left hn₀ hfac
  nlinarith

end GoldbachBoundaries.Phi2HInf
