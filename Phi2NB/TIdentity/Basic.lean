import Phi2NB.Defs
import Phi2NB.ResidueAPI
import Phi2NB.LogDerivZeta
import Phi2NB.SigmaMeromorphic
import Phi2NB.SigmaFinite
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.IntegralBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.GammaStirlingAux

/-!
# Tools for the Mellin argument

* `norm_Gamma_mul_one_add_abs_im_pow_le`: polynomial decay of `Γ` on vertical strips.
* `verticalIntegral'_eq_add_of_simplePole`: moving a vertical line of integration past one simple pole.
* `mellin_convergent_and_hasSum_of_exp`: the Mellin transform of a sum of exponentials, with convergence.
* `continuous_Gamma_line`, `integrable_Gamma_mul_of_bound`: `Γ` along a vertical line, and integrability of `Γ`
  against a function of at most linear growth.

Bochner integrals are `0` when the integrand is not integrable; each lemma that evaluates one does so only where the
integrand is integrable (and its proof shows it).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries

namespace TIdentity

/-! ## Γ on vertical strips -/

/-- **Polynomial decay of `Γ` on vertical strips.** On `a ≤ Re z ≤ a'` with `a > 0`,
`|Γ(z)| (1 + |Im z|)^n` is bounded, for every `n`. (Stirling gives exponential decay; polynomial decay suffices
for every use here, since each is against a function of at most logarithmic or linear growth.)

Proof: induction on `n`, shifting the strip by `1` each time.
`n = 0`: `|Γ(z)| ≤ Γ(Re z)` (PNT+ `Complex.Gamma.norm_le_Gamma_re`), bounded on the compact
`[a, a']`. Step: `|Γ(z)| = |Γ(z + 1)| / |z|` and `|z| ≥ max(a, |Im z|) ≥ min(a, 1)(1 + |Im z|)/2`. -/
theorem norm_Gamma_mul_one_add_abs_im_pow_le {a a' : ℝ} (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ a' → ‖Gamma z‖ * (1 + |z.im|) ^ n ≤ C := by
  induction n generalizing a a' with
  | zero =>
    have hcont : ContinuousOn Real.Gamma (Icc a a') := fun x hx =>
      (Real.differentiableAt_Gamma fun m h => by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith [hx.1]).continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := a')).exists_bound_of_continuousOn hcont
    refine ⟨M, fun z hz1 hz2 => ?_⟩
    simp only [pow_zero, mul_one]
    calc ‖Gamma z‖ ≤ Real.Gamma z.re := Complex.Gamma.norm_le_Gamma_re (by linarith)
      _ ≤ ‖Real.Gamma z.re‖ := Real.le_norm_self _
      _ ≤ M := hM _ ⟨hz1, hz2⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih (a := a + 1) (a' := a' + 1) (by linarith)
    set c : ℝ := min a 1 / 2 with hcdef
    have hm0 : 0 < min a 1 := lt_min ha one_pos
    have hm1 : min a 1 ≤ a := min_le_left _ _
    have hm2 : min a 1 ≤ 1 := min_le_right _ _
    have hc : 0 < c := by positivity
    refine ⟨C / c, fun z hz1 hz2 => ?_⟩
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz1; simp at hz1; linarith
    have hnorm : ‖Gamma (z + 1)‖ = ‖z‖ * ‖Gamma z‖ := by rw [Gamma_add_one z hz0, norm_mul]
    have h1 := hC (z + 1) (by simp; linarith) (by simp; linarith)
    simp only [add_im, one_im, add_zero] at h1
    have hre : z.re ≤ ‖z‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm z)
    have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hnz : c * (1 + |z.im|) ≤ ‖z‖ := by
      rw [hcdef]
      rcases le_or_gt |z.im| 1 with h | h
      · nlinarith [abs_nonneg z.im]
      · nlinarith [abs_nonneg z.im]
    rw [le_div_iff₀ hc]
    calc ‖Gamma z‖ * (1 + |z.im|) ^ (n + 1) * c
        = (c * (1 + |z.im|)) * (‖Gamma z‖ * (1 + |z.im|) ^ n) := by ring
      _ ≤ ‖z‖ * (‖Gamma z‖ * (1 + |z.im|) ^ n) :=
          mul_le_mul_of_nonneg_right hnz (by positivity)
      _ = ‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n := by rw [hnorm]; ring
      _ ≤ C := h1

/-! ## Moving a vertical line of integration past a simple pole -/

/-- **Moving a vertical line of integration past one simple pole** (general; Cauchy's theorem
on rectangles plus the residue theorem for a simple pole). If `f` is holomorphic on the closed
strip `σ ≤ Re ≤ σ'` except at `p` (strictly inside), `f - A/(s - p)` is bounded near `p`, the
horizontal integrals tend to `0` as `Im → ±∞`, and `f` is integrable on both lines, then
`(2πi)⁻¹ ∫_{(σ')} f = A + (2πi)⁻¹ ∫_{(σ)} f`.

Proof: a port of PNT+ `PerronFormula.lean`,
`tendsto_truncated_vertical_shift_with_simple_pole` (the truncated left integral tends to
`VerticalIntegral' f σ' - A`; its proof uses only `ResidueTheoremOnRectangleWithSimplePole'` from
`ResidueCalcOnRectangles.lean`), then `tendsto_nhds_unique` against the left line's limit.
`PerronFormula` itself is not imported (its import chain is long). -/
theorem verticalIntegral'_eq_add_of_simplePole {σ σ' : ℝ} {f : ℂ → ℂ} {p A : ℂ}
    (hσ : σ < p.re ∧ p.re < σ')
    (hf : DifferentiableOn ℂ f (Icc σ σ' ×ℂ univ \ {p}))
    (hpole : (f - fun s => A / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hbot : Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun y : ℝ => ∫ x in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ => f (σ + y * I))
    (hright : Integrable fun y : ℝ => f (σ' + y * I)) :
    VerticalIntegral' f σ' = A + VerticalIntegral' f σ := by
  -- Port of PNT+ `tendsto_truncated_vertical_shift_with_simple_pole` (`PerronFormula.lean`).
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) = A := by
    filter_upwards [eventually_gt_atTop (|p.im| + 1)] with T hT
    have hTabs : |p.im| < T := by linarith
    have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg p.im) hTabs
    refine ResidueTheoremOnRectangleWithSimplePole' ?_ ?_ ?_ ?_ hpole
    · simp [le_of_lt (hσ.1.trans hσ.2)]
    · simp only [sub_im, ofReal_im, mul_im, I_re, zero_mul, I_im, ofReal_re, one_mul,
        zero_add, zero_sub, add_im]
      linarith
    · rw [rectangle_mem_nhds_iff]
      simp only [mem_reProdIm, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
        mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, one_mul, zero_add,
        zero_sub, add_im]
      constructor
      · rw [uIoo_of_lt (hσ.1.trans hσ.2)]
        exact ⟨hσ.1, hσ.2⟩
      · rw [uIoo_of_lt (by linarith)]
        exact abs_lt.mp hTabs
    · refine hf.mono (sdiff_subset_sdiff ?_ subset_rfl)
      intro z hz
      rw [Rectangle] at hz
      simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, sub_zero, add_re, add_zero, uIcc_of_le (le_of_lt (hσ.1.trans hσ.2)),
        mem_reProdIm] at hz
      exact ⟨hz.1, trivial⟩
  have hleft_eq : ∀ᶠ T : ℝ in atTop,
      (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ (-T) T =
        (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' (-T) -
          (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' T +
          (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ' (-T) T - A := by
    filter_upwards [hrect] with T hT
    have hT' : (1 / (2 * Real.pi * I) : ℂ) •
        RectangleIntegral f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) = A := by
      simpa [RectangleIntegral'] using hT
    calc
      (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ (-T) T
          = (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' (-T) -
              (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' T +
              (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ' (-T) T -
              (1 / (2 * Real.pi * I) : ℂ) •
                RectangleIntegral f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) := by
            simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
              ofReal_im, mul_zero, sub_self, sub_zero, sub_im, mul_im, one_mul, zero_add,
              zero_sub, add_re, add_zero, add_im]
            module
      _ = _ := by rw [hT']
  have hbotT : Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' (-T))
      atTop (𝓝 0) := by
    simpa [HIntegral] using
      (hbot.comp tendsto_neg_atTop_atBot).const_smul (1 / (2 * Real.pi * I) : ℂ)
  have htopT : Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • HIntegral f σ σ' T)
      atTop (𝓝 0) := by
    simpa [HIntegral] using htop.const_smul (1 / (2 * Real.pi * I) : ℂ)
  have hvert : ∀ τ : ℝ, Integrable (fun y : ℝ => f (τ + y * I)) →
      Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • VIntegral f τ (-T) T)
        atTop (𝓝 (VerticalIntegral' f τ)) := fun τ hτ => by
    simpa [VIntegral, VerticalIntegral', VerticalIntegral] using
      ((intervalIntegral_tendsto_integral hτ tendsto_neg_atTop_atBot tendsto_id).const_smul
        I).const_smul (1 / (2 * Real.pi * I) : ℂ)
  have hsum := ((hbotT.sub htopT).add (hvert σ' hright)).sub
    (tendsto_const_nhds (x := A) (f := atTop))
  have hlim : Tendsto (fun T : ℝ ↦ (1 / (2 * Real.pi * I) : ℂ) • VIntegral f σ (-T) T)
      atTop (𝓝 (VerticalIntegral' f σ' - A)) := by
    refine (hsum.congr' (hleft_eq.mono fun _ hT => hT.symm)).trans ?_
    simp
  have := tendsto_nhds_unique (hvert σ hleft) hlim
  rw [this]
  ring

/-! ## Mellin transforms of sums of exponentials; `Γ` on vertical lines -/

/-- "Mellin transform of a sum of exponentials" with convergence. Steps copied from Mathlib's
`hasSum_mellin` (`MellinEqDirichlet.lean`). -/
theorem mellin_convergent_and_hasSum_of_exp {ι : Type*} [Countable ι] {a : ι → ℂ}
    {w : ι → ℝ} {F : ℝ → ℂ} {s : ℂ} (hw : ∀ i, 0 < w i) (hs : 0 < s.re)
    (hF : ∀ t ∈ Ioi 0, HasSum (fun i ↦ a i * Real.exp (-w i * t)) (F t))
    (hFc : ContinuousOn F (Ioi 0))
    (h_sum : Summable fun i ↦ ‖a i‖ / (w i) ^ s.re) :
    MellinConvergent F s ∧ HasSum (fun i ↦ Gamma s * a i / w i ^ s) (mellin F s) := by
  set Fi : ι → ℝ → ℂ := fun i t ↦ (t : ℂ) ^ (s - 1) * (a i * Real.exp (-w i * t)) with hFi
  have hint : ∀ i, Integrable (Fi i) (volume.restrict (Ioi 0)) := fun i ↦ by
    have hpi := hw i
    simp only [hFi]
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc]
    have := Complex.GammaIntegral_convergent hs
    rw [← mul_zero (w i), ← integrableOn_Ioi_comp_mul_left_iff _ _ hpi] at this
    refine (IntegrableOn.congr_fun (this.const_mul (1 / w i ^ (s - 1)))
      (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi).const_mul _
    simp_rw [mul_comm (↑(Real.exp _) : ℂ), ← mul_assoc, neg_mul, ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hpi.le ht.le, ← mul_assoc, one_div, inv_mul_cancel₀, one_mul]
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (ofReal_ne_zero.mpr hpi.ne')
  have hnorm_sum : Summable fun i ↦ ∫ t in Ioi 0, ‖Fi i t‖ := by
    apply Summable.of_norm
    convert h_sum.mul_left (Real.Gamma s.re) using 2 with i
    simp only [hFi]
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc, norm_mul (a i), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc, norm_mul ‖a i‖, norm_norm]
    have hpi := hw i
    congr 1
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← neg_mul (w i), one_div, Real.inv_rpow hpi.le, ← div_eq_inv_mul] at this
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _)), ← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  have hval : HasSum (fun i ↦ Gamma s * a i / w i ^ s) (mellin F s) :=
    hasSum_mellin (fun i ↦ Or.inr (hw i)) hs hF h_sum
  refine ⟨?_, hval⟩
  -- convergence
  have hlin : ∑' i, ∫⁻ t in Ioi 0, ‖Fi i t‖ₑ ≠ ⊤ := by
    have (i : ι) : ∫⁻ t in Ioi 0, ‖Fi i t‖ₑ = ‖∫ t in Ioi 0, ‖Fi i t‖‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hint i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun a ↦ norm_nonneg (Fi i a)))]
      simp only [coe_nnnorm]
    rw [funext this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hnorm_sum.abs
  have heq : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) → (t : ℂ) ^ (s - 1) • F t = ∑' i, Fi i t := fun t ht ↦ by
    rw [smul_eq_mul, ← (hF t ht).tsum_eq, ← tsum_mul_left]
  refine ⟨?_, ?_⟩
  · refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
    exact ((continuousAt_ofReal_cpow_const t (s - 1) (Or.inr (ne_of_gt ht))).continuousWithinAt).smul
      (hFc t ht)
  · show ∫⁻ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) • F t‖ₑ < ⊤
    calc ∫⁻ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) • F t‖ₑ
        ≤ ∫⁻ t : ℝ in Ioi 0, ∑' i, ‖Fi i t‖ₑ := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht ↦ ?_
          rw [heq t ht]
          exact enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ t in Ioi 0, ‖Fi i t‖ₑ :=
          lintegral_tsum fun i ↦ (hint i).1.enorm
      _ < ⊤ := lt_top_iff_ne_top.mpr hlin

/-- `Γ` is continuous along a vertical line `Re z = σ > 0`. -/
theorem continuous_Gamma_line {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun y : ℝ => Gamma (σ + y * I) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hd : DifferentiableAt ℂ Gamma (σ + y * I) := differentiableAt_Gamma _ fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact hd.continuousAt.comp (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)

/-- Integrability of `Γ(σ + iy) q(y)` on a line `Re z = σ > 0`, as soon as `q` is continuous and
grows at most linearly in `|y|` (`norm_Gamma_mul_one_add_abs_im_pow_le` with `n = 3` against
`∫ (1 + |y|)^{-2} < ∞`). -/
theorem integrable_Gamma_mul_of_bound {σ : ℝ} (hσ : 0 < σ) {q : ℝ → ℂ}
    (hq : Continuous q) {K : ℝ} (hK : ∀ y : ℝ, ‖q y‖ ≤ K * (1 + |y|)) :
    Integrable fun y : ℝ => Gamma (σ + y * I) * q y := by
  obtain ⟨C, hC⟩ := norm_Gamma_mul_one_add_abs_im_pow_le (a := σ) (a' := σ) hσ 3
  have hK0 : 0 ≤ K := by
    have := hK 0
    simp only [abs_zero, add_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine Integrable.mono'
    ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul
      (C * K))
    (((continuous_Gamma_line hσ).mul hq).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have hC' := hC (σ + y * I) (by simp) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hC'
  have hpos : 0 < 1 + |y| := by positivity
  have hrpow : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hpos.le]
    norm_cast
  rw [hrpow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), norm_mul]
  have hq' := hK y
  calc ‖Gamma (σ + y * I)‖ * ‖q y‖ * (1 + |y|) ^ 2
      ≤ ‖Gamma (σ + y * I)‖ * (K * (1 + |y|)) * (1 + |y|) ^ 2 := by gcongr
    _ = K * (‖Gamma (σ + y * I)‖ * (1 + |y|) ^ 3) := by ring
    _ ≤ K * C := mul_le_mul_of_nonneg_left hC' hK0
    _ = C * K := by ring

end TIdentity

end GoldbachBoundaries
