import Phi2NB.Phi2.Proof.M3Radial
import Phi2NB.Phi2.Fill.pairAtom_neg
import Phi2NB.Phi2.Fill.pairAtom_eq_two_tsum
import Phi2NB.Phi2.Fill.Aidx_bin_le
import Phi2NB.Phi2.Fill.sum_bKer_ne_zero

/-! The non-cancellation lemma: `pairAtom_ne_zero_of_large`. `K` from `Aidx_bin_le`, `U` from
`sum_bKer_ne_zero`, `H = max Y U`. For `τ > 0`: `pairAtom_eq_two_tsum`, then `sum_bKer_ne_zero` on `A_τ` with
`u₀ = min A_τ` (non-empty from a pair; the minimum exists because the part of `A_τ` below any point is a finite union
of unit fibres; every `u ∈ A_τ` exceeds `H ≥ U`, being the modulus of an ordinate of the pair `(ρ + iτ, ρ̄)`). For
`τ < 0`: `pairAtom_neg`, and conjugation `(ρ, ρ') ↦ (ρ̄, ρ̄')` carries `pairIdx τ` to `pairIdx (-τ)`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma fillDl_conj_sum (τ : ℝ) {a b : ℂ} (h : a + b = 1 + τ * I) :
    conj a + conj b = 1 + ((-τ : ℝ) : ℂ) * I := by
  rw [← map_add, h]
  apply Complex.ext <;> simp

/-- Conjugation of a pair. -/
private def fillDl_conjPair (τ : ℝ) (p : pairIdx τ) : pairIdx (-τ) :=
  ⟨(⟨conj (p.1.1 : ℂ), conj_mem_nontrivialZeros p.1.1.2⟩,
    ⟨conj (p.1.2 : ℂ), conj_mem_nontrivialZeros p.1.2.2⟩), fillDl_conj_sum τ p.2⟩

/-- Conjugation of a pair for `-τ`, back to `τ`. -/
private def fillDl_conjPairInv (τ : ℝ) (p : pairIdx (-τ)) : pairIdx τ :=
  ⟨(⟨conj (p.1.1 : ℂ), conj_mem_nontrivialZeros p.1.1.2⟩,
    ⟨conj (p.1.2 : ℂ), conj_mem_nontrivialZeros p.1.2.2⟩), by
      have := fillDl_conj_sum (-τ) p.2
      simpa using this⟩

/-- The pair `(i + iτ, ī)` of `i ∈ A_τ` (RH). -/
private def fillDl_pairL (hRH : RiemannHypothesis) (τ : ℝ) (i : Aidx τ) : pairIdx τ :=
  ⟨(⟨(i.1 : ℂ) + τ * I, i.2.2⟩, ⟨conj (i.1 : ℂ), conj_mem_nontrivialZeros i.1.2⟩), by
    have h := sigmaFinite_re_eq_half hRH i.1.2
    apply Complex.ext
    · simp; linarith
    · simp⟩

/-- A pair with both ordinates large yields an element of `A_τ` (RH, `0 < τ ≤ H`). -/
private lemma fillDl_nonempty (hRH : RiemannHypothesis) {H τ : ℝ} (hτ : 0 < τ) (hτH : τ ≤ H)
    (p : pairIdx τ) (hp : H < |(p.1.1 : ℂ).im| ∧ H < |(p.1.2 : ℂ).im|) : Nonempty (Aidx τ) := by
  have hρ := sigmaFinite_re_eq_half hRH p.1.1.2
  have hρ' := sigmaFinite_re_eq_half hRH p.1.2.2
  have him : (p.1.1 : ℂ).im + (p.1.2 : ℂ).im = τ := by
    have := congrArg Complex.im p.2
    simpa using this
  obtain ⟨h1, h2⟩ := hp
  by_cases hγ : 0 < (p.1.1 : ℂ).im
  · have hγ' : (p.1.2 : ℂ).im < 0 := by
      by_contra hc
      rw [abs_of_pos hγ] at h1
      linarith
    have heq : conj (p.1.2 : ℂ) + τ * I = p.1.1 := by
      apply Complex.ext <;> simp <;> linarith
    exact ⟨⟨⟨conj (p.1.2 : ℂ), conj_mem_nontrivialZeros p.1.2.2⟩,
      by simp; linarith, by rw [heq]; exact p.1.1.2⟩⟩
  · have hγn : (p.1.1 : ℂ).im < 0 := by
      rcases (not_lt.mp hγ).lt_or_eq with h | h
      · exact h
      · rw [h, abs_zero] at h1; linarith
    have heq : conj (p.1.1 : ℂ) + τ * I = p.1.2 := by
      apply Complex.ext <;> simp <;> linarith
    exact ⟨⟨⟨conj (p.1.1 : ℂ), conj_mem_nontrivialZeros p.1.1.2⟩,
      by simp; linarith, by rw [heq]; exact p.1.2.2⟩⟩

private lemma fillDl_one_le_zetaMult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ zetaMult ρ :=
  one_le_zetaMult_of_zero (fun h => by
    have := hρ.2.2; rw [h, Complex.one_re] at this; exact lt_irrefl _ this) hρ.1

/-- **The non-cancellation lemma** (RH, (RiemannVonMangoldt)): for each `Y > 0` there is `H ≥ Y` such that `μ{τ} ≠ 0`
whenever `0 < |τ| ≤ Y`, `τ` has a representation, and every representation has both ordinates of modulus `> H`.
Positive `τ`: `pairAtom_eq_two_tsum`, then `sum_bKer_ne_zero` on `A_τ` with `u₀ = min A_τ` (exists: `A_τ` is non-empty
and has finitely many points in each unit interval, `Aidx_bin_le`), `K` from `Aidx_bin_le`, `H = max Y U`. Negative
`τ`: `pairAtom_neg`, and `(ρ, ρ') ↦ (ρ̄, ρ̄')` maps `pairIdx (-τ)` onto `pairIdx τ` preserving `|γ|`. -/
theorem pairAtom_ne_zero_of_large (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) {Y : ℝ} (hY : 0 < Y) :
    ∃ H : ℝ, Y ≤ H ∧ ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ Y → Nonempty (pairIdx τ) →
      (∀ p : pairIdx τ, H < |(p.1.1 : ℂ).im| ∧ H < |(p.1.2 : ℂ).im|) → pairAtom τ ≠ 0 := by
  classical
  obtain ⟨K, hK⟩ := Aidx_bin_le hRH hRvM hY
  obtain ⟨U, hU⟩ := sum_bKer_ne_zero (K := K) hY
  refine ⟨max Y U, le_max_left _ _, ?_⟩
  set H := max Y U with hH
  -- the positive case
  have hpos : ∀ τ : ℝ, 0 < τ → τ ≤ Y → Nonempty (pairIdx τ) →
      (∀ p : pairIdx τ, H < |(p.1.1 : ℂ).im| ∧ H < |(p.1.2 : ℂ).im|) → pairAtom τ ≠ 0 := by
    intro τ hτ hτY hne hlarge
    have hτm : τ ∈ Ioc (0 : ℝ) Y := ⟨hτ, hτY⟩
    rw [pairAtom_eq_two_tsum hRH hRvM (le_max_left Y U) hτm hlarge]
    refine mul_ne_zero two_ne_zero ?_
    obtain ⟨p⟩ := hne
    obtain ⟨i₁⟩ := fillDl_nonempty hRH hτ (hτY.trans (le_max_left _ _)) p (hlarge p)
    set u : Aidx τ → ℝ := fun i => (i.1 : ℂ).im with hu
    -- every height exceeds `H`
    have hbig : ∀ i : Aidx τ, H < u i := by
      intro i
      have h := (hlarge (fillDl_pairL hRH τ i)).2
      have hp : 0 < (i.1 : ℂ).im := i.2.1
      change H < |(conj (i.1 : ℂ)).im| at h
      rw [Complex.conj_im, abs_neg, abs_of_pos hp] at h
      exact h
    -- the minimum of `A_τ`
    set S := {i : Aidx τ | u i ≤ u i₁} with hS
    have hSfin : S.Finite := by
      refine (Set.Finite.biUnion (Finset.range (⌊u i₁⌋₊ + 1)).finite_toSet
        (fun k _ => (hK τ hτm (k : ℝ)).1)).subset ?_
      intro i hi
      have hp : 0 ≤ u i := (i.2.1).le
      simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_ofPred_eq]
      refine ⟨⌊u i⌋₊, ?_, Nat.floor_le hp, Nat.lt_floor_add_one _⟩
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hi)
    obtain ⟨i₀, hi₀S, hi₀⟩ := hSfin.toFinset.exists_min_image u ⟨i₁, by simp [hS]⟩
    have hmin : ∀ i, u i₀ ≤ u i := by
      intro i
      by_cases hi : i ∈ S
      · exact hi₀ i (hSfin.mem_toFinset.mpr hi)
      · have h1 : u i₁ < u i := by simpa [hS] using hi
        have h2 : u i₀ ≤ u i₁ := by simpa [hS] using (hSfin.mem_toFinset.mp hi₀S)
        linarith
    have hq : 1 ≤ Aweight τ i₀ := by
      have h1 := fillDl_one_le_zetaMult i₀.1.2
      have h2 := fillDl_one_le_zetaMult i₀.2.2
      simp only [Aweight]
      nlinarith
    exact hU τ hτm u (Aweight τ) i₀ ((le_max_right Y U).trans (hbig i₀).le) hmin hq
      (fun v => (hK τ hτm v).1) (fun v hv => (hK τ hτm v).2 hv)
  intro τ hτ0 hτY hne hlarge
  rcases lt_or_gt_of_ne hτ0 with hneg | hpos'
  · -- `τ < 0`: conjugate
    have hσ : 0 < -τ := neg_pos.mpr hneg
    have hσY : -τ ≤ Y := by rw [abs_of_neg hneg] at hτY; exact hτY
    have hconj : pairAtom τ = conj (pairAtom (-τ)) := by
      have := pairAtom_neg (-τ)
      rwa [neg_neg] at this
    rw [hconj]
    intro h0
    have h1 : pairAtom (-τ) = 0 := by simpa using h0
    obtain ⟨p⟩ := hne
    refine hpos (-τ) hσ hσY ⟨fillDl_conjPair τ p⟩ (fun p' => ?_) h1
    -- conjugate `p'` back to a pair for `τ`
    have hback := hlarge (fillDl_conjPairInv τ p')
    simpa [fillDl_conjPairInv, Complex.conj_im, abs_neg] using hback
  · exact hpos τ hpos' (by rwa [abs_of_pos hpos'] at hτY) hne hlarge

end GoldbachBoundaries.Phi2Proof
