import Phi2NB.Phi2.Proof.M3Radial

/-! The atom `μ{τ}` as a sum over `A_τ`: `pairAtom_eq_two_tsum`. Under RH every zero is `1/2 + iγ`, so a pair
`(ρ, ρ')` with `ρ + ρ' = 1 + iτ` has `γ + γ' = τ`; with `|γ|, |γ'| > H ≥ Y ≥ τ > 0` the two ordinates have opposite
signs. The map `e : A_τ ⊕ A_τ → pairIdx τ`, `inl i ↦ (i + iτ, ī)`, `inr i ↦ (ī, i + iτ)`, is a bijection (the sign
of the first ordinate separates `inl` from `inr`), and both images carry the term `m(i) m(i + iτ) b_τ(Im i)`
(`zetaMult_conj`, `i + iτ = 1/2 + i(u+τ)`, `ī = 1/2 - iu`). Summability of each half comes from
`summable_norm_pair` through the injective map into `NontrivialZeros × NontrivialZeros`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma fillDz_sumL (hRH : RiemannHypothesis) {τ : ℝ} (i : Aidx τ) :
    ((i.1 : ℂ) + τ * I) + conj (i.1 : ℂ) = 1 + τ * I := by
  have h := sigmaFinite_re_eq_half hRH i.1.2
  apply Complex.ext
  · simp; linarith
  · simp

/-- `inl i ↦ (i + iτ, ī)`. -/
private def fillDz_eL (hRH : RiemannHypothesis) (τ : ℝ) (i : Aidx τ) : pairIdx τ :=
  ⟨(⟨(i.1 : ℂ) + τ * I, i.2.2⟩, ⟨conj (i.1 : ℂ), conj_mem_nontrivialZeros i.1.2⟩), fillDz_sumL hRH i⟩

/-- `inr i ↦ (ī, i + iτ)`. -/
private def fillDz_eR (hRH : RiemannHypothesis) (τ : ℝ) (i : Aidx τ) : pairIdx τ :=
  ⟨(⟨conj (i.1 : ℂ), conj_mem_nontrivialZeros i.1.2⟩, ⟨(i.1 : ℂ) + τ * I, i.2.2⟩), by
    rw [add_comm]; exact fillDz_sumL hRH i⟩

private def fillDz_e (hRH : RiemannHypothesis) (τ : ℝ) : Aidx τ ⊕ Aidx τ → pairIdx τ :=
  Sum.elim (fillDz_eL hRH τ) (fillDz_eR hRH τ)

private lemma fillDz_e_injective (hRH : RiemannHypothesis) {τ : ℝ} (hτ : 0 < τ) :
    Function.Injective (fillDz_e hRH τ) := by
  intro a b hab
  have h1 := congrArg (fun p : pairIdx τ => (p.1.1 : ℂ)) hab
  rcases a with i | i <;> rcases b with j | j <;>
    simp only [fillDz_e, Sum.elim_inl, Sum.elim_inr, fillDz_eL, fillDz_eR] at h1
  · have hij : (i.1 : ℂ) = j.1 := by simpa using h1
    exact congrArg Sum.inl (Subtype.ext (Subtype.ext hij))
  · have := congrArg Complex.im h1
    simp at this
    linarith [i.2.1, j.2.1]
  · have := congrArg Complex.im h1
    simp at this
    linarith [i.2.1, j.2.1]
  · have hij : (i.1 : ℂ) = j.1 := by simpa using congrArg conj h1
    exact congrArg Sum.inr (Subtype.ext (Subtype.ext hij))

private lemma fillDz_e_surjective (hRH : RiemannHypothesis) {Y H τ : ℝ} (hYH : Y ≤ H)
    (hτ : τ ∈ Ioc (0 : ℝ) Y)
    (hlarge : ∀ p : pairIdx τ, H < |(p.1.1 : ℂ).im| ∧ H < |(p.1.2 : ℂ).im|) :
    Function.Surjective (fillDz_e hRH τ) := by
  intro p
  have hρ := sigmaFinite_re_eq_half hRH p.1.1.2
  have hρ' := sigmaFinite_re_eq_half hRH p.1.2.2
  have him : (p.1.1 : ℂ).im + (p.1.2 : ℂ).im = τ := by
    have := congrArg Complex.im p.2
    simpa using this
  obtain ⟨hτ0, hτY⟩ := hτ
  obtain ⟨h1, h2⟩ := hlarge p
  by_cases hγ : 0 < (p.1.1 : ℂ).im
  · have hγ' : (p.1.2 : ℂ).im < 0 := by
      by_contra hc
      rw [abs_of_pos hγ] at h1
      linarith
    have heq : conj (p.1.2 : ℂ) + τ * I = p.1.1 := by
      apply Complex.ext <;> simp <;> linarith
    let i : Aidx τ := ⟨⟨conj (p.1.2 : ℂ), conj_mem_nontrivialZeros p.1.2.2⟩,
      by simp; linarith, by rw [heq]; exact p.1.1.2⟩
    refine ⟨Sum.inl i, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact heq
    · change conj (conj (p.1.2 : ℂ)) = p.1.2
      simp
  · have hγn : (p.1.1 : ℂ).im < 0 := by
      rcases (not_lt.mp hγ).lt_or_eq with h | h
      · exact h
      · rw [h, abs_zero] at h1; linarith
    have heq : conj (p.1.1 : ℂ) + τ * I = p.1.2 := by
      apply Complex.ext <;> simp <;> linarith
    let i : Aidx τ := ⟨⟨conj (p.1.1 : ℂ), conj_mem_nontrivialZeros p.1.1.2⟩,
      by simp; linarith, by rw [heq]; exact p.1.2.2⟩
    refine ⟨Sum.inr i, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · change conj (conj (p.1.1 : ℂ)) = p.1.1
      simp
    · exact heq

/-- The term identity `a(i + iτ) a(ī) = m(i) m(i + iτ) b_τ(Im i)`. -/
private lemma fillDz_term (hRH : RiemannHypothesis) {τ : ℝ} (i : Aidx τ) :
    zeroCoef ((i.1 : ℂ) + τ * I) * zeroCoef (conj (i.1 : ℂ)) =
      (Aweight τ i : ℂ) * bKer τ ((i.1 : ℂ).im) := by
  have hre := sigmaFinite_re_eq_half hRH i.1.2
  have hA : (i.1 : ℂ) + τ * I = 1 / 2 + (((i.1 : ℂ).im + τ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hB : conj (i.1 : ℂ) = 1 / 2 - (((i.1 : ℂ).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hm : zetaMult (conj (i.1 : ℂ)) = zetaMult (i.1 : ℂ) := zetaMult_conj i.1.2
  simp only [zeroCoef, Aweight, bKer, hm]
  rw [hA, hB]
  rw [← hA]
  push_cast
  ring

/-- **`μ{τ}` as a sum over `A_τ`** (RH, (RiemannVonMangoldt) for the summability): if `0 < τ ≤ Y ≤ H` and every representation `ρ + ρ' = 1 + iτ` has
`|γ|, |γ'| > H`, then no representation has both ordinates of one sign (`γ + γ' = τ ≤ Y ≤ H`), every one is
`(ρ + iτ, ρ̄)` or `(ρ̄, ρ + iτ)` with `ρ = 1/2 + iu`, `u > 0`, and
`μ{τ} = 2 ∑_{A_τ} m(ρ) m(ρ + iτ) b_τ(u)` (using `m(ρ̄) = m(ρ)`, `zetaMult_conj`). Both sides are genuine sums.
The proof reindexes by the bijection `A_τ ⊕ A_τ → pairIdx τ` of the module docstring. -/
theorem pairAtom_eq_two_tsum (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) {Y H τ : ℝ} (hYH : Y ≤ H)
    (hτ : τ ∈ Ioc (0 : ℝ) Y)
    (hlarge : ∀ p : pairIdx τ, H < |(p.1.1 : ℂ).im| ∧ H < |(p.1.2 : ℂ).im|) :
    pairAtom τ = 2 * ∑' i : Aidx τ, (Aweight τ i : ℂ) * bKer τ ((i.1 : ℂ).im) := by
  set f : pairIdx τ → ℂ := fun p => zeroCoef p.1.1 * zeroCoef p.1.2 with hf
  have hS : Summable f :=
    Summable.of_norm ((summable_norm_pair hRH hRvM).comp_injective Subtype.val_injective)
  let E : Aidx τ ⊕ Aidx τ ≃ pairIdx τ :=
    Equiv.ofBijective (fillDz_e hRH τ)
      ⟨fillDz_e_injective hRH hτ.1, fillDz_e_surjective hRH hYH hτ hlarge⟩
  have hE : ∀ s, E s = fillDz_e hRH τ s := fun s => rfl
  have hL : ∀ i, f (E (Sum.inl i)) = (Aweight τ i : ℂ) * bKer τ ((i.1 : ℂ).im) := by
    intro i
    rw [hE]
    exact fillDz_term hRH i
  have hR : ∀ i, f (E (Sum.inr i)) = (Aweight τ i : ℂ) * bKer τ ((i.1 : ℂ).im) := by
    intro i
    rw [hE, ← fillDz_term hRH i]
    exact mul_comm _ _
  have h1 : Summable ((fun s => f (E s)) ∘ Sum.inl) :=
    hS.comp_injective (E.injective.comp Sum.inl_injective)
  have h2 : Summable ((fun s => f (E s)) ∘ Sum.inr) :=
    hS.comp_injective (E.injective.comp Sum.inr_injective)
  change ∑' p, f p = _
  rw [← E.tsum_eq, Summable.tsum_sum h1 h2, two_mul]
  congr 1
  · exact tsum_congr hL
  · exact tsum_congr hR

end GoldbachBoundaries.Phi2Proof
