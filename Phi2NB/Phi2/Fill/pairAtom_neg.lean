import Phi2NB.Phi2.Proof.M3Radial

/-! Conjugation of the atom: `pairAtom_neg`. Conjugation `(ρ, ρ') ↦ (ρ̄, ρ̄')` is a bijection
`pairIdx τ ≃ pairIdx (-τ)` (`conj (1 + iτ) = 1 - iτ`), and `zeroCoef ρ̄ = conj (zeroCoef ρ)` at a zero
(`zetaMult_conj`, `Complex.Gamma_conj`). Then `Equiv.tsum_eq` and `Complex.conj_tsum`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma fillDz_zeroCoef_conj {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    zeroCoef (conj ρ) = conj (zeroCoef ρ) := by
  simp only [zeroCoef, zetaMult_conj hρ, Complex.Gamma_conj, map_mul, Complex.conj_natCast]

private lemma fillDz_conj_sum (τ : ℝ) {a b : ℂ} (h : a + b = 1 + τ * I) :
    conj a + conj b = 1 + ((-τ : ℝ) : ℂ) * I := by
  rw [← map_add, h]
  apply Complex.ext <;> simp

/-- Conjugation of a pair. -/
private def fillDz_conjPair (τ : ℝ) (p : pairIdx τ) : pairIdx (-τ) :=
  ⟨(⟨conj (p.1.1 : ℂ), conj_mem_nontrivialZeros p.1.1.2⟩,
    ⟨conj (p.1.2 : ℂ), conj_mem_nontrivialZeros p.1.2.2⟩), fillDz_conj_sum τ p.2⟩

/-- The inverse: conjugation of a pair for `-τ`. -/
private def fillDz_conjPairInv (τ : ℝ) (p : pairIdx (-τ)) : pairIdx τ :=
  ⟨(⟨conj (p.1.1 : ℂ), conj_mem_nontrivialZeros p.1.1.2⟩,
    ⟨conj (p.1.2 : ℂ), conj_mem_nontrivialZeros p.1.2.2⟩), by
      have := fillDz_conj_sum (-τ) p.2
      simpa using this⟩

private def fillDz_conjEquiv (τ : ℝ) : pairIdx τ ≃ pairIdx (-τ) where
  toFun := fillDz_conjPair τ
  invFun := fillDz_conjPairInv τ
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [fillDz_conjPair, fillDz_conjPairInv]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      simp [fillDz_conjPair, fillDz_conjPairInv]

/-- **Conjugation** (no hypotheses): `μ{-τ} = conj μ{τ}`, via `(ρ, ρ') ↦ (ρ̄, ρ̄')`, `zetaMult_conj`, `Complex.Gamma_conj`. -/
theorem pairAtom_neg (τ : ℝ) : pairAtom (-τ) = conj (pairAtom τ) := by
  unfold pairAtom
  rw [← (fillDz_conjEquiv τ).tsum_eq, Complex.conj_tsum]
  congr 1
  funext p
  change zeroCoef (conj (p.1.1 : ℂ)) * zeroCoef (conj (p.1.2 : ℂ)) = _
  rw [fillDz_zeroCoef_conj p.1.1.2, fillDz_zeroCoef_conj p.1.2.2, map_mul]

end GoldbachBoundaries.Phi2Proof
