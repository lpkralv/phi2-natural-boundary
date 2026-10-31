import Phi2NB.Phi2.Proof.M1Continuation
import Phi2NB.Paper2.M5.Fill.noMeromorphicExtensionAt_of_line_blowup
import Phi2NB.Paper2.M5.Fill.exists_ordinate_in_interval
import Phi2NB.Density

/-! Conjugate zeros have the same multiplicity: `zetaMult_conj`. `ψ(s̄) = conj ψ(s)` (`riemannZeta_conj`, Mathlib's
`deriv_conj_conj`), so `(s - ρ̄) ψ(s) = conj((s̄ - ρ)ψ(s̄))`, and the residue `-m(ρ)` of `ψ` at `ρ` is carried to
`ρ̄`; `HasResidue.unique` against `hasResidue_negLogDerivZeta_of_mem_nontrivialZeros` at `ρ̄` gives `m(ρ̄) = m(ρ)`. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `ψ(s̄) = conj ψ(s)`. -/
lemma fillB_negLogDerivZeta_conj (s : ℂ) : negLogDerivZeta (conj s) = conj (negLogDerivZeta s) := by
  have hd : deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
    have h := congrFun (deriv_conj_conj (f := riemannZeta)) (conj s)
    simpa [Function.comp_def] using h
  simp only [negLogDerivZeta, hd, riemannZeta_conj, map_neg, map_div₀]

/-- **Conjugate zeros have the same multiplicity** (no RH). `ψ(s̄) = conj ψ(s)` (Mathlib `riemannZeta_conj` and the
conjugation rule for derivatives), so the residue of `ψ` at `ρ̄` is the conjugate of its residue `-m(ρ)` at `ρ`
(`hasResidue_negLogDerivZeta_of_mem_nontrivialZeros`), and `HasResidue.unique` gives `m(ρ̄) = m(ρ)`.
Uses `conj_mem_nontrivialZeros` (`Density.lean`). -/
theorem zetaMult_conj {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : zetaMult (conj ρ) = zetaMult ρ := by
  have h1 := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros hρ).1
  have h2 := (hasResidue_negLogDerivZeta_of_mem_nontrivialZeros (conj_mem_nontrivialZeros hρ)).1
  -- transport the residue at `ρ` to `ρ̄`
  have hconj : Tendsto (fun s : ℂ => conj s) (𝓝[≠] (conj ρ)) (𝓝[≠] ρ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (Complex.continuous_conj.tendsto (conj ρ))
      rw [Complex.conj_conj] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      apply hw
      have := congrArg conj h
      simpa using this
  have h3 : HasResidue negLogDerivZeta (conj ρ) (conj (-(zetaMult ρ : ℂ))) := by
    have hc := (Complex.continuous_conj.tendsto _).comp (h1.comp hconj)
    refine hc.congr' (Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    rw [map_mul, map_sub, Complex.conj_conj, fillB_negLogDerivZeta_conj, Complex.conj_conj]
  have h4 := h2.unique h3
  rw [map_neg, Complex.conj_natCast, neg_inj] at h4
  exact_mod_cast h4

end GoldbachBoundaries.Phi2Proof
