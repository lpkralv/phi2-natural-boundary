import Phi2NB.Defs
import Phi2NB.ResidueAPI
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-!
# The logarithmic derivative `-ζ'/ζ`

`A z := -(ζ'(z) / ζ(z))`. We prove:

* `meromorphicAt_negLogDerivZeta`: `A` is meromorphic at every point;
* `hasResidue_negLogDerivZeta_one`: `HasResidue A 1 1`;
* `hasResidue_negLogDerivZeta_of_ne_one`: for every `ρ ≠ 1`, `HasResidue A ρ (-(m(ρ)))`, with
  `m = zetaMult`; at a zero `ρ ≠ 1`, `1 ≤ m(ρ)` (`one_le_zetaMult_of_zero`); both for every
  non-trivial zero (`hasResidue_negLogDerivZeta_of_mem_nontrivialZeros`);
* `analyticAt_negLogDerivZeta`: `A` is analytic at every `z ≠ 1` with `ζ z ≠ 0`;
* the general lemma behind the residues: if `f` is meromorphic at `p` with order `n ∈ ℤ`, then
  `HasResidue (logDeriv f) p n` (`hasResidue_logDeriv_of_meromorphicOrderAt`).

## Junk values

`A` is defined pointwise by a quotient, so at a pole of `A` (the point `1` and the zeros of `ζ`)
its value is junk (Lean's `x / 0 = 0`; also `ζ 1` is itself a junk value). Every statement here is
about punctured neighbourhoods (`HasResidue`, `meromorphicOrderAt`) or about points where `A` is
analytic, so the junk values never enter.

## Reuse

* PNT+ `logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt`
  (`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean`): `logDeriv f - n/(s - p)` is bounded
  on a punctured neighbourhood of `p` when `f` has order `n` at `p`.
* The three facts `meromorphicAt_riemannZeta`, `meromorphicOrderAt_riemannZeta_ne_top`,
  `meromorphicOrderAt_riemannZeta_one` are proved in PNT+ (`IEANTN/KadiriEq12Helpers.lean`) in a
  module that imports `IEANTN.ZetaDefinitions` and its long import chain, which
  `Defs.lean` avoids. They are re-proved here, following the PNT+ proofs, from Mathlib only.
* Mathlib: `analyticOn_riemannZeta`, `riemannZeta_residue_one`, `riemannZeta_eventually_ne_zero_nhds_one`,
  `riemannZeta_ne_zero_of_one_le_re`, `meromorphicOrderAt_mul`, `meromorphicOrderAt_eq_int_iff`.
-/

noncomputable section

open Complex Filter Topology Set Asymptotics

namespace GoldbachBoundaries

/-! ## Residue of a logarithmic derivative -/

/-- If `f` is meromorphic at `p` with order `n ∈ ℤ`, then `logDeriv f` has residue `n` at `p`. -/
theorem hasResidue_logDeriv_of_meromorphicOrderAt {f : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = (n : WithTop ℤ)) :
    HasResidue (logDeriv f) p (n : ℂ) :=
  hasResidue_of_sub_isBigO (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf hord)

/-! ## Meromorphy and order of `ζ` -/

/-- `ζ` is meromorphic at every point. (Re-proof of the PNT+ lemma of the same name in
`IEANTN/KadiriEq12Helpers.lean`, via `ζ = Λ / Γ_ℝ`.) -/
theorem meromorphicAt_riemannZeta (s : ℂ) : MeromorphicAt riemannZeta s := by
  have hΛ : MeromorphicAt completedRiemannZeta s := by
    rw [show completedRiemannZeta = fun z ↦ completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) from
      funext completedRiemannZeta_eq]
    exact (((differentiable_completedZeta₀.analyticAt s).meromorphicAt.sub
      ((MeromorphicAt.const 1 s).div analyticAt_id.meromorphicAt)).sub
      ((MeromorphicAt.const 1 s).div ((analyticAt_const.sub analyticAt_id).meromorphicAt)))
  have hG : MeromorphicAt Gammaℝ s := by
    rw [show Gammaℝ = fun z ↦ (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) from
      funext Gammaℝ_def]
    refine MeromorphicAt.mul (AnalyticAt.meromorphicAt ?_)
      (MeromorphicAt.comp_analyticAt (f := Complex.Gamma) (g := fun z : ℂ ↦ z / 2) (x := s)
        ((MeromorphicOn.Gamma (s := Set.univ)) (s / 2) (Set.mem_univ _)) (by fun_prop))
    rw [show (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2))
        = fun z ↦ Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) from by
      funext z; rw [Complex.cpow_def_of_ne_zero (by simp [Real.pi_ne_zero])]]
    fun_prop
  have hz0 : ∀ᶠ z in 𝓝[≠] s, z ≠ 0 := by
    rcases eq_or_ne s 0 with h | h
    · subst h; exact self_mem_nhdsWithin
    · exact (isOpen_compl_singleton.eventually_mem (Set.mem_compl_singleton_iff.mpr h)).filter_mono
        nhdsWithin_le_nhds
  exact (hΛ.div hG).congr ((by
    filter_upwards [hz0] with z hz using riemannZeta_def_of_ne_zero hz :
    riemannZeta =ᶠ[𝓝[≠] s] fun z ↦ completedRiemannZeta z / Gammaℝ z)).symm

/-- `ζ` is not identically zero near any point. (Re-proof of the PNT+ lemma.) -/
theorem meromorphicOrderAt_riemannZeta_ne_top (z : ℂ) : meromorphicOrderAt riemannZeta z ≠ ⊤ := by
  rcases eq_or_ne z 1 with h | h
  · subst h
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_riemannZeta 1)).2
      (riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds)
  · have hz1 : z ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := h
    rw [(analyticOn_riemannZeta z hz1).meromorphicOrderAt_eq, Ne, ENat.map_eq_top_iff]
    have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simp
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have hord2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
      rw [(analyticOn_riemannZeta 2 h2).analyticOrderAt_eq_zero.mpr
        (riemannZeta_ne_zero_of_one_le_re (by norm_num))]; simp
    exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected hconn h2 hz1 hord2

/-- `ζ` has a simple pole at `1`: its meromorphic order there is `-1`. (Re-proof of the PNT+
lemma.) -/
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = ((-1 : ℤ) : WithTop ℤ) := by
  have hsub : MeromorphicAt (fun s : ℂ ↦ s - 1) 1 :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have h0 : meromorphicOrderAt ((fun s : ℂ ↦ s - 1) * riemannZeta) 1 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
      (hsub.mul (meromorphicAt_riemannZeta 1))).1 ⟨1, one_ne_zero, riemannZeta_residue_one⟩
  rw [meromorphicOrderAt_mul hsub (meromorphicAt_riemannZeta 1),
    meromorphicOrderAt_id_sub_const] at h0
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (meromorphicOrderAt_riemannZeta_ne_top 1)
  rw [← hn] at h0 ⊢
  have hni : (1 : ℤ) + n = 0 := by exact_mod_cast h0
  norm_cast
  omega

/-- Away from `1`, the order of `ζ` is the natural number `zetaMult`. -/
theorem meromorphicOrderAt_riemannZeta_eq_zetaMult {ρ : ℂ} (hρ : ρ ≠ 1) :
    meromorphicOrderAt riemannZeta ρ = (((zetaMult ρ : ℕ) : ℤ) : WithTop ℤ) := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ
  have hntop := meromorphicOrderAt_riemannZeta_ne_top ρ
  unfold zetaMult
  rw [han.meromorphicOrderAt_eq] at hntop ⊢
  cases hO : analyticOrderAt riemannZeta ρ with
  | top => rw [hO] at hntop; exact absurd rfl hntop
  | coe n =>
    rw [ENat.map_natCast, WithTop.untopD_coe]
    simp

/-- `zetaMult ρ` is the analytic order of `ζ` at `ρ ≠ 1`. -/
theorem analyticOrderAt_riemannZeta_eq_zetaMult {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ = (zetaMult ρ : ℕ∞) := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ
  have h := meromorphicOrderAt_riemannZeta_eq_zetaMult hρ
  rw [han.meromorphicOrderAt_eq] at h
  cases hO : analyticOrderAt riemannZeta ρ with
  | top => rw [hO] at h; simp at h
  | coe n =>
    rw [hO, ENat.map_natCast] at h
    have : (n : ℤ) = (zetaMult ρ : ℤ) := by exact_mod_cast h
    exact_mod_cast this

/-- At a zero `ρ ≠ 1` of `ζ`, `zetaMult ρ ≥ 1`. -/
theorem one_le_zetaMult_of_zero {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    1 ≤ zetaMult ρ := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ
  have h := analyticOrderAt_riemannZeta_eq_zetaMult hρ
  rcases Nat.eq_zero_or_pos (zetaMult ρ) with h0 | h0
  · rw [h0, Nat.cast_zero, han.analyticOrderAt_eq_zero] at h
    exact absurd hz h
  · exact h0

/-! ## The function `A = -ζ'/ζ` -/

/-- `A(z) = -(ζ'(z)/ζ(z))`. Its values at `1` and at the zeros of `ζ` are junk (see the module
docstring); all statements about `A` are on punctured neighbourhoods or at points of analyticity.
-/
def negLogDerivZeta (z : ℂ) : ℂ := -(deriv riemannZeta z / riemannZeta z)

theorem negLogDerivZeta_eq : negLogDerivZeta = fun z => -logDeriv riemannZeta z := by
  funext z; simp [negLogDerivZeta, logDeriv_apply]

/-- `A` is meromorphic at every point. -/
theorem meromorphicAt_negLogDerivZeta (z : ℂ) : MeromorphicAt negLogDerivZeta z :=
  ((meromorphicAt_riemannZeta z).deriv.div (meromorphicAt_riemannZeta z)).neg

/-- `Res_{z=1} A = 1`. -/
theorem hasResidue_negLogDerivZeta_one : HasResidue negLogDerivZeta 1 1 := by
  have h := (hasResidue_logDeriv_of_meromorphicOrderAt (meromorphicAt_riemannZeta 1)
    meromorphicOrderAt_riemannZeta_one).neg
  rw [negLogDerivZeta_eq]
  simpa using h

/-- For every `ρ ≠ 1`: `Res_{z=ρ} A = -m(ρ)` (which is `0` where `ζ ρ ≠ 0`). -/
theorem hasResidue_negLogDerivZeta_of_ne_one {ρ : ℂ} (hρ : ρ ≠ 1) :
    HasResidue negLogDerivZeta ρ (-(zetaMult ρ : ℂ)) := by
  have h := (hasResidue_logDeriv_of_meromorphicOrderAt (meromorphicAt_riemannZeta ρ)
    (meromorphicOrderAt_riemannZeta_eq_zetaMult hρ)).neg
  rw [negLogDerivZeta_eq]
  simpa using h

/-- At a zero `ρ ≠ 1` of `ζ`: `Res_{z=ρ} A = -m(ρ)` and `m(ρ) ≥ 1`. -/
theorem hasResidue_negLogDerivZeta_of_zero {ρ : ℂ} (hρ : ρ ≠ 1) (hz : riemannZeta ρ = 0) :
    HasResidue negLogDerivZeta ρ (-(zetaMult ρ : ℂ)) ∧ 1 ≤ zetaMult ρ :=
  ⟨hasResidue_negLogDerivZeta_of_ne_one hρ, one_le_zetaMult_of_zero hρ hz⟩

/-- At a non-trivial zero `ρ`: `Res_{z=ρ} A = -m(ρ)` and `m(ρ) ≥ 1`. -/
theorem hasResidue_negLogDerivZeta_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    HasResidue negLogDerivZeta ρ (-(zetaMult ρ : ℂ)) ∧ 1 ≤ zetaMult ρ := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp [NontrivialZeros] at hρ
  exact hasResidue_negLogDerivZeta_of_zero hρ1 hρ.1

/-- `A` is analytic at every `z ≠ 1` with `ζ z ≠ 0`. -/
theorem analyticAt_negLogDerivZeta {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z ≠ 0) :
    AnalyticAt ℂ negLogDerivZeta z := by
  have han : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz1
  exact (han.deriv.div han hz).neg

/-- `A` is differentiable at every `z ≠ 1` with `ζ z ≠ 0`. -/
theorem differentiableAt_negLogDerivZeta {z : ℂ} (hz1 : z ≠ 1) (hz : riemannZeta z ≠ 0) :
    DifferentiableAt ℂ negLogDerivZeta z :=
  (analyticAt_negLogDerivZeta hz1 hz).differentiableAt

end GoldbachBoundaries
