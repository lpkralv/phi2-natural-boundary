import Phi2NB.Phi2.Defs
import Phi2NB.Phi2.Proof.M5Boundary

/-!
# Under RH, `Re s = 1` is a natural boundary of `Φ₂`

`Φ₂(s) = ∑_{m,n ≥ 1} Λ(m)Λ(n)(m+n)^{-s}` converges absolutely for `σ = Re s > 2`. The theorem
`phi2_natural_boundary` says, under RH:

1. `Φ₂` continues from `σ > 2` to a meromorphic function on `ℍ = {σ > 1}` that is analytic off the points `2` and
   `1 + ρ` (`ρ` a non-trivial zero of `ζ`) and has a simple pole at each of them, with residue `1` at `2` and
   `-2m(ρ)/ρ` at `1 + ρ` (`m(ρ)` the multiplicity of `ρ`); and
2. the line `σ = 1` is a natural boundary of every meromorphic continuation of `Φ₂` to `ℍ`, in the sense of
   `IsNaturalBoundary`: no function meromorphic on a disc centred on the line agrees with it on the part of the disc
   in `ℍ`, off a discrete set.

`phi2_natural_boundary_classical` restates part 2 in the classical form, with agreement at every point of the part
of the disc in `ℍ`; it is the case of part 2 with an empty exceptional set.

## Hypotheses

RH is Mathlib's `RiemannHypothesis`. Three classical theorems on the zeros of `ζ` are taken as named premises
(defined in `Paper2/Defs.lean`; they are hypotheses of the theorem, not axioms, and are not proved here). All three
are in Titchmarsh, *The Theory of the Riemann Zeta-Function*, Ch. IX.

* `RiemannVonMangoldt`, the local count of zeros (Thm 9.2): `N(t+1) - N(t) ≤ C₁ log(t+3)` for `t ≥ 0`.
* `LogDerivZetaLocal`, the local expansion of `ζ'/ζ`: `ζ'/ζ(z) = ∑_{|γ - Im z| ≤ 1} m(ρ)/(z - ρ) + O(log |Im z|)` uniformly for
  `-1 ≤ Re z ≤ 2`, `|Im z| ≥ 2`.
* `LittlewoodGap`, Littlewood's theorem on gaps between ordinates: for large `t` there is an ordinate `γ` with
  `|γ - t| < a / log log log t`.

The symmetry of the zeros with their multiplicities, (ZeroSymmetry), is not a premise: under RH it is proved
(`Phi2Proof.zeroSymmetry_of_RH`). The continuation (part 1) uses RH alone.

The proof is in `Phi2/Proof/` (the main steps) and `Phi2/Fill/` (the supporting lemmas), with no `sorry`;
`#print axioms GoldbachBoundaries.phi2_natural_boundary` gives `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

open GoldbachBoundaries.Paper2

/-! ## The theorem -/

/-- **Theorem.** Assume RH, (RiemannVonMangoldt), (LogDerivZetaLocal) and Littlewood's gap theorem. Then

* there is `F` meromorphic on `ℍ = {σ > 1}`, equal to `Φ₂` on `σ > 2`, analytic on `ℍ ∖ phi2Poles`, with a simple
  pole (order `-1`) at every point of `phi2Poles = {2} ∪ {1 + ρ}`, whose residues `res` satisfy `HasPhi2Residues`
  (`1` at `2`, `-2m(ρ)/ρ` at `1 + ρ`) and are all non-zero; and
* every `F` meromorphic on `ℍ` that agrees with `Φ₂` off a discrete subset of `σ > 2` has the line `σ = 1` as a
  natural boundary (`IsNaturalBoundary F HH lineOne`).

The continuation is `Phi2Proof.Phi2c` (`Phi2Proof.phi2_continuation`, which uses RH only); the boundary clause is
`Phi2Proof.phi2_boundary`. -/
theorem phi2_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue F α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne) :=
  ⟨⟨Phi2Proof.Phi2c, Phi2Proof.phi2_continuation hRH⟩,
    fun F hF hFΦ => Phi2Proof.phi2_boundary hRH hRvM hLD hL F hF hFΦ⟩

/-- **Corollary (classical form of the natural boundary).** Under the hypotheses of `phi2_natural_boundary`, let `F` be
a meromorphic continuation of `Φ₂` to `ℍ` (meromorphic on `ℍ` and equal to `Φ₂` on `σ > 2`; `Phi2Proof.Phi2c` is one,
`Phi2Proof.phi2_continuation`). Then for every point `1 + iτ` of the line `σ = 1` and every `r > 0`, no function `g`
meromorphic on the disc `|s - (1 + iτ)| < r` coincides with `F` at every point of the disc with `σ > 1`.

This is the second clause of `phi2_natural_boundary` with an empty exceptional set: agreement on all of `σ > 2`
implies agreement off a discrete subset of it, and agreement at every point of `ball (1 + iτ) r ∩ ℍ` implies
agreement off a discrete subset of that set. -/
theorem phi2_natural_boundary_classical (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt)
    (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFΦ : EqOn F Phi2 (halfPlane 2)) (τ r : ℝ) (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball (1 + τ * I) r) ∧ EqOn g F (ball (1 + τ * I) r ∩ HH) := by
  rintro ⟨g, hg, hgF⟩
  have hcod : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 := by
    filter_upwards [self_mem_codiscreteWithin (halfPlane 2)] with s hs using hFΦ hs
  have hline : (1 + τ * I : ℂ) ∈ lineOne := by
    show (1 + τ * I : ℂ).re = 1
    simp
  refine (phi2_natural_boundary hRH hRvM hLD hL).2 F hF hcod (1 + τ * I) hline r hr ⟨g, hg, ?_⟩
  filter_upwards [self_mem_codiscreteWithin (ball (1 + τ * I) r ∩ HH)] with s hs using hgF hs

end GoldbachBoundaries
