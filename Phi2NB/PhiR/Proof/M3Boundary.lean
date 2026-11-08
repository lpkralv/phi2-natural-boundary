import Phi2NB.PhiR.Proof.M2Continuation
import Phi2NB.Phi2.Proof.M5Boundary
import Phi2NB.PhiR.Fill.noMeromorphicExtensionAt_comp_sub_iff
import Phi2NB.PhiR.Fill.noMeromorphicExtensionAt_iff_of_eq_add_mul

/-!
# Step M3: the natural boundary of `Φ_r` (Theorem 7.1(ii)), transferred from `Φ₂`

On `σ > r - 1`, `PhiRc r = rest + f₄ · Phi2c(· - (r-2))`, with `rest`
meromorphic and `f₄` analytic and non-zero on the open half-plane `σ > r - 3/2`, which contains the line `σ = r - 1`.
So a meromorphic extension of `Φ_r` across a point `z₀` of the line gives one of `Phi2c(· - (r-2))` across `z₀`
(`(g - rest)/f₄`), i.e. of `Phi2c` across `z₀ - (r - 2)`, a point of `σ = 1`; this contradicts `phi2_boundary`.
The converse direction (needed for the pointwise statement) is `rest + f₄ · g`.

Lemmas proved in `Fill/` (abstract complex analysis, no number theory): `noMeromorphicExtensionAt_comp_sub_iff`,
`noMeromorphicExtensionAt_iff_of_eq_add_mul`. Proved in this file: `preimage_sub_halfPlane`,
`eventuallyEq_nhdsNE_of_agree_halfPlane`, `PhiRc_eq_add_mul`, `Phi2c_natural_boundary`,
`noMeromorphicExtensionAt_PhiR_iff`, `phiR_boundary`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof GoldbachBoundaries.Paper2

/-! ## Abstract transfer lemmas -/

/-- Translating a half-plane: `{s : Re(s - c) > a} = {Re s > a + c}` for real `c`. -/
theorem preimage_sub_halfPlane (a c : ℝ) :
    (fun s : ℂ => s - (c : ℂ)) ⁻¹' halfPlane a = halfPlane (a + c) := by
  ext s
  simp only [halfPlane, mem_preimage, Set.mem_ofPred_eq, sub_re, ofReal_re]
  constructor <;> intro h <;> linarith

/-- **Translation** (no number theory): `H` has no meromorphic extension across `z₀` from `U` iff
`s ↦ H(s - c)` has none across `z₀ + c` from the translate `{s : s - c ∈ U}`.
Proof: an extension `f` on `ball z₀ ρ` gives `f(· - c)` on `ball (z₀ + c) ρ` (`MeromorphicOn.comp_analyticOn`-style,
`MeromorphicAt.comp_analyticAt` pointwise), and `s ↦ s - c` is a homeomorphism mapping `ball (z₀+c) ρ ∩ (· - c)⁻¹' U`
onto `ball z₀ ρ ∩ U`, so it maps `codiscreteWithin` to `codiscreteWithin` (`mem_codiscreteWithin`, `𝓝[≠]` is carried
by the homeomorphism); the other direction is the same with `-c`. -/
theorem noMeromorphicExtensionAt_comp_sub_iff {H : ℂ → ℂ} {U : Set ℂ} {z₀ c : ℂ} :
    NoMeromorphicExtensionAt (fun s => H (s - c)) ((fun s => s - c) ⁻¹' U) (z₀ + c) ↔
      NoMeromorphicExtensionAt H U z₀ :=
  FillC.noMeromorphicExtensionAt_comp_sub_iff'

/-- **Adding a meromorphic function and multiplying by a non-vanishing analytic one** (no number theory): if `W` is open,
`z₀ ∈ W`, `D` is meromorphic on `W`, `f` is analytic and non-zero on `W`, and `F = D + f·H` off a discrete subset of
`U`, then `F` has a meromorphic extension across `z₀` (from `U`) iff `H` does.
Proof: shrink the disc into `W` (`Metric.isOpen_iff`; `NoMeromorphicExtensionAt` quantifies over all radii, so a
smaller disc suffices). `g` extends `H` ⟹ `D + f g` extends `F`; `g` extends `F` ⟹ `(g - D)/f` extends `H` (`1/f` is
analytic on `W`). Agreement off a discrete set: intersect the two `codiscreteWithin` sets after
`Filter.codiscreteWithin_mono` (as in `Phi2Proof.isNaturalBoundary_of_eventuallyEq_add`). -/
theorem noMeromorphicExtensionAt_iff_of_eq_add_mul {F D f H : ℂ → ℂ} {U W : Set ℂ} {z₀ : ℂ}
    (hW : IsOpen W) (hz₀ : z₀ ∈ W) (hD : MeromorphicOn D W) (hf : AnalyticOnNhd ℂ f W)
    (hf0 : ∀ s ∈ W, f s ≠ 0) (hF : F =ᶠ[codiscreteWithin U] fun s => D s + f s * H s) :
    NoMeromorphicExtensionAt F U z₀ ↔ NoMeromorphicExtensionAt H U z₀ :=
  FillC.noMeromorphicExtensionAt_iff_of_eq_add_mul' hW hz₀ hD hf hf0 hF

/-- Identity theorem on `σ > a` (`Phi2Proof.eventuallyEq_nhdsNE_of_agree_halfPlane_two'` with `ℍ`, `2`, `3`
replaced by `σ > a`, `σ > b`, `b + 1`): two meromorphic functions on `σ > a` that agree with `G` on `σ > b ≥ a`
(one off a discrete set) agree on a punctured neighbourhood of every point of `σ > a`. -/
theorem eventuallyEq_nhdsNE_of_agree_halfPlane {a b : ℝ} (hab : a ≤ b) {F F₀ G : ℂ → ℂ}
    (hF : MeromorphicOn F (halfPlane a)) (hF₀ : MeromorphicOn F₀ (halfPlane a))
    (hF₀G : EqOn F₀ G (halfPlane b)) (hFG : F =ᶠ[codiscreteWithin (halfPlane b)] G) {z : ℂ}
    (hz : z ∈ halfPlane a) : F =ᶠ[𝓝[≠] z] F₀ := by
  set p : ℂ := ((b + 1 : ℝ) : ℂ) with hp
  have hpb : p ∈ halfPlane b := by show b < p.re; simp [hp]
  have hpa : p ∈ halfPlane a := by show a < p.re; simp [hp]; linarith
  have hn : halfPlane b ∈ 𝓝 p := (isOpen_halfPlane b).mem_nhds hpb
  have hFGp : F =ᶠ[𝓝[≠] p] G := eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hFG hn
  have hF₀Gp : F₀ =ᶠ[𝓝[≠] p] G :=
    Filter.mem_of_superset (nhdsWithin_le_nhds hn) fun s hs => hF₀G hs
  have htopp : meromorphicOrderAt (F - F₀) p = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hFGp, hF₀Gp] with s h1 h2
    simp [h1, h2]
  have htop : meromorphicOrderAt (F - F₀) z = ⊤ :=
    (hF.sub hF₀).meromorphicOrderAt_eq_top_of_isPreconnected (isPreconnected_halfPlane a) hpa hz htopp
  rw [meromorphicOrderAt_eq_top_iff] at htop
  filter_upwards [htop] with s hs
  exact sub_eq_zero.mp hs

/-! ## The transfer for `Φ_r` -/

/-- `PhiRc r = rest + f₄ · Phi2c(· - (r - 2))`, pointwise (the definition, with
`s - r + 2 = s - (r - 2)`). -/
theorem PhiRc_eq_add_mul (r : ℕ) (s : ℂ) :
    PhiRc r s = phiRRest r s + phiRCoef r s * Phi2c (s - (((r : ℝ) - 2 : ℝ) : ℂ)) := by
  have h : s - (r : ℂ) + 2 = s - (((r : ℝ) - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [PhiRc, h, add_comm]

/-- `σ = 1` is a natural boundary of the continuation `Phi2c` (RH, (RiemannVonMangoldt), (LogDerivZetaLocal), Littlewood): `phi2_boundary`
applied to `Phi2c` itself. -/
theorem Phi2c_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    IsNaturalBoundary Phi2c HH lineOne := by
  obtain ⟨hmero, heq, -⟩ := phi2_continuation hRH
  refine phi2_boundary hRH hRvM hLD hL Phi2c hmero ?_
  filter_upwards [self_mem_codiscreteWithin (halfPlane 2)] with s hs using heq hs

/-- **The pointwise transfer** (RH only): for every meromorphic continuation `F` of `Φ_r` to `σ > r - 1`
and every point `z₀` of the line `σ = r - 1`, `F` has no meromorphic extension across `z₀` iff `Phi2c` has none across
`z₀ - (r - 2)` (a point of `σ = 1`). The proof of Theorem 7.1(ii) in the paper argues one direction (an extension for `Φ_r` gives one for `Φ₂`); this
is the equivalence, for the meromorphic notion of extension, and at every `τ` (including `τ = 0`). -/
theorem noMeromorphicExtensionAt_PhiR_iff (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r) {z₀ : ℂ} (hz₀ : z₀.re = (r : ℝ) - 1) :
    NoMeromorphicExtensionAt F (halfPlane ((r : ℝ) - 1)) z₀ ↔
      NoMeromorphicExtensionAt Phi2c HH (z₀ - (((r : ℝ) - 2 : ℝ) : ℂ)) := by
  have hmero := meromorphicOn_PhiRc hRH hr
  have heq : EqOn (PhiRc r) (PhiR r) (halfPlane r) := fun s hs => (PhiR_eq_PhiRc hr hs).symm
  set c : ℝ := (r : ℝ) - 2 with hc
  have hagree : F =ᶠ[codiscreteWithin (halfPlane ((r : ℝ) - 1))]
      fun s => phiRRest r s + phiRCoef r s * Phi2c (s - (c : ℂ)) := by
    have h1 : F =ᶠ[codiscreteWithin (halfPlane ((r : ℝ) - 1))] PhiRc r :=
      eventuallyEq_codiscreteWithin_of_nhdsNE fun a ha =>
        eventuallyEq_nhdsNE_of_agree_halfPlane (by linarith) hF hmero heq hFΦ ha
    filter_upwards [h1] with s hs
    rw [hs, PhiRc_eq_add_mul]
  have hW : z₀ ∈ halfPlane ((r : ℝ) - 3 / 2) := by show _ < z₀.re; linarith
  rw [noMeromorphicExtensionAt_iff_of_eq_add_mul (isOpen_halfPlane _) hW (meromorphicOn_phiRRest hRH hr)
    (fun s hs => analyticAt_phiRCoef (by have : (r : ℝ) - 3 / 2 < s.re := hs; linarith))
    (fun s hs => phiRCoef_ne_zero hr (by have : (r : ℝ) - 3 / 2 < s.re := hs; linarith)) hagree]
  have hpre : (fun s : ℂ => s - (c : ℂ)) ⁻¹' HH = halfPlane ((r : ℝ) - 1) := by
    rw [preimage_sub_halfPlane, hc]; congr 1; ring
  have := noMeromorphicExtensionAt_comp_sub_iff (H := Phi2c) (U := HH) (z₀ := z₀ - (c : ℂ)) (c := (c : ℂ))
  rwa [sub_add_cancel, hpre] at this

/-- **Theorem 7.1(ii), boundary clause** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal), Littlewood): every meromorphic continuation of `Φ_r`
to `σ > r - 1` has `σ = r - 1` as a natural boundary. -/
theorem phiR_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) {r : ℕ} (hr : 2 ≤ r)
    (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r) :
    IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)) := by
  intro z₀ hz₀
  have hz₀' : z₀.re = (r : ℝ) - 1 := hz₀
  rw [noMeromorphicExtensionAt_PhiR_iff hRH hr F hF hFΦ hz₀']
  refine Phi2c_natural_boundary hRH hRvM hLD hL _ ?_
  show (z₀ - (((r : ℝ) - 2 : ℝ) : ℂ)).re = 1
  simp only [sub_re, ofReal_re]
  linarith

end GoldbachBoundaries.PhiRProof
