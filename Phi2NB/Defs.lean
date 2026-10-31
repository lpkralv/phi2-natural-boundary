import Mathlib
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Basic definitions

Half-planes and the line `σ = 1`; the non-trivial zeros of `ζ` and their multiplicity `m(ρ)`; residues at simple
poles (`HasResidue`); and the natural-boundary predicate.

## Junk-value discipline

`tsum` returns `0` where a series is not summable, and `riemannZeta 1` and quotients by `0` are junk values. No
statement evaluates a series off its half-plane of absolute convergence. Continuations are always existentially (or
universally) quantified functions that agree with the series on the half-plane of convergence; boundary statements
compare functions only off a discrete set (`=ᶠ[codiscreteWithin _]`) or on a punctured neighbourhood
(`=ᶠ[𝓝[≠] _]`), never pointwise at a possible pole.

## Relation to PrimeNumberTheoremAnd (PNT+)

* `zetaMult ρ` is `(riemannZeta.order ρ).toNat` for PNT+'s `riemannZeta.order`
  (`PrimeNumberTheoremAnd/IEANTN/ZetaDefinitions.lean`), written out here so that we do not
  import that module, which pulls in a long import chain. The two agree by `rfl`
  once both are in scope.
* `NontrivialZeros` is the same set as PNT+'s `Kadiri.NontrivialZeros`
  (`riemannZeta.zeroes_rect (Ioo 0 1) univ`), written out for the same reason.
* Residues are stated with `HasResidue` (a `Tendsto` of `(s - a) * f s` on the punctured
  neighbourhood), which is junk-free.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-! ## Half-planes and the line `σ = 1` -/

/-- The open right half-plane `{s : Re s > a}`. -/
def halfPlane (a : ℝ) : Set ℂ := {s | a < s.re}

/-- The half-plane `ℍ = {s : σ > 1}`. -/
abbrev HH : Set ℂ := halfPlane 1

/-- The line `σ = 1`, i.e. the points `1 + iy`, `y ∈ ℝ`. -/
def lineOne : Set ℂ := {s | s.re = 1}

lemma isOpen_halfPlane (a : ℝ) : IsOpen (halfPlane a) :=
  isOpen_lt continuous_const Complex.continuous_re

/-! ## Zeros of ζ, multiplicity -/

/-- The non-trivial zeros of `ζ`: zeros in the critical strip `0 < Re ρ < 1`.
(Same set as PNT+'s `Kadiri.NontrivialZeros`.) This is equivalent to the classical notion "zero that is not a
negative even integer" because `ζ ≠ 0` on `Re s ≥ 1`, off the real axis on `Re s ≤ 0` (functional equation), and on
the real half-line `(-∞, 0]` except at `-2, -4, …` (`ζ(0) = -1/2`; at the other non-positive reals the
functional equation gives a non-zero value). We use the strip form because it needs no theorem to
state. -/
def NontrivialZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The multiplicity `m(ρ)` of a zero: `meromorphicOrderAt riemannZeta ρ`, converted to `ℕ`
(`⊤ ↦ 0`, negative ↦ `0`; neither case occurs at a zero `ρ ≠ 1`, see `one_le_zetaMult_of_zero` in
`LogDerivZeta.lean`). Definitionally `(riemannZeta.order ρ).toNat` in PNT+. -/
def zetaMult (ρ : ℂ) : ℕ := ((meromorphicOrderAt riemannZeta ρ).untopD 0).toNat

/-! ## Residues at simple poles -/

/-- `HasResidue f a c`: `(s - a) f(s) → c` as `s → a`, `s ≠ a`. At a pole of order at most one
this says the residue of `f` at `a` is `c`. It looks only at the punctured neighbourhood, so the
value `f a` (junk at a pole) plays no role. -/
def HasResidue (f : ℂ → ℂ) (a c : ℂ) : Prop :=
  Tendsto (fun s => (s - a) * f s) (𝓝[≠] a) (𝓝 c)

/-! ## Natural boundaries -/

/-- `F`, given on the open set `U`, has no meromorphic extension across `z₀`: for no `r > 0` is
there a meromorphic `f` on `Δ(z₀, r)` equal to `F` on `Δ(z₀, r) ∩ U` off a discrete set. -/
def NoMeromorphicExtensionAt (F : ℂ → ℂ) (U : Set ℂ) (z₀ : ℂ) : Prop :=
  ∀ r : ℝ, 0 < r → ¬ ∃ f : ℂ → ℂ, MeromorphicOn f (ball z₀ r) ∧
    f =ᶠ[codiscreteWithin (ball z₀ r ∩ U)] F

/-- `L` is a natural boundary of `F` (given on `U`): no point of `L` has a disc on which `F` extends
meromorphically. -/
def IsNaturalBoundary (F : ℂ → ℂ) (U L : Set ℂ) : Prop :=
  ∀ z₀ ∈ L, NoMeromorphicExtensionAt F U z₀

end GoldbachBoundaries
