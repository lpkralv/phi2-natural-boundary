import Phi2NB.Paper2.M4b.Fill.BCommon

/-!
# The principal part of `g·f` at a simple pole of `f`

`(z - p) f(z)` agrees near `p` with a function `H` differentiable at `p`, `H p = R`
(`exists_numerator_of_simplePole`: normal form `f = (z - p)^n φ`, `n ≥ -1`, or `f = 0` near `p` when the order is
`⊤`); then `g f - g(p) R/(z - p)` is the slope of `g H` at `p`, which converges, hence is bounded
(`isBigO_mul_sub_of_numerator`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The residue of `g·f` at a simple pole of `f`** (general). `f` has order `≥ -1` at `p` and residue `R`, so
`f(z) = R/(z - p) + h(z)` with `h` bounded near `p` (`MeromorphicAt` normal form: `(z - p)f(z)` extends analytically
with value `R` at `p`, by `HasResidue`; if the order is `⊤`, `R = 0` and `f = 0` near `p`). Then
`g f - g(p)R/(z - p) = R(g(z) - g(p))/(z - p) + g h`, both bounded (`AnalyticAt` gives `g(z) - g(p) = O(z - p)`). -/
theorem isBigO_mul_sub_residue {f g : ℂ → ℂ} {p R : ℂ} (hf : MeromorphicAt f p)
    (hord : -1 ≤ meromorphicOrderAt f p) (hres : HasResidue f p R) (hg : AnalyticAt ℂ g p) :
    (fun z => g z * f z - g p * R / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  obtain ⟨H, hH, hHp, hev⟩ := exists_numerator_of_simplePole hf hord hres
  have := isBigO_mul_sub_of_numerator hH hg.differentiableAt hev
  rwa [hHp] at this

end GoldbachBoundaries.Paper2.M4b
