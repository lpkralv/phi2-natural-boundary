import Phi2NB.Phi2.Proof.M1Continuation
import Phi2NB.Paper2.M5.Fill.noMeromorphicExtensionAt_of_line_blowup
import Phi2NB.Paper2.M5.Fill.exists_ordinate_in_interval
import Phi2NB.Density
import Phi2NB.Phi2.Fill.zetaMult_conj
import Phi2NB.Phi2.Fill.summable_norm_zeroCoef
import Phi2NB.Phi2.Fill.BCommon
import Phi2NB.Phi2.Fill.negLogDerivZeta_good_height
import Phi2NB.Phi2.Fill.rect_kernelL
import Phi2NB.Phi2.Fill.verticalIntegral'_kernelL_zero_shift
import Phi2NB.Phi2.Fill.norm_verticalIntegral'_kernelL_two_fifths_le

/-!
# The explicit formula for `FL` near `0`

Under RH, (RiemannVonMangoldt) and (LogDerivZetaLocal):
`FL(t) = 1/t - ∑_ρ m(ρ)Γ(ρ) t^{-ρ} + R(t)` with `|R(t)| ≤ C t^{-2/5}` for all `t > 0` (`hL_explicit`).

The inverse Mellin line is shifted from `Re w = 3/4` to `Re w = 2/5`, across the zeros, and no further: the remainder
`O(t^{-2/5})` already makes the leftover of `hL²` an `O(t^{-9/10})`, integrable against `t^{σ-1}` for `σ > 9/10`, which
is all the radial limit needs. Stopping there avoids `ψ` on `Re w ≤ 1/3`, the pole of `Γ` at `0`, and the constant
`-log 2π` (the residue at `w = 0`, which belongs to `phi2Main`'s pole at `s = 1` and plays no part at `τ ≠ 0`).

(ZeroSymmetry) is not a premise: under RH it is proved (`zeroSymmetry_of_RH`, from `zetaMult_conj`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas proved in `Fill/`

One file per lemma, imported above: `zetaMult_conj`, `summable_norm_zeroCoef`, `negLogDerivZeta_good_height`,
`rect_kernelL`, `verticalIntegral'_kernelL_zero_shift`, `norm_verticalIntegral'_kernelL_two_fifths_le`. -/

/-! ## (ZeroSymmetry) from RH -/

/-- **(ZeroSymmetry) holds under RH**: `ρ̄` is a zero of the same multiplicity, and `1 - ρ̄ = ρ` on the critical
line. -/
theorem zeroSymmetry_of_RH (hRH : RiemannHypothesis) : ZeroSymmetry := by
  intro ρ hρ
  have hc : conj ρ ∈ NontrivialZeros := conj_mem_nontrivialZeros hρ
  have hre : ρ.re = 1 / 2 := sigmaFinite_re_eq_half hRH hρ
  have h1 : 1 - conj ρ = ρ := by
    apply Complex.ext
    · simp [hre]; norm_num
    · simp
  refine ⟨⟨hc, zetaMult_conj hρ⟩, ?_, ?_⟩
  · rw [h1]; exact hρ
  · rw [h1]

/-! ## The second contour shift, across the zeros -/

/-- **The explicit formula** (RH, (RiemannVonMangoldt), (LogDerivZetaLocal)): `hL(t) = -∑_ρ a_ρ t^{-ρ} + R(t)`, `|R(t)| ≤ C t^{-2/5}`,
for all `t > 0`. -/
theorem hL_explicit (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖(hL t : ℂ) + zeroSum t‖ ≤ C * t ^ (-(2 / 5 : ℝ)) := by
  obtain ⟨C, hC⟩ := norm_verticalIntegral'_kernelL_two_fifths_le
  refine ⟨C, fun t ht => ?_⟩
  have h1 := FL_eq_verticalIntegral' (c := 2) (by norm_num) ht
  have h2 := verticalIntegral'_kernelL_shift hRH (b := 3 / 4) (c := 2) (by norm_num) (by norm_num)
    (by norm_num) ht
  have h3 := verticalIntegral'_kernelL_zero_shift hRH hRvM hLD ht
  have heq : (hL t : ℂ) + zeroSum t = VerticalIntegral' (kernelL t) (2 / 5) := by
    simp only [hL]
    push_cast
    rw [h1, h2, h3]
    ring
  rw [heq]
  exact hC t ht

end GoldbachBoundaries.Phi2Proof
