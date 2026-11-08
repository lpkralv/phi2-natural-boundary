import Phi2NB.PhiR.Proof.M2Continuation
import Phi2NB.PhiR.Fill.PhiR_eq_explicit
import Phi2NB.PhiR.Fill.exists_RR
import Phi2NB.PhiR.Fill.RR_bounded_halfStrip

/-!
# Step M4: the reduction identity (Proposition 7.2, identity (22)) in its classical form

From `Gamma_mul_PhiR_split` and `Γ(s - j) P_j(s) = Γ(s)`:
for `r ≥ 2` and `σ > r` (no RH),
`Φ_r(s) = A_r/(r-1)! · ζ(s-r+1) + r(r-2)/P_{r-1}(s) · (ζ'/ζ)(s-r+1) + C(r,2)/P_{r-2}(s) · Φ₂(s-r+2) + R_r(s)`,
`R_r = RRraw r`. Under RH `R_r` has a holomorphic version on `σ > r - 3/2` (the singularity at
`s = r` is removable: the residues `A_r/(r-1)!` of the two terms cancel), bounded on every half-strip
`σ ≥ a > r - 3/2`, `T ≤ t ≤ T + 1`.

Lemmas proved in `Fill/`: `PhiR_eq_explicit`, `exists_RR`, `RR_bounded_halfStrip`. Proved in this file: `Gamma_sub_mul_polyP`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- **`Γ(s - j) P_j(s) = Γ(s)`** for `Re s > j` (induction on `j` with `Γ(z + 1) = z Γ(z)`). -/
theorem Gamma_sub_mul_polyP (j : ℕ) {s : ℂ} (hs : (j : ℝ) < s.re) : Gamma (s - j) * polyP j s = Gamma s := by
  induction j with
  | zero => simp [polyP]
  | succ j ih =>
    have hs' : (j : ℝ) < s.re := by push_cast at hs; linarith
    have hne : s - ((j + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      push_cast at hs
      linarith
    have hΓ : Gamma (s - (j : ℂ)) = (s - ((j + 1 : ℕ) : ℂ)) * Gamma (s - ((j + 1 : ℕ) : ℂ)) := by
      have h := Complex.Gamma_add_one (s - ((j + 1 : ℕ) : ℂ)) hne
      rw [show s - ((j + 1 : ℕ) : ℂ) + 1 = s - (j : ℂ) by push_cast; ring] at h
      exact h
    rw [polyP, Finset.prod_Icc_succ_top (by omega), ← polyP]
    calc Gamma (s - ((j + 1 : ℕ) : ℂ)) * (polyP j s * (s - ((j + 1 : ℕ) : ℂ)))
        = Gamma (s - (j : ℂ)) * polyP j s := by rw [hΓ]; ring
      _ = Gamma s := ih hs'

/-- **Identity (22) of the paper on `σ > r`** (no RH): the classical form of `Gamma_mul_PhiR_split`.
Proof: divide `Gamma_mul_PhiR_split` by `Γ(s)`; `Γ(s-r+2)/Γ(s) = 1/P_{r-2}(s)` and `Γ(s-r+1)/Γ(s) = 1/P_{r-1}(s)`
(`Gamma_sub_mul_polyP` with `j = r - 2, r - 1`, `Nat.cast_sub`); `B_r ψ = r(r-2) ζ'/ζ` (`negLogDerivZeta`);
`C(r,2) = cC r` (`Nat.cast_choose_two`); and `A_r/(Γ(s)(s-r)) = A_r ζ(s-r+1)/(r-1)! + (the A_r-part of RRraw)` by the
definition of `RRraw`. `ring`/`field_simp` with `Γ(s) ≠ 0`, `P_j(s) ≠ 0`. -/
theorem PhiR_eq_explicit {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
      (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
        (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
      ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + RRraw r s :=
  FillC.PhiR_eq_explicit' hr hs

/-- **The remainder has a holomorphic version on `σ > r - 3/2`** (RH). `RRraw r` is holomorphic on
`σ > r - 3/2` off `s = r` (`differentiableOn_KR`; `1/Γ` entire; `ζ(s-r+1)` is differentiable off `s = r`,
`differentiableAt_riemannZeta`), and bounded near `r`: `1/(Γ(s)(s-r)) - 1/((r-1)!(s-r))` tends to `-Γ'(r)/Γ(r)²`
(derivative of `1/Γ`), and `ζ(w) - 1/(w-1)` tends to Euler's `γ` (`tendsto_riemannZeta_sub_one_div`). Removable
singularity: `FillC.exists_RR'` builds `R` explicitly, with `dslope` of `1/Γ` at `r` and of `zetaRes` at `1`. -/
theorem exists_RR (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      ∀ s ∈ halfPlane ((r : ℝ) - 3 / 2), s ≠ (r : ℂ) → R s = RRraw r s :=
  FillC.exists_RR' hRH hr

/-- **Half-strip bounds for the remainder** (the last clause of Proposition 7.2; no further RH use). For `a > r - 3/2` and real `T`,
`R` is bounded on `{σ ≥ a, T ≤ t ≤ T + 1}` (the bound may depend on `a`, `T`, `r`).
Proof (as in the proof of Proposition 7.2): fix `b = r + 2`. On `a ≤ σ ≤ b` the closed rectangle is compact and inside `σ > r - 3/2`, where `R`
is continuous (`IsCompact.exists_bound_of_continuousOn`). On `σ ≥ b`, `R s = RRraw r s` (`s ≠ r`) and by
`PhiR_eq_explicit` it is `Φ_r` minus three terms, each bounded by its value at `σ = b`: `|Φ_r(s)| ≤ ∑ |terms at b|`
(`mellin_FL_pow`'s summability), `|ζ(s-r+1)| ≤ ζ(3)`, `|ζ'/ζ(s-r+1)| ≤ ∑ Λ(n) n^{-3}`, `|Φ₂(s-r+2)| ≤ ∑ at 4`, and
`|1/P_j(s)| ≤ 1` (each factor has `|s - l| ≥ σ - l ≥ 1`). -/
theorem RR_bounded_halfStrip {r : ℕ} (hr : 2 ≤ r) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)))
    (hRR : ∀ s ∈ halfPlane ((r : ℝ) - 3 / 2), s ≠ (r : ℂ) → R s = RRraw r s) {a : ℝ}
    (ha : (r : ℝ) - 3 / 2 < a) (T : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M :=
  FillC.RR_bounded_halfStrip' hr hR hRR ha T

end GoldbachBoundaries.PhiRProof
