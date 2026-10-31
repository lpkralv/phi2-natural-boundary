# Lean formalization: under RH, Re s = 1 is a natural boundary of Φ₂

Louis P. Slothouber

Lean 4 code for the paper

> Louis P. Slothouber, *The line Re s = 1 is a natural boundary of Σ Λ(m)Λ(n)(m+n)^(-s) under the Riemann
> Hypothesis*, preprint, 2026.

Release `v1.0` is the version described in the paper.

## What it proves

Let Φ₂(s) = Σ_{m,n ≥ 1} Λ(m)Λ(n)(m+n)^(-s), which converges absolutely for Re s > 2. Egami and Matsumoto proved
that under the Riemann Hypothesis Φ₂ continues meromorphically to Re s > 1, and conjectured that Re s = 1 is its
natural boundary. The paper proves the conjecture under the Riemann Hypothesis alone, and this library checks that
proof in Lean 4. The formal theorem is an implication. Its hypotheses are the Riemann Hypothesis, in Mathlib's
formulation `RiemannHypothesis`, and three classical theorems on the zeros of ζ from Titchmarsh, *The Theory of the
Riemann Zeta-Function*, Ch. IX (Theorems 9.2, 9.6(A) and 9.12), which Mathlib lacks. Each of the three is written
as a proposition about Mathlib's `riemannZeta` and its zeros and taken as a hypothesis, not as an axiom; none is
proved here. What Lean checks is that RH and these three imply the theorem. Everything else, from the facts about
Γ and the residues of ζ'/ζ to Mellin inversion and the residue theorem, is proved in the library or taken from
Mathlib and PrimeNumberTheoremAnd.

## The theorem

The main theorem is `GoldbachBoundaries.phi2_natural_boundary`, in `Phi2NB/Phi2/Statement.lean`. Assume the
Riemann Hypothesis and the three classical theorems. Then Φ₂ continues from Re s > 2 to a meromorphic function on
the half-plane Re s > 1, analytic except for a simple pole at 2 with residue 1 and a simple pole at 1 + ρ, for each
non-trivial zero ρ of ζ, with residue -2m(ρ)/ρ, where m(ρ) is the multiplicity of ρ; all these residues are
non-zero. And every function meromorphic on Re s > 1 that agrees with Φ₂ on Re s > 2, outside a set with no
accumulation point in Re s > 2, has the line Re s = 1 as a natural boundary: at no point of the line does it extend
meromorphically to a disc around that point.

The corollary `GoldbachBoundaries.phi2_natural_boundary_classical`, in the same file, states the boundary in the
classical form: for a meromorphic continuation F of Φ₂ to Re s > 1, no function meromorphic on a disc centred on
the line Re s = 1 coincides with F at every point of the disc with Re s > 1. By the identity theorem the two forms
are equivalent.

The three classical theorems are stated in `Phi2NB/Paper2/Defs.lean`:

* `RiemannVonMangoldt`: the local count of zeros, N(t+1) - N(t) ≤ C₁ log(t+3) for t ≥ 0 (Theorem 9.2);
* `LogDerivZetaLocal`: the local expansion of ζ'/ζ by the zeros with |γ - t| ≤ 1, for |t| ≥ 2 (Theorem 9.6(A));
* `LittlewoodGap`: Littlewood's bound on gaps between ordinates of zeros (Theorem 9.12).

The passage from Titchmarsh's statements to these forms is checked by hand in Section 2 of the paper. Whether the
formal definitions say what the prose says is a matter of reading them; Appendix A of the paper reproduces the
statements of the theorem and the corollary verbatim (docstrings and proofs omitted) and explains every name they
use.

The library has 76 Lean files (7,440 lines). Its declarations live in the namespace `GoldbachBoundaries`, kept from
the larger development the library was extracted from. The only dependencies are Mathlib and PrimeNumberTheoremAnd.

## Versions

* Lean 4.34.0 (`lean-toolchain`)
* Mathlib, tag v4.34.0
* PrimeNumberTheoremAnd, commit c39a751 (c39a751132c88b6e8080b74c74023fd95b3d8be0)

`lake-manifest.json` pins every dependency to an exact commit.

## Build and check

With elan installed (it reads `lean-toolchain` and fetches the right Lean), from this folder:

    lake exe cache get              # downloads the Mathlib build cache
    lake build                      # builds PrimeNumberTheoremAnd and Phi2NB
    lake env lean CheckAxioms.lean  # prints the axioms and the statement

`lake build` should end with `Build completed successfully`. The last command should print

    'GoldbachBoundaries.phi2_natural_boundary' depends on axioms: [propext, Classical.choice, Quot.sound]
    'GoldbachBoundaries.phi2_natural_boundary_classical' depends on axioms: [propext, Classical.choice, Quot.sound]

followed by the full types of the theorem and the corollary. These are the three standard axioms of Lean's logic;
no `sorry` and no other axiom is used. The library contains no `sorry`, `admit`, `native_decide` or `axiom`
declaration.

These steps were checked on a clean copy of this release (macOS, Apple silicon): `lake exe cache get` and
`lake build` together took about 25 minutes, almost all of it building PrimeNumberTheoremAnd; the build finished
with no errors. It prints some warnings. Those in `Phi2NB` are linter and deprecation notices (unused simp
arguments, `if_pos`/`if_neg` deprecated, `Try this` suggestions). Two are `declaration uses 'sorry'` in
PrimeNumberTheoremAnd's own `Wiener.lean`; nothing in this library depends on them, as the axiom check shows
(a dependence on `sorry` would add `sorryAx` to the list).

## Correspondence with the paper

Hypothesis abbreviations: RH = Mathlib's `RiemannHypothesis`; RvM = `RiemannVonMangoldt` (the paper's (Z1),
Titchmarsh 9.2); LDL = `LogDerivZetaLocal` ((Z3), Titchmarsh 9.6(A)); LG = `LittlewoodGap` ((Z2), Titchmarsh 9.12).
"Lean assumes" lists the hypotheses of the declaration. The threshold of Section 5 of the paper, X, is called `H` in
Lean. To find a declaration, search the sources for its name (for example `grep -rn "theorem hL_explicit" Phi2NB`).

### Classical inputs and unnumbered facts (paper Sections 2 and 3)

| Paper | Lean declaration(s) | Lean assumes | Note |
|---|---|---|---|
| (Z1) | premise `RiemannVonMangoldt` | — | the local count only; the asymptotic for N(t) is not part of the premise |
| (Z2) | premise `LittlewoodGap` | — | |
| (Z3) | premise `LogDerivZetaLocal` | — | stated for \|Im z\| ≥ 2, as in the paper |
| bound (5), ψ ≪ log\|Im z\| on Re z ≥ ½+ε | `norm_negLogDerivZeta_le_log` | RH | Lean proves it from RH alone (Borel–Carathéodory); the paper deduces it from (Z3) and (Z1) |
| (Z4) / Lemma 4.4 | `hL_explicit` | RH, RvM, LDL | Lean: ‖h+Z‖ ≤ C x^{−2/5} for all x > 0, contour along Re w = 2/5; paper: a = 0, contour along Re w = −½ |
| (Z5) ordinates unbounded | `exists_nontrivialZero_im_gt` | — | Lean: Hadamard product (PrimeNumberTheoremAnd); paper: from (Z2) |
| conjugate symmetry, multiplicity | `conj_mem_nontrivialZeros`, `zetaMult_conj` | — | |
| finitely many zeros up to height T | `finite_zeros_abs_im_le` | — | |
| (G2), (G3) | `norm_bKer`, `norm_Gamma_mul_one_add_abs_im_pow_le` | — | the paper's (G3) adds a ≤ a′ |
| residues of ψ | `hasResidue_negLogDerivZeta_one`, `hasResidue_negLogDerivZeta_of_mem_nontrivialZeros` | — | |
| definitions of Section 3 (F, h, the pieces of the decomposition, H, M) | `FL`, `hL`, `e1L`, `E2L`, `RrL`, `Hphi2`, `phi2Main`, `Phi2c`, `kernelL`; also `m1L` = ∫₀¹ h x^{z−1} | — | `m1L` has no name in the paper |
| (10) Mellin transforms, F ≥ 0, F ≤ Ce^{−x} | `mellin_FL'`, `mellin_FL_sq'`, `FL_nonneg'`, `FL_continuousOn_and_le_exp` | — | |
| (11) Mellin inversion | `FL_eq_verticalIntegral'` | — | integrability inside `FL_eq_verticalIntegral'_aux` |
| (6) a_ρ, Z | `zeroCoef`, `zeroSum` | — | |
| (15) 𝒞, J, P_τ, μ{τ} | `cauchyT`, `Kc`, `pairIdx`, `pairAtom` | — | |
| (17) b_τ | `bKer` | — | |
| (20) 𝒜_τ, q_τ | `Aidx`, `Aweight` | — | |

### Numbered results

| Paper | Lean declaration(s) | Lean assumes | Note |
|---|---|---|---|
| Theorem 1.1(i) | `phi2_continuation`; first conjunct of `phi2_natural_boundary` | RH (continuation); RH, RvM, LDL, LG (main theorem) | the continuation is `Phi2c` = M + H |
| Theorem 1.1(ii) | `phi2_natural_boundary_classical` applied to `Phi2c`; `phi2_boundary` | RH, RvM, LDL, LG | Lean also proves the codiscrete form for every meromorphic continuation |
| Lemma 3.1 (decomposition) | `Gamma_mul_negLogDerivZeta_split'`, `Gamma_mul_Phi2_split'`, `differentiable_e1L_E2L`, `phi2_identity` | — | integrability of h x^{z−1}: `integrableOn_Ioc_hL_mul_cpow`; of R: inside `Gamma_mul_Phi2_split'`; (14) is `Gamma_mul_negLogDerivZeta_split'` |
| Lemma 3.2 (first shift, h = O(x^{−b})) | `verticalIntegral'_kernelL_shift`, `norm_hL_le` | RH | integrability on both lines: `integrable_kernelL`; Lean uses `norm_negLogDerivZeta_le_log` where the paper uses (5) |
| Proposition 3.3 (continuation) | `differentiableOn_RrL`, `differentiableOn_Hphi2`, `meromorphicOn_phi2Main`, `analyticAt_negLogDerivZeta_sub_one`, `phi2_continuation` | RH | |
| Lemma 4.1 (counting) | `sum_zetaMult_window_le`, `zetaMult_le_log`, `summable_zeros_inv_sq`, with `zeroSymmetry_of_RH` | `ZeroSymmetry`, RvM (`ZeroSymmetry` from RH) | `ZeroSymmetry`: ρ̄ and 1−ρ̄ are zeros of the same multiplicity; the paper uses conjugate symmetry under its standing RH. In (b) the paper names the constant of (a); Lean has ∃C |
| Lemma 4.2 | `summable_norm_zeroCoef`, `summable_norm_pair`, `norm_zeroSum_le` | RH, RvM | the paper takes S = Σ\|a_ρ\|; Lean has ∃S ≥ 0 |
| Lemma 4.3 | `integral_zeroSum_sq` | RH, RvM | absolute convergence of 𝒞 inside the proof |
| Lemma 4.4 (explicit formula) | `hL_explicit` | RH, RvM, LDL | see (Z4) above; the identity with the integral on Re w = −½ is not a Lean statement |
| Lemma 4.5 (R = 𝒞 + J, J bounded) | `RrL_eq_cauchyT_add_Kc` (RH, RvM), `norm_Kc_le` (RH, RvM, LDL) | RH, RvM; RH, RvM, LDL | integrability of J inside the proof; Lean's bound goes through `hL_explicit`; `norm_verticalIntegral'_kernelL_two_fifths_le`, used there, has no hypotheses |
| Lemma 4.6 | `tendsto_eta_cauchyT` | RH, RvM | also gives summability of μ{τ} |
| Theorem 4.7 (radial limit) | `tendsto_eta_Hphi2` | RH, RvM, LDL | exact match |
| Lemma 5.1 | `norm_bKer`, `norm_bKer_le` | — | |
| Lemma 5.2 (phase cone) | `bKer_cone` | — | existential U in both; the paper's proof exhibits max(1, 64Y²) |
| Theorem 5.3 (abstract family) | `sum_bKer_ne_zero` | — | absolute convergence implied: a nonzero `tsum` is summable |
| Lemma 5.4 | `pairAtom_eq_two_tsum` | RH, RvM | absolute convergence inside the proof |
| Lemma 5.5 | `Aidx_bin_le` | RH, RvM | |
| Theorem 5.6 (non-cancellation) | `pairAtom_ne_zero_of_large`; conjugation step `pairAtom_neg` | RH, RvM; `pairAtom_neg` none | `pairAtom_neg` has no hypotheses: a non-summable series has `tsum` 0, and conj 0 = 0 |
| Lemma 6.1 (exceptional set finite) | `finite_exceptional` | — | no hypotheses in either |
| Lemma 6.2 (large pairs) | `exists_ordinate_in_interval`, `exists_large_pair` | LG; RH, LG | |
| Theorem 6.3 (density) | `exists_tau_pairAtom_ne_zero` | RH, RvM, LG | |
| Lemma 6.4 (line blow-up) | `noMeromorphicExtensionAt_of_line_blowup` | — (G differentiable on the half-plane Re s > 1) | Lean proves the codiscrete conclusion, which implies the classical one |
| Theorem 6.5 (boundary of H) | `Hphi2_natural_boundary` | RH, RvM, LDL, LG | codiscrete conclusion |
| Proof of Theorem 1.1(ii) | `isNaturalBoundary_of_eventuallyEq_add`, `eventuallyEq_nhdsNE_of_agree_halfPlane_two'`, `phi2_boundary`, `phi2_natural_boundary_classical` | RH, RvM, LDL, LG | the paper's two sentences are the case with an empty exceptional set |

### Not formalized

The uniqueness of the continuation (identity theorem, remark after Theorem 1.1); the remark after Theorem 1.1 on
poles for r ≤ ½; the passage from Titchmarsh's statements to the forms (Z1) and (Z3); the remark on same-sign
weights; the phase-drift heuristic of Section 5; the remarks of Section 7 (the comparison with Egami and Matsumoto,
the radial limit of Φ₂ itself at τ = 0 with the value μ{0} − 2 log 2π, thresholds). The proof uses none of them.

### Formalized only in weaker form

In the proof of Lemma 4.4: the bounded remainder (a = 0), the limit −log 2π and the bound B₀x^{1/2} on the line
integral, where the formal lemma has a = 2/5 (the argument needs only some a < ½). The named constant S = Σ|a_ρ| of
Lemma 4.2; formally some S exists. The shared constant C₂ of Lemma 4.1(a) and (b); formally each part has its own.
Absolute convergence of R(s) for Re s > 2 (Lemma 3.1), of J (Lemma 4.5) and of the series over 𝒜_τ (Lemma 5.4) is
established formally only inside the proofs that use it; for R, inside `Gamma_mul_Phi2_split'`. Note also that
`C_hsq_integrable` (`Phi2NB/Phi2/Fill/CCommon.lean`) needs RH.

## Axioms

`#print axioms` on `GoldbachBoundaries.phi2_natural_boundary` and on
`GoldbachBoundaries.phi2_natural_boundary_classical` gives `[propext, Classical.choice, Quot.sound]` for each; run
`lake env lean CheckAxioms.lean` to see it. The result is also recorded in the docstring of
`Phi2NB/Phi2/Statement.lean`.

## License

Copyright 2026 Louis P. Slothouber. Licensed under the Apache License, Version 2.0; see LICENSE.
