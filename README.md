# Lean formalization: natural boundaries of Φ₂ and Φ_r under H∞

Louis P. Slothouber
lpslot@me.com

Lean 4 code for the paper

> Louis P. Slothouber, *The Egami–Matsumoto conjecture: a natural boundary of the Goldbach generating series*, preprint, Hexagon, hexagon:2611.00834, 2026.
>
> Version 1 on Hexagon carried the title *The Egami–Matsumoto conjecture under the Riemann Hypothesis alone: a natural boundary of the Goldbach generating series*. Version 2 adds the unconditional consequence of Alpöge's Lean proof of RH, as certified by the Lean and Mathlib communities; that step is a written argument and is not part of this formalization.

Release `v1.2` contains the H∞ development of Theorems A and C and the retained RH development of Corollary B in one Lake
project. Import `Phi2NB` to use both. Plain `lake build` builds the single default target `Phi2NB`.

## What it proves

Let Φ₂(s) = Σ_{m,n ≥ 1} Λ(m)Λ(n)(m+n)^(-s), which converges absolutely for Re s > 2. Assume H∞: for every δ > 0,
only finitely many non-trivial zeros ρ = β + iγ of ζ have β > 1/2 + δ. Then Φ₂ continues meromorphically to
Re s > 1, and Re s = 1 is its natural boundary. For every integer r ≥ 2, the corresponding ordered r-fold series
Φ_r continues meromorphically to Re s > r − 1, and Re s = r − 1 is its natural boundary.

Under H∞ the formal development also proves the real point 2B of Φ₂ (B = sup of the real parts of the zeros, when a zero
lies off the line): it is a simple pole with residue ν(2B)/Γ(2B) > 0, where ν(2B) = Σ_{β = B} m(ρ)²|Γ(ρ)|². It also
proves that RH holds if and only if Φ₂ has no pole in the real interval (1, 2). This is Theorem C of the paper.

The formal theorems are implications. Their hypotheses are H∞ and five classical inputs about the zeros of ζ
and the Gamma function. Each input is a proposition about Mathlib's functions and is taken as a hypothesis;
none is proved here as an unconditional theorem. What Lean checks is that these hypotheses imply the results.
RH is not a premise of any H∞ theorem; in Theorem C(ii) it is one side of an equivalence. The classical inputs, their sources and the precise difference from the
paper's input list are given below.

The RH results of release `v1.1` remain available with the same public theorem statements. They give the exact
simple poles and residues, the natural boundaries of Φ₂ and Φ_r, the reduction to Φ₂ and the radial limits.
The RH proofs use their original route. The derivation of Corollary B from the H∞ machinery in the paper's
Section 8.1 is not formalized in that form.

## The theorems

The main theorems are `GoldbachBoundaries.Phi2HInf.phi2_hinf_natural_boundary` and
`GoldbachBoundaries.Phi2HInf.phiR_hinf_natural_boundary`, in `Phi2NB/Phi2HInf/Statements.lean`. Each asserts the
existence of a meromorphic continuation equal to the series on its half-plane of absolute convergence, and
that every meromorphic continuation agreeing with the series outside a set with no accumulation point there
has the claimed natural boundary. The H∞ existence clauses assert no pole or residue catalogue.

The corollaries `Phi2HInf.phi2_hinf_natural_boundary_classical` and
`Phi2HInf.phiR_hinf_natural_boundary_classical`, in `Phi2NB/Phi2HInf/Classical.lean`, state the classical form.
For a continuation F, no function meromorphic on a disc centred on the boundary line agrees with F at every
point of the half-disc at which F is analytic. Appendix A of the paper does not print these two statements or the retained `phi2_natural_boundary_classical`; the paper's Section 10 states them in prose and refers to this README, which lists them below.
All names in this README have the prefix `GoldbachBoundaries` unless stated otherwise.

The pole at 2B and the RH criterion (Theorem C) are in `Phi2NB/Phi2HInf/PoleTwoBsup.lean`, namespace
`GoldbachBoundaries.Phi2HInf`. `phi2_hinf_pole_twoBsup` states, for the continuation `Phi2cHInf` given by the
right side of the regularized identity and a zero off the line: 1/2 < B < 1, the set of zeros with β = B is finite and
non-empty, the formula for ν(2B) and its positivity, the residue ν(2B)/Γ(2B) and its positivity, order exactly −1, and
that `Phi2cHInf` is not analytic at 2B. `phi2_hinf_pole_twoBsup_of_continuation` gives the residue and the order for every
function meromorphic on Re s > 1 that agrees with Φ₂ on Re s > 2 outside a set without accumulation point there.
`phi2_hinf_rh_iff_no_real_pole_of_continuation` is the equivalence of `RiemannHypothesis` with the absence of a pole
(order ≥ 0) at every real x in (1, 2), for every such function. The three theorems take the premise `ZetaNoZeroIoo`,
which says ζ(σ) ≠ 0 for 0 < σ < 1. It is not a hypothesis of the development: `zetaNoZeroIoo` proves it from the library's
`riemannZeta_ne_zero_of_mem_Ioo` (`Phi2NB/ZetaRealNonvanishing.lean`). The companions `phi2_hinf_pole_twoBsup'` and
`phi2_hinf_rh_iff_no_real_pole'`, stated for `Phi2cHInf`, omit it; `phi2_hinf_rh_iff_no_real_pole` is the same
equivalence for `Phi2cHInf` with the premise. All take `Hinf`, `Z1`, `Z2`, `Z3` and `StirlingStrip`;
`ZLittlewood` is not used. Only 2B is proved to be a pole; the statements say nothing about other real points of (1, 2).

The retained RH main theorems are `phi2_natural_boundary`, in `Phi2NB/Phi2/Statement.lean`, and
`phiR_natural_boundary`, in `Phi2NB/PhiR/Statement.lean`. For Φ₂ the poles are 2 and 1 + ρ, with residues 1 and
−2m(ρ)/ρ. For Φ_r they are r and r − 1 + ρ, with residues 1/(r − 1)! and
−r m(ρ) Γ(ρ)/Γ(r − 1 + ρ). The theorems assert that these are simple poles with nonzero residues.
Their `_classical` corollaries exclude agreement at every point of the half-disc. That formulation is weaker
than the new H∞ classical form; the retained codiscrete RH boundary clauses also exclude agreement only at
analytic points, as Section 10 of the paper explains.

The continuation results `Phi2Proof.phi2_continuation` and `PhiRProof.phiR_continuation` use RH alone, as do
`phiR_reduction` for r ≥ 3 and `phiR_singular_iff`. The radial limits `Phi2Proof.tendsto_eta_Hphi2`,
`PhiRProof.tendsto_eta_Phi2c` and `phiR_radial_limit` use RH, the local zero count and the local logarithmic-derivative
expansion. The latter two require τ ≠ 0. `phiR_natural_boundary_two` derives r = 2 directly from the retained
Φ₂ theorem.

## The premises

Write N(t) = Σ_{0 < γ ≤ t} m(ρ), over distinct non-trivial zeros with multiplicity m(ρ).
Titchmarsh below means *The Theory of the Riemann Zeta-Function*, second edition, revised by D. R. Heath-Brown,
Oxford University Press, 1986. These are the sources cited in Section 2 of the paper, in its Table 2 (Section 10) and in Appendix A.

The H∞ theorems of Theorem A take the following premises; Theorem C uses the same list without `ZLittlewood`.
The first five names are in `Paper2`; `StirlingStrip` is in `Phi2HInf`.

| Lean premise | Classical statement | Source |
|---|---|---|
| `Hinf` | For every δ > 0, the set of zeros with β > 1/2 + δ is finite. | The hypothesis H∞ of the paper, Section 1.2; it follows from RH (`Paper2.hinf_of_RH`), and here it is taken as a hypothesis. Its definition is retained in `Phi2NB/Paper2/Defs.lean`. |
| `Z1` | If ρ is a non-trivial zero, then its conjugate and 1 − its conjugate are zeros with the same multiplicity. | Conjugation and the functional equation, Titchmarsh (2.1.1), p. 13; the multiplicity argument is given in Section 2 of the paper. |
| `Z2` | N(t) = (t/(2π)) log(t/(2π)) − t/(2π) + O(log t) as t tends to infinity, and N(t+1) − N(t) ≤ C₁ log(t+3) for every t ≥ 0. | Titchmarsh Theorem 9.4, p. 214, for the asymptotic, and Theorem 9.2, p. 211, for the local count. |
| `Z3` | Uniformly for −1 ≤ Re z ≤ 2, \|Im z\| ≥ 2 and ζ(z) ≠ 0, the norm of ζ′(z)/ζ(z) − Σ_{\|γ−Im z\|≤1} m(ρ)/(z−ρ) is at most C log\|Im z\|. | Titchmarsh Theorem 9.6(A), p. 217. Section 2 extends the large-height statement to \|Im z\| ≥ 2. |
| `ZLittlewood` | For all sufficiently large t, some non-trivial zero has \|γ−t\| < a/(log log log t). | Littlewood, *Two notes on the Riemann zeta-function*, 1924; Titchmarsh Theorem 9.12, p. 224. |
| `StirlingStrip` | For each real x₁ ≤ x₂ there are C ≥ 0 and T₀ such that \|Γ(z)−exp S(z)\| ≤ C/\|Im z\| · \|exp S(z)\| whenever x₁ ≤ Re z ≤ x₂ and \|Im z\| ≥ T₀, where S(z) = (z−1/2) Log z − z + (1/2) Log(2π) and Log z is principal. | NIST DLMF §5.11(i), the multiplicative form 5.11.3: Γ(z) = e^(−z) z^z (2π/z)^(1/2) Γ*(z) with Γ*(z) = 1 + O(1/z) uniformly in \|arg z\| ≤ π − δ. Section 2 of the paper derives this premise (its (G4)) from that form: with principal powers the prefactor equals exp S(z), and the part of the strip with \|Im z\| ≥ T₀ lies in such a sector. |

The Theorem C statements add `ZetaNoZeroIoo` (ζ(σ) ≠ 0 for 0 < σ < 1), defined and proved as `zetaNoZeroIoo` in
`Phi2NB/Phi2HInf/ZetaNoZeroIoo.lean`. It is not an unconditional input: Lean proves it from
`riemannZeta_ne_zero_of_mem_Ioo`, and three of the statements list it as a premise only to show where it is used.

`Z1`, `Z2`, `Z3` and `ZLittlewood` are extracted in `Phi2NB/HInfSupport/Paper2/Defs.lean`;
`StirlingStrip` is in `Phi2NB/Phi2HInf/Defs.lean`. The formal numbering differs from the paper's numbering.
The paper's (Z1) is the local-count conjunct of Lean's `Z2`; the paper's (Z2) is `ZLittlewood`; (Z3) is `Z3`;
and (G4) is `StirlingStrip`. Lean also assumes the symmetries and the asymptotic for N(t). The proofs do not use
the asymptotic conjunct, but v1.2 retains it to preserve the H∞ statements exactly. No `Z4`, `Z5`, `Z6`, `Z7` or
hypothesis on additive relations between ordinates is a premise of the main theorems.

The RH theorems retain Mathlib's `RiemannHypothesis`, defined in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`,
which says that every non-trivial zero has real part 1/2,
and these three premises in `Phi2NB/Paper2/Defs.lean`:

| Lean premise | Classical statement | Source |
|---|---|---|
| `RiemannVonMangoldt` | N(t+1) − N(t) ≤ C₁ log(t+3) for all t ≥ 0. The asymptotic for N(t) is not included. | Titchmarsh Theorem 9.2, p. 211. |
| `LogDerivZetaLocal` | The same uniform local expansion of ζ′/ζ as `Z3` above. | Titchmarsh Theorem 9.6(A), p. 217. |
| `LittlewoodGap` | The same bound on gaps between ordinates as `ZLittlewood` above. | Titchmarsh Theorem 9.12, p. 224; Littlewood, 1924. |

`ZeroSymmetry`, defined in the same file, has the same body as `Z1`. The RH development proves it from RH as
`Phi2Proof.zeroSymmetry_of_RH`. The bridges in `Phi2NB/Phi2HInf/PremiseCorrespondence.lean` check these definitional
identities and the projection from `Z2` to `RiemannVonMangoldt`. They also check that the full `Z2` agrees with
the stronger counting premise already recorded in v1.1's `PhiRSource` namespace.

## Extraction and release history

The library keeps the namespace `GoldbachBoundaries` and its sub-namespaces from the in-repo development.
The v1.2 extraction follows the four H∞ theorems of Theorem A and the declarations of Theorem C (the pole at 2B and
the RH criterion, listed below) through their types, proof terms and source references, sharing the existing v1.1
declarations. It adds the needed H∞ proofs and their supporting declarations under
`Phi2NB/Phi2HInf/` and `Phi2NB/HInfSupport/`. Source helpers that clash with v1.1 because they take full `Z2`
have the suffix `_fullZ2`. The eight renamed helpers and all extracted declarations are recorded in
`release-tools/extraction.json`; no v1.1 public theorem is renamed or restated.

`STATEMENT-DIFF.md` gives every public main statement beside its v1.1 and in-repo counterparts, including the
four H∞ statements and the seven statements of Theorem C that are new in v1.2. All v1.1 statements and all H∞
statements are byte-identical to their respective inputs. Only imports, extraction comments and the eight internal helper names change in the H∞ extraction.
The comment on the pre-existing `Hinf` definition now describes its use in v1.2. The unextracted in-repo tree
still defines the same names independently and must not be imported alongside this library.

The H∞ addition, including its extracted support, the premise bridges and the files of Theorem C, has 69 Lean files
(5,711 lines): 47 files (4,617 lines) under `Phi2NB/Phi2HInf/` and 22 files (1,094 lines) under `Phi2NB/HInfSupport/`.
The whole library has 170 Lean files (15,732 lines), counting `Phi2NB.lean` and every Lean file under `Phi2NB/`.
Including the three axiom-check scripts, there are 173 Lean files (15,833 lines). These are physical line counts,
including comments and blank lines; dependencies, build products and extraction tools are excluded.
`SourceAudit.out` records the counts and the checks of pins, preserved v1.1 modules and import coverage.

* `v1.0`: the RH development for Φ₂, extracted from the larger library.
* `v1.1`: adds the RH extension to Φ_r, including its poles, residues, reduction, pointwise transfer and radial limit.
* `v1.2`: adds Φ₂ and Φ_r under H∞ and both classical-form corollaries, the real pole at 2B and the RH criterion for Φ₂ under H∞ (Theorem C), and makes the whole release one default build target. The RH public statements are retained.

## Versions

* Lean 4.34.0 (`lean-toolchain`)
* Mathlib, tag v4.34.0, commit `5ed2965256430c3649e86755f9576b54eca72435`
* PrimeNumberTheoremAnd, commit `c39a751132c88b6e8080b74c74023fd95b3d8be0`

`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` are byte-identical to v1.1. The manifest pins every
dependency to an exact commit. Mathlib and PrimeNumberTheoremAnd are the mathematical dependencies.

## Build and check

With elan installed, from this folder:

    lake exe cache get
    lake build
    lake env lean CheckAxioms.lean
    lake env lean CheckPhiRAxioms.lean
    lake env lean CheckPoleAxioms.lean

`lake build` builds the single default target `Phi2NB`, including both RH and H∞ and the premise bridges.
No separate PhiR or H∞ target is needed. For a clean rebuild of the release sources, remove `.lake/build`
before `lake build`; the dependency cache remains available.

The complete release was checked on 2026-11-20 on macOS, Apple silicon, with `lake clean`,
`lake exe cache get`, then plain `lake build`. All three commands exited successfully. The build ended with

    Build completed successfully (9179 jobs).

The `lake build` step took 80.6 minutes. [BuildV12Clean.out](BuildV12Clean.out) is the full output;
[BuildV12Clean.tail.out](BuildV12Clean.tail.out) contains its final 35 lines. `CleanV12.out`, `CacheGet.out` and
`release-tools/build-record.json` record the clean/cache steps, exit codes and times. `Toolchain.out` records the
compiler version. Lake used its default scheduling; the job count above is Lake's total, not a CPU count.

The cache command restored the matching local Mathlib cache, with no downloads in the final run.
PrimeNumberTheoremAnd and all release modules then compiled from source after `lake clean`; no compiled artifacts from either input library were used.

## Correspondence with the paper

These rows follow Appendix A of *The Egami–Matsumoto conjecture under the Riemann Hypothesis alone: a natural boundary of the Goldbach generating series*.
H = `Hinf`, Sym = `Z1`, Count = `Z2`, Local = `Z3`, Gap = `ZLittlewood`, Stir = `StirlingStrip`.
RvM, LDL and LG denote the three retained RH premises listed above. The declarations have the prefix
`GoldbachBoundaries`.

| Paper statement | Lean declaration | Lean assumes / scope |
|---|---|---|
| Theorem A(i), A(ii) | `Phi2HInf.phi2_hinf_natural_boundary` | H, Sym, Count, Local, Gap, Stir; existence of a continuation and boundary for every continuation agreeing codiscretely with Φ₂. |
| Theorem A(ii), classical form | `Phi2HInf.phi2_hinf_natural_boundary_classical` | Same premises, and a meromorphic continuation equal to Φ₂ on Re s > 2; agreement on the disc is tested at analytic points of F. |
| Theorem A(iii) | `Phi2HInf.phiR_hinf_natural_boundary` | Same premises, r ≥ 2; continuation to Re s > r − 1 and boundary there. |
| Theorem A(iii), boundary in the sense of A(ii) | `Phi2HInf.phiR_hinf_natural_boundary_classical` | Same premises and r ≥ 2; analytic-point agreement on the half-disc. |
| Theorem C(i), the pole at 2B | `Phi2HInf.phi2_hinf_pole_twoBsup` | Hinf, Sym, Count, Local, Stir, `ZetaNoZeroIoo` (proved as `Phi2HInf.zetaNoZeroIoo`), and a zero off the line; for `Phi2cHInf`. The primed `Phi2HInf.phi2_hinf_pole_twoBsup'` omits `ZetaNoZeroIoo`. |
| Theorem C(i), every continuation | `Phi2HInf.phi2_hinf_pole_twoBsup_of_continuation` | Same premises as the previous row, including the zero off the line; residue ν(2B)/Γ(2B) and order −1 at 2B for every meromorphic F on Re s > 1 agreeing with Φ₂ outside a set without accumulation point in Re s > 2. |
| Theorem C(ii), RH criterion | `Phi2HInf.phi2_hinf_rh_iff_no_real_pole_of_continuation` | Hinf, Sym, Count, Local, Stir, `ZetaNoZeroIoo`; `RiemannHypothesis` iff 0 ≤ order of F at every real x in (1, 2), for every such F. `phi2_hinf_rh_iff_no_real_pole` and the primed `phi2_hinf_rh_iff_no_real_pole'` state it for `Phi2cHInf`. |
| Corollary B(i), B(ii) | `phi2_natural_boundary` | RH, RvM, LDL, LG; the first conjunct includes the exact simple poles and residues. The codiscrete boundary clause gives B(ii). |
| Corollary B(ii), weaker classical form retained from v1.1 | `phi2_natural_boundary_classical` | RH, RvM, LDL, LG; excludes agreement at every point of the half-disc. |
| Corollary B(iii) | `Phi2Proof.tendsto_eta_Hphi2` | RH, RvM, LDL; every real τ, including 0. `Hphi2` is the holomorphic remainder, with limit `pairAtom τ / Gamma (1 + τ * I)`. |
| Corollary B(iv), continuation and boundary | `phiR_natural_boundary` | RH, RvM, LDL, LG, r ≥ 2; the first conjunct includes the exact simple poles and residues. |
| Corollary B(iv), radial limit | `phiR_radial_limit` | RH, RvM, LDL, r ≥ 2, τ ≠ 0; stated for the constructed continuation `PhiRProof.PhiRc r`. |

The retained `phiR_natural_boundary_classical`, `phiR_natural_boundary_two`, `phiR_reduction` and
`phiR_singular_iff` are additional v1.1 public results; their exact statements are in `STATEMENT-DIFF.md`.
The continuation lemmas and the Φ₂ radial limit for τ ≠ 0 are recorded there too.

Appendix A's definitions use the same meanings in the combined release:

| Paper notation | Lean definition |
|---|---|
| Non-trivial zeros, m(ρ), N(t) | `NontrivialZeros`, `zetaMult`, `Paper2.Nzero` |
| Φ₂, Φ_r | `Phi2`, `PhiR r`; ordered tuples, with von Mangoldt weights |
| Re s > a, Re s = a | `halfPlane a`, `lineAt a`; `HH` and `lineOne` are the cases a = 1 |
| No local meromorphic extension; natural boundary | `NoMeromorphicExtensionAt`, `IsNaturalBoundary`; agreement outside a set with no accumulation point in the open overlap |
| RH pole sets and residues | `phi2Poles`, `HasPhi2Residues`, `phiRPoles`, `HasPhiRResidues`, `HasResidue` |
| H and μ{τ} in Corollary B(iii) | `Phi2Proof.Hphi2`, `Phi2Proof.pairAtom τ` |
| The RH continuation of Φ_r | `PhiRProof.PhiRc r` |

What Section 10 of the paper lists as not formalized remains outside this release: the expository prose of Sections 1.1 to 1.4
(for instance the bound G₂(N) ≤ N log² N and the outline of the proof), the comments after the statements in Section 1.2,
the section openers and unnumbered remarks of Sections 3 to 7, the three remarks of Section 8.3 with their numerical values
(the radial coefficient and the bound for μ{0}, the kernel bound T₃ of Bhowmik and Schlage-Puchta, the thresholds), and all
of Section 9. The release does not formalize the remarks on notation in Section 2 either.
The passage from Titchmarsh's statements to the exact local-count and local-expansion forms is checked by hand
in Section 2. The kernel checks the stated implications; whether the definitions express the paper's meaning
is a matter of reading them.

## Intermediate results by paper section

The paper's Section 10 and Appendix A state the main theorems only. The intermediate results of its Sections 3 to 7 and of
Section 8.2 (Theorem C) have formal counterparts in the H∞ development; they are listed here by section, with the file that
contains each. All names have the prefix `GoldbachBoundaries.Phi2HInf.`. Suitable constants are existential where the paper
names them. The residue theorem `hasResidue_Phi2cHInf` is stated on the strip 1 < Re s < 2 − B, as in the paper; `hasResidue_Phi2cHInf_of_not_mem_phi2Poles` is the wider
statement for every point of Re s > 1 that is neither 2 nor 1 + ρ, and is what Theorem C uses at 2B.

**Section 3 (the decomposition)**

| Group | Declarations (prefix `GoldbachBoundaries.Phi2HInf.`) | File |
|---|---|---|
| Explicit formula (3.3) | `hL_explicit_hinf`, `norm_V_le` | `Phi2NB/Phi2HInf/Proof/M1Regularization.lean` |
| Regularized identity (3.4) | `phi2_reg_identity`, `differentiableOn_A` | `Phi2NB/Phi2HInf/Proof/M1Regularization.lean` |
|  | `meromorphicOn_M0` | `Phi2NB/Phi2HInf/Fill/meromorphicOn_M0.lean` |

**Section 4 (continuation under H∞)**

| Group | Declarations (prefix `GoldbachBoundaries.Phi2HInf.`) | File |
|---|---|---|
| Local finiteness and residues | `locallyFinite_pairCat`, `pairCat_denominator_bound` | `Phi2NB/Phi2HInf/Fill/pairCat_geometry.lean` |
|  | `hasResidue_C` | `Phi2NB/Phi2HInf/Fill/hasResidue_C.lean` |
|  | `hasResidue_Phi2cHInf` | `Phi2NB/Phi2HInf/Proof/M2Catalogue.lean` |

**Section 5 (non-cancellation: the phase cone)**

| Group | Declarations (prefix `GoldbachBoundaries.Phi2HInf.`) | File |
|---|---|---|
| Weights and cone (5.1) | `norm_bKer_asymp` | `Phi2NB/Phi2HInf/Fill/norm_bKer_asymp.lean` |
|  | `bKer_cone_hinf` | `Phi2NB/Phi2HInf/Fill/bKer_cone_hinf.lean` |
|  | `norm_bKer_ratio_le` | `Phi2NB/Phi2HInf/Fill/norm_bKer_ratio_le.lean` |
| Abstract theorem (5.2) | `sum_bKer_ne_zero_hinf` | `Phi2NB/Phi2HInf/Fill/sum_bKer_ne_zero_hinf.lean` |
| Non-cancellation on the zero side (5.3) | `pair_family_ne_zero_of_large` | `Phi2NB/Phi2HInf/Fill/collision_family.lean` |
|  | `collisionAtom_ne_zero_of_large` | `Phi2NB/Phi2HInf/Proof/M3Cone.lean` |

**Section 6 (the natural boundary)**

| Group | Declarations (prefix `GoldbachBoundaries.Phi2HInf.`) | File |
|---|---|---|
| Infinitely many zeros off the line (6.1) | `exists_interior_poles_accum`, `boundary_infinite_case` | `Phi2NB/Phi2HInf/Proof/M5Boundary.lean` |
| Finitely many zeros off the line (6.2) | `critical_decomposition` | `Phi2NB/Phi2HInf/Fill/critical_decomposition.lean` |
|  | `tendsto_eta_criticalC` | `Phi2NB/Phi2HInf/Fill/tendsto_eta_criticalC.lean` |
|  | `exists_tau_criticalAtom_ne_zero`, `criticalC_natural_boundary` | `Phi2NB/Phi2HInf/Fill/critical_boundary.lean` |
|  | `boundary_finite_case` | `Phi2NB/Phi2HInf/Proof/M5Boundary.lean` |

**Section 7 (sums of more than two prime powers)**

| Group | Declarations (prefix `GoldbachBoundaries.Phi2HInf.`) | File |
|---|---|---|
| The cutoff and the reduction to Φ₂ | `norm_E_le`, `norm_g_le` | `Phi2NB/Phi2HInf/Fill/r_cutoff.lean` |
|  | `Gb_eq_integral`, `mellin_Pr` | `Phi2NB/Phi2HInf/Fill/r_finite_mellin.lean` |
|  | `differentiableOn_Hr` | `Phi2NB/Phi2HInf/Fill/r_remainder.lean` |
|  | `phiR_reg_identity` | `Phi2NB/Phi2HInf/Fill/r_identity.lean` |
|  | `phiR_hinf_boundary` | `Phi2NB/Phi2HInf/Fill/r_boundary.lean` |

**Theorem C (Section 8.2) and Proposition 4.2(c)**

| Group | Declarations (prefix `GoldbachBoundaries.Phi2HInf.`) | File |
|---|---|---|
| Residue off the poles of M₀ | `analyticAt_M0_of_not_mem_phi2Poles`, `hasResidue_Phi2cHInf_of_not_mem_phi2Poles` | `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean` |
| ζ does not vanish on (0, 1) | `ZetaNoZeroIoo`, `zetaNoZeroIoo` | `Phi2NB/Phi2HInf/ZetaNoZeroIoo.lean` |
|  | `ofReal_not_mem_phi2Poles` | `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean` |
| B is attained | `exists_rightZero_of_offLine`, `Bsup_attained_of_offLine` | `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean` |
| The coefficient at 2B | `collision_twoBsup_iff`, `collisionTwoBsupEquiv`, `zeroCoef_mul_zeroCoef_conj`, `collisionAtom_twoBsup`, `collisionAtom_twoBsup_pos` | `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean` |
| The pole at 2B | `hasResidue_Phi2cHInf_twoBsup`, `not_analyticAt_Phi2cHInf_twoBsup` | `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean` |
| From RH to the absence of real poles | `analyticAt_cauchy_of_gap`, `analyticAt_C_of_not_pairSum`, `analyticAt_Phi2cHInf_of_not_pole`, `exists_trivial_of_riemannZeta_eq_zero_of_re_nonpos`, `riemannHypothesis_iff_nontrivialZeros`, `analyticAt_Phi2cHInf_real_of_RH`, `riemannHypothesis_iff_analyticAt_Phi2cHInf_real` | `Phi2NB/Phi2HInf/Fill/pole_twoBsup_rh.lean` |
| Main statements | `phi2_hinf_pole_twoBsup`, `phi2_hinf_pole_twoBsup'`, `phi2_hinf_pole_twoBsup_of_continuation`, `phi2_hinf_rh_iff_no_real_pole`, `phi2_hinf_rh_iff_no_real_pole'`, `phi2_hinf_rh_iff_no_real_pole_of_continuation` | `Phi2NB/Phi2HInf/PoleTwoBsup.lean` |

The files `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean`, `Phi2NB/Phi2HInf/Fill/pole_twoBsup_rh.lean`,
`Phi2NB/Phi2HInf/ZetaNoZeroIoo.lean` and `Phi2NB/Phi2HInf/PoleTwoBsup.lean` are the files of Theorem C.

## Declarations named in the paper but not printed in Appendix A

Section 10 and Appendix A of the paper name these declarations without printing them. Each is listed here with its file.
All names have the prefix `GoldbachBoundaries.` plus the namespace shown.

| Declaration | Namespace | File |
|---|---|---|
| `phi2_hinf_natural_boundary_classical`, `phiR_hinf_natural_boundary_classical` | `Phi2HInf` | `Phi2NB/Phi2HInf/Classical.lean` |
| `phi2_natural_boundary_classical` | (none) | `Phi2NB/Phi2/Statement.lean` |
| `phiR_natural_boundary_classical` (retained from v1.1; not named in the paper) | (none) | `Phi2NB/PhiR/Statement.lean` |
| `ZetaNoZeroIoo` (the premise) and `zetaNoZeroIoo` (its proof) | `Phi2HInf` | `Phi2NB/Phi2HInf/ZetaNoZeroIoo.lean` |
| `riemannZeta_ne_zero_of_mem_Ioo` (the proof of `zetaNoZeroIoo` rests on it) | (none) | `Phi2NB/ZetaRealNonvanishing.lean` |
| `phi2Poles`, `HasPhi2Residues` | (none) | `Phi2NB/Phi2/Defs.lean` |
| `phiRPoles`, `HasPhiRResidues` | (none) | `Phi2NB/PhiR/Defs.lean` |
| `Hphi2`, `pairAtom` | `Phi2Proof` | `Phi2NB/Phi2/Proof/Defs.lean` |
| `PhiRc` | `PhiRProof` | `Phi2NB/PhiR/Proof/Defs.lean` |
| `Phi2cHInf` | `Phi2HInf` | `Phi2NB/Phi2HInf/Proof/Defs.lean` |
| `HasResidue.meromorphicOrderAt_eq_neg_one` (a simple pole has order −1) | (none) | `Phi2NB/ResidueAPI.lean` |

The two forms of the formal residue theorem behind Proposition 4.2(c) are `hasResidue_Phi2cHInf` (strip 1 < Re s < 2 − B,
Section 4 above) and `hasResidue_Phi2cHInf_of_not_mem_phi2Poles` (every point of Re s > 1 other than 2 and 1 + ρ, in the Theorem C table).

## Axioms

`CheckAxioms.lean` imports the complete `Phi2NB` library and prints the axioms and types of 16 results: the four
H∞ theorems and 12 retained results, including every main theorem in Appendix A. `CheckPoleAxioms.lean` does the same
for the 26 declarations of Theorem C (the pole at 2B and the RH criterion) that are listed in the section on intermediate
results, among them its six main statements `phi2_hinf_pole_twoBsup`, `phi2_hinf_pole_twoBsup'`,
`phi2_hinf_pole_twoBsup_of_continuation`, `phi2_hinf_rh_iff_no_real_pole`, `phi2_hinf_rh_iff_no_real_pole'` and
`phi2_hinf_rh_iff_no_real_pole_of_continuation`. Every axiom list is exactly

    [propext, Classical.choice, Quot.sound]

The captured outputs are [CheckAxioms.out](CheckAxioms.out) and [CheckPoleAxioms.out](CheckPoleAxioms.out). The original `CheckPhiRAxioms.lean` also gives those
same three axioms for each of its six results; its fresh output is [CheckPhiRAxioms.out](CheckPhiRAxioms.out).
`AxiomAudit.out` records the exact-list checks. `StatementAudit.out` records the statement comparison, and
`SourceAudit.out` records the source scan, definition comparisons, pins and file counts.

The release-owned Lean files contain no `sorry`, `axiom`, `admit`, `native_decide`, `implemented_by` or `extern`
construct. These are the three standard axioms of Lean's logic. The pinned PrimeNumberTheoremAnd dependency
prints two existing `declaration uses 'sorry'` warnings in `Wiener.lean`; the axiom outputs show that neither is
in the dependency closure of the audited results. The release's warnings are linter and deprecation notices.

The extraction and audit tools in `release-tools/` use the original read-only input paths recorded for this
build. They are not needed to build or use the library.

## License

Copyright 2026 Louis P. Slothouber. Licensed under the Apache License, Version 2.0; see LICENSE.
