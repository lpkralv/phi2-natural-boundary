# Statement comparison for v1.2

All names below have the prefix `GoldbachBoundaries.`. Each block contains the source bytes from `theorem` through the type, with the proof and final `:=` omitted. Line breaks inside the statement are preserved. The comparison covers the public boundary theorems, their classical corollaries, and the continuation, reduction, transfer and radial-limit results named in the README.

The v1.1 reference is the published release source. The in-repo reference is `FableForward/riemann/A4-12-lean-boundaries/lean/GoldbachBoundaries/`. The comparison script fails if any v1.1 statement changes or any H∞ statement changes. The seven statements of the pole at 2B and the RH criterion (the last seven blocks) are new in v1.2 and have no v1.1 counterpart.

The four H∞ statements and their premise identifiers are unchanged. The H∞ premise `Z2` retains both the asymptotic and the local count. Shared definitions have the same bodies; `Hinf`, `Phi2`, `PhiR`, `HH`, `halfPlane`, `lineOne`, `lineAt` and the natural-boundary predicates use the release definitions. The extracted `Z1`, `Z3` and `ZLittlewood` have the source definition bodies. They are definitionally equal to `ZeroSymmetry`, `LogDerivZetaLocal` and `LittlewoodGap`, respectively.

The RH statements retain v1.1's weaker counting premise. In the in-repo RH tree, `Z2` includes the Riemann–von Mangoldt asymptotic as well as the local bound. In v1.1 and v1.2, `RiemannVonMangoldt` is only the local bound. This difference predates v1.2; no release theorem is strengthened. `Z3`/`LogDerivZetaLocal` and `ZLittlewood`/`LittlewoodGap` have identical definition bodies. Binder spellings and line breaks also differ between those two RH trees.

The H∞ classical corollaries require agreement only where the continuation is analytic. The retained RH classical corollaries require agreement everywhere in the half-disc. The codiscrete RH boundary clauses also exclude analytic-point agreement, as explained in the paper’s §9. The H∞ conclusions have no exact pole/residue catalogue; the RH conclusions retain theirs. These differences are present in the input statements.

## `phi2_natural_boundary`

Release file: `Phi2NB/Phi2/Statement.lean`. In-repo file: `GoldbachBoundaries/Phi2/Statement.lean`.

### v1.2

```lean
theorem phi2_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue F α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne)
```

### In-repo

```lean
theorem phi2_natural_boundary (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue F α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne)
```

### v1.1

```lean
theorem phi2_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue F α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne)
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `phi2_natural_boundary_classical`

Release file: `Phi2NB/Phi2/Statement.lean`. In-repo file: `GoldbachBoundaries/Phi2/Statement.lean`.

### v1.2

```lean
theorem phi2_natural_boundary_classical (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt)
    (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFΦ : EqOn F Phi2 (halfPlane 2)) (τ r : ℝ) (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball (1 + τ * I) r) ∧ EqOn g F (ball (1 + τ * I) r ∩ HH)
```

### In-repo

Not present in the in-repo file; retained from v1.1.

### v1.1

```lean
theorem phi2_natural_boundary_classical (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt)
    (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFΦ : EqOn F Phi2 (halfPlane 2)) (τ r : ℝ) (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball (1 + τ * I) r) ∧ EqOn g F (ball (1 + τ * I) r ∩ HH)
```

Difference: none from v1.1. No counterpart in the in-repo file.

## `Phi2Proof.phi2_continuation`

Release file: `Phi2NB/Phi2/Proof/M1Continuation.lean`. In-repo file: `GoldbachBoundaries/Phi2/Proof/M1Continuation.lean`.

### v1.2

```lean
theorem phi2_continuation (hRH : RiemannHypothesis) :
    MeromorphicOn Phi2c HH ∧ EqOn Phi2c Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ Phi2c (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt Phi2c α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue Phi2c α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0
```

### In-repo

```lean
theorem phi2_continuation (hRH : RiemannHypothesis) :
    MeromorphicOn Phi2c HH ∧ EqOn Phi2c Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ Phi2c (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt Phi2c α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue Phi2c α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0
```

### v1.1

```lean
theorem phi2_continuation (hRH : RiemannHypothesis) :
    MeromorphicOn Phi2c HH ∧ EqOn Phi2c Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ Phi2c (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt Phi2c α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue Phi2c α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0
```

Difference: none from v1.1. None from the in-repo statement.

## `Phi2Proof.tendsto_eta_Hphi2`

Release file: `Phi2NB/Phi2/Proof/M3Radial.lean`. In-repo file: `GoldbachBoundaries/Phi2/Proof/M3Radial.lean`.

### v1.2

```lean
theorem tendsto_eta_Hphi2 (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (τ : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) * Hphi2 (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I)))
```

### In-repo

```lean
theorem tendsto_eta_Hphi2 (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (τ : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) * Hphi2 (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I)))
```

### v1.1

```lean
theorem tendsto_eta_Hphi2 (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (τ : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) * Hphi2 (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I)))
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `phiR_natural_boundary`

Release file: `Phi2NB/PhiR/Statement.lean`. In-repo file: `GoldbachBoundaries/PhiR/Statement.lean`.

### v1.2

```lean
theorem phiR_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) {r : ℕ}
    (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ F (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue F α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) → F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)))
```

### In-repo

```lean
theorem phiR_natural_boundary (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) {r : ℕ}
    (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ F (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue F α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) → F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)))
```

### v1.1

```lean
theorem phiR_natural_boundary (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) {r : ℕ}
    (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ F (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue F α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) → F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)))
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `phiR_natural_boundary_classical`

Release file: `Phi2NB/PhiR/Statement.lean`. In-repo file: `GoldbachBoundaries/PhiR/Statement.lean`.

### v1.2

```lean
theorem phiR_natural_boundary_classical (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap)
    {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : EqOn F (PhiR r) (halfPlane r)) (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      EqOn g F (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1))
```

### In-repo

```lean
theorem phiR_natural_boundary_classical (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : EqOn F (PhiR r) (halfPlane r)) (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      EqOn g F (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1))
```

### v1.1

```lean
theorem phiR_natural_boundary_classical (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap)
    {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : EqOn F (PhiR r) (halfPlane r)) (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      EqOn g F (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1))
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `phiR_natural_boundary_two`

Release file: `Phi2NB/PhiR/Statement.lean`. In-repo file: `GoldbachBoundaries/PhiR/Statement.lean`.

### v1.2

```lean
theorem phiR_natural_boundary_two (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) ∧ EqOn F (PhiR 2) (halfPlane ((2 : ℕ) : ℝ)) ∧
      AnalyticOnNhd ℂ F (halfPlane (((2 : ℕ) : ℝ) - 1) \ phiRPoles 2) ∧
      (∀ α ∈ phiRPoles 2, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles 2, HasResidue F α (res α)) ∧ HasPhiRResidues 2 res ∧
        ∀ α ∈ phiRPoles 2, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane ((2 : ℕ) : ℝ))] PhiR 2 →
      IsNaturalBoundary F (halfPlane (((2 : ℕ) : ℝ) - 1)) (lineAt (((2 : ℕ) : ℝ) - 1)))
```

### In-repo

```lean
theorem phiR_natural_boundary_two (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) ∧ EqOn F (PhiR 2) (halfPlane ((2 : ℕ) : ℝ)) ∧
      AnalyticOnNhd ℂ F (halfPlane (((2 : ℕ) : ℝ) - 1) \ phiRPoles 2) ∧
      (∀ α ∈ phiRPoles 2, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles 2, HasResidue F α (res α)) ∧ HasPhiRResidues 2 res ∧
        ∀ α ∈ phiRPoles 2, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane ((2 : ℕ) : ℝ))] PhiR 2 →
      IsNaturalBoundary F (halfPlane (((2 : ℕ) : ℝ) - 1)) (lineAt (((2 : ℕ) : ℝ) - 1)))
```

### v1.1

```lean
theorem phiR_natural_boundary_two (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) (hL : LittlewoodGap) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) ∧ EqOn F (PhiR 2) (halfPlane ((2 : ℕ) : ℝ)) ∧
      AnalyticOnNhd ℂ F (halfPlane (((2 : ℕ) : ℝ) - 1) \ phiRPoles 2) ∧
      (∀ α ∈ phiRPoles 2, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles 2, HasResidue F α (res α)) ∧ HasPhiRResidues 2 res ∧
        ∀ α ∈ phiRPoles 2, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane ((2 : ℕ) : ℝ))] PhiR 2 →
      IsNaturalBoundary F (halfPlane (((2 : ℕ) : ℝ) - 1)) (lineAt (((2 : ℕ) : ℝ) - 1)))
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `phiR_singular_iff`

Release file: `Phi2NB/PhiR/Statement.lean`. In-repo file: `GoldbachBoundaries/PhiR/Statement.lean`.

### v1.2

```lean
theorem phiR_singular_iff (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r)
    (τ : ℝ) :
    NoMeromorphicExtensionAt F (halfPlane ((r : ℝ) - 1)) ((r : ℂ) - 1 + τ * I) ↔
      NoMeromorphicExtensionAt Phi2Proof.Phi2c HH (1 + τ * I)
```

### In-repo

```lean
theorem phiR_singular_iff (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r)
    (τ : ℝ) :
    NoMeromorphicExtensionAt F (halfPlane ((r : ℝ) - 1)) ((r : ℂ) - 1 + τ * I) ↔
      NoMeromorphicExtensionAt Phi2Proof.Phi2c HH (1 + τ * I)
```

### v1.1

```lean
theorem phiR_singular_iff (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r)
    (τ : ℝ) :
    NoMeromorphicExtensionAt F (halfPlane ((r : ℝ) - 1)) ((r : ℂ) - 1 + τ * I) ↔
      NoMeromorphicExtensionAt Phi2Proof.Phi2c HH (1 + τ * I)
```

Difference: none from v1.1. None from the in-repo statement.

## `phiR_reduction`

Release file: `Phi2NB/PhiR/Statement.lean`. In-repo file: `GoldbachBoundaries/PhiR/Statement.lean`.

### v1.2

```lean
theorem phiR_reduction (hRH : RiemannHypothesis) {r : ℕ} (hr : 3 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      (∀ a : ℝ, (r : ℝ) - 3 / 2 < a → ∀ T : ℝ, ∃ M : ℝ,
        ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M) ∧
      ∀ s : ℂ, (r : ℝ) < s.re →
        PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
          (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
            (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
          ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + R s
```

### In-repo

```lean
theorem phiR_reduction (hRH : RiemannHypothesis) {r : ℕ} (hr : 3 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      (∀ a : ℝ, (r : ℝ) - 3 / 2 < a → ∀ T : ℝ, ∃ M : ℝ,
        ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M) ∧
      ∀ s : ℂ, (r : ℝ) < s.re →
        PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
          (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
            (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
          ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + R s
```

### v1.1

```lean
theorem phiR_reduction (hRH : RiemannHypothesis) {r : ℕ} (hr : 3 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      (∀ a : ℝ, (r : ℝ) - 3 / 2 < a → ∀ T : ℝ, ∃ M : ℝ,
        ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M) ∧
      ∀ s : ℂ, (r : ℝ) < s.re →
        PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
          (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
            (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
          ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + R s
```

Difference: none from v1.1. None from the in-repo statement.

## `phiR_radial_limit`

Release file: `Phi2NB/PhiR/Statement.lean`. In-repo file: `GoldbachBoundaries/PhiR/Statement.lean`.

### v1.2

```lean
theorem phiR_radial_limit (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ}
    (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * PhiRProof.PhiRc r ((r : ℂ) - 1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℕ) : ℂ) * Phi2Proof.pairAtom τ / Gamma ((r : ℂ) - 1 + τ * I)))
```

### In-repo

```lean
theorem phiR_radial_limit (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ}
    (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * PhiRProof.PhiRc r ((r : ℂ) - 1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℕ) : ℂ) * Phi2Proof.pairAtom τ / Gamma ((r : ℂ) - 1 + τ * I)))
```

### v1.1

```lean
theorem phiR_radial_limit (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ}
    (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * PhiRProof.PhiRc r ((r : ℂ) - 1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℕ) : ℂ) * Phi2Proof.pairAtom τ / Gamma ((r : ℂ) - 1 + τ * I)))
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `PhiRProof.phiR_continuation`

Release file: `Phi2NB/PhiR/Proof/M2Continuation.lean`. In-repo file: `GoldbachBoundaries/PhiR/Proof/M2Continuation.lean`.

### v1.2

```lean
theorem phiR_continuation (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (PhiRc r) (halfPlane ((r : ℝ) - 1)) ∧ EqOn (PhiRc r) (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ (PhiRc r) (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt (PhiRc r) α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue (PhiRc r) α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0
```

### In-repo

```lean
theorem phiR_continuation (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (PhiRc r) (halfPlane ((r : ℝ) - 1)) ∧ EqOn (PhiRc r) (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ (PhiRc r) (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt (PhiRc r) α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue (PhiRc r) α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0
```

### v1.1

```lean
theorem phiR_continuation (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (PhiRc r) (halfPlane ((r : ℝ) - 1)) ∧ EqOn (PhiRc r) (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ (PhiRc r) (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt (PhiRc r) α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue (PhiRc r) α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0
```

Difference: none from v1.1. None from the in-repo statement.

## `PhiRProof.tendsto_eta_Phi2c`

Release file: `Phi2NB/PhiR/Proof/M5Radial.lean`. In-repo file: `GoldbachBoundaries/PhiR/Proof/M5Radial.lean`.

### v1.2

```lean
theorem tendsto_eta_Phi2c (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * Phi2c (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I)))
```

### In-repo

```lean
theorem tendsto_eta_Phi2c (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * Phi2c (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I)))
```

### v1.1

```lean
theorem tendsto_eta_Phi2c (hRH : RiemannHypothesis) (hRvM : RiemannVonMangoldt) (hLD : LogDerivZetaLocal) {τ : ℝ} (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * Phi2c (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I)))
```

Difference: none from v1.1. The in-repo RH statement uses its original premise names and formatting. Where it takes `Z2`, v1.1 and v1.2 take only its local-count conjunct as `RiemannVonMangoldt`; the other renamed premises are definitionally identical. The conclusions are unchanged.

## `Phi2HInf.phi2_hinf_natural_boundary`

Release file: `Phi2NB/Phi2HInf/Statements.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/Statements.lean`.

### v1.2

```lean
theorem phi2_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne)
```

### In-repo

```lean
theorem phi2_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne)
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phiR_hinf_natural_boundary`

Release file: `Phi2NB/Phi2HInf/Statements.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/Statements.lean`.

### v1.2

```lean
theorem phiR_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)))
```

### In-repo

```lean
theorem phiR_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)))
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_natural_boundary_classical`

Release file: `Phi2NB/Phi2HInf/Classical.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/Classical.lean`.

### v1.2

```lean
theorem phi2_hinf_natural_boundary_classical (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : EqOn F Phi2 (halfPlane 2))
    (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball (1 + τ * I) ε) ∧
      ∀ s ∈ ball (1 + τ * I) ε ∩ HH, AnalyticAt ℂ F s → g s = F s
```

### In-repo

```lean
theorem phi2_hinf_natural_boundary_classical (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : EqOn F Phi2 (halfPlane 2))
    (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball (1 + τ * I) ε) ∧
      ∀ s ∈ ball (1 + τ * I) ε ∩ HH, AnalyticAt ℂ F s → g s = F s
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phiR_hinf_natural_boundary_classical`

Release file: `Phi2NB/Phi2HInf/Classical.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/Classical.lean`.

### v1.2

```lean
theorem phiR_hinf_natural_boundary_classical (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : EqOn F (PhiR r) (halfPlane r))
    (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      ∀ s ∈ ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1), AnalyticAt ℂ F s → g s = F s
```

### In-repo

```lean
theorem phiR_hinf_natural_boundary_classical (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : EqOn F (PhiR r) (halfPlane r))
    (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      ∀ s ∈ ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1), AnalyticAt ℂ F s → g s = F s
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_pole_twoBsup`

Release file: `Phi2NB/Phi2HInf/PoleTwoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/PoleTwoBsup.lean`.

### v1.2

```lean
theorem phi2_hinf_pole_twoBsup (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    (1 / 2 < Bsup ∧ Bsup < 1) ∧
    ({ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) ∧
    (collisionAtom (2 * (Bsup : ℂ)) =
        ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
          ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) ∧
      0 < (collisionAtom (2 * (Bsup : ℂ))).re ∧ (collisionAtom (2 * (Bsup : ℂ))).im = 0) ∧
    HasResidue Phi2cHInf (2 * (Bsup : ℂ))
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    (0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re ∧
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).im = 0) ∧
    meromorphicOrderAt Phi2cHInf (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) ∧
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ))
```

### In-repo

```lean
theorem phi2_hinf_pole_twoBsup (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    (1 / 2 < Bsup ∧ Bsup < 1) ∧
    ({ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) ∧
    (collisionAtom (2 * (Bsup : ℂ)) =
        ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
          ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) ∧
      0 < (collisionAtom (2 * (Bsup : ℂ))).re ∧ (collisionAtom (2 * (Bsup : ℂ))).im = 0) ∧
    HasResidue Phi2cHInf (2 * (Bsup : ℂ))
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    (0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re ∧
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).im = 0) ∧
    meromorphicOrderAt Phi2cHInf (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) ∧
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ))
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_pole_twoBsup'`

Release file: `Phi2NB/Phi2HInf/PoleTwoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/PoleTwoBsup.lean`.

### v1.2

```lean
theorem phi2_hinf_pole_twoBsup' (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    (1 / 2 < Bsup ∧ Bsup < 1) ∧
    ({ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) ∧
    (collisionAtom (2 * (Bsup : ℂ)) =
        ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
          ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) ∧
      0 < (collisionAtom (2 * (Bsup : ℂ))).re ∧ (collisionAtom (2 * (Bsup : ℂ))).im = 0) ∧
    HasResidue Phi2cHInf (2 * (Bsup : ℂ))
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    (0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re ∧
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).im = 0) ∧
    meromorphicOrderAt Phi2cHInf (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) ∧
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ))
```

### In-repo

```lean
theorem phi2_hinf_pole_twoBsup' (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hStir : StirlingStrip)
    (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2) :
    (1 / 2 < Bsup ∧ Bsup < 1) ∧
    ({ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty) ∧
    (collisionAtom (2 * (Bsup : ℂ)) =
        ((∑' ρ : {ρ : NontrivialZeros // (ρ : ℂ).re = Bsup},
          ((zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) : ℝ) : ℂ) ∧
      0 < (collisionAtom (2 * (Bsup : ℂ))).re ∧ (collisionAtom (2 * (Bsup : ℂ))).im = 0) ∧
    HasResidue Phi2cHInf (2 * (Bsup : ℂ))
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    (0 < (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).re ∧
      (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))).im = 0) ∧
    meromorphicOrderAt Phi2cHInf (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ) ∧
    ¬ AnalyticAt ℂ Phi2cHInf (2 * (Bsup : ℂ))
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_pole_twoBsup_of_continuation`

Release file: `Phi2NB/Phi2HInf/PoleTwoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/PoleTwoBsup.lean`.

### v1.2

```lean
theorem phi2_hinf_pole_twoBsup_of_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    HasResidue F (2 * (Bsup : ℂ)) (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    meromorphicOrderAt F (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ)
```

### In-repo

```lean
theorem phi2_hinf_pole_twoBsup_of_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) (hoff : ∃ ρ ∈ NontrivialZeros, ρ.re ≠ 1 / 2)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    HasResidue F (2 * (Bsup : ℂ)) (collisionAtom (2 * (Bsup : ℂ)) / Gamma (2 * (Bsup : ℂ))) ∧
    meromorphicOrderAt F (2 * (Bsup : ℂ)) = ((-1 : ℤ) : WithTop ℤ)
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_rh_iff_no_real_pole`

Release file: `Phi2NB/Phi2HInf/PoleTwoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/PoleTwoBsup.lean`.

### v1.2

```lean
theorem phi2_hinf_rh_iff_no_real_pole (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x
```

### In-repo

```lean
theorem phi2_hinf_rh_iff_no_real_pole (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_rh_iff_no_real_pole'`

Release file: `Phi2NB/Phi2HInf/PoleTwoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/PoleTwoBsup.lean`.

### v1.2

```lean
theorem phi2_hinf_rh_iff_no_real_pole' (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x
```

### In-repo

```lean
theorem phi2_hinf_rh_iff_no_real_pole' (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → AnalyticAt ℂ Phi2cHInf x
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.phi2_hinf_rh_iff_no_real_pole_of_continuation`

Release file: `Phi2NB/Phi2HInf/PoleTwoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/PoleTwoBsup.lean`.

### v1.2

```lean
theorem phi2_hinf_rh_iff_no_real_pole_of_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → 0 ≤ meromorphicOrderAt F x
```

### In-repo

```lean
theorem phi2_hinf_rh_iff_no_real_pole_of_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) (hζ : ZetaNoZeroIoo)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2) :
    RiemannHypothesis ↔ ∀ x : ℝ, 1 < x → x < 2 → 0 ≤ meromorphicOrderAt F x
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.

## `Phi2HInf.hasResidue_Phi2cHInf_of_not_mem_phi2Poles`

Release file: `Phi2NB/Phi2HInf/Fill/pole_twoBsup.lean`. In-repo file: `GoldbachBoundaries/Phi2HInf/Fill/pole_twoBsup.lean`.

### v1.2

```lean
theorem hasResidue_Phi2cHInf_of_not_mem_phi2Poles (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {s : ℂ} (hs : 1 < s.re) (hP : s ∉ phi2Poles) :
    HasResidue Phi2cHInf s (collisionAtom s / Gamma s)
```

### In-repo

```lean
theorem hasResidue_Phi2cHInf_of_not_mem_phi2Poles (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {s : ℂ} (hs : 1 < s.re) (hP : s ∉ phi2Poles) :
    HasResidue Phi2cHInf s (collisionAtom s / Gamma s)
```

### v1.1

Not present in v1.1.

Difference: none from the in-repo statement.
