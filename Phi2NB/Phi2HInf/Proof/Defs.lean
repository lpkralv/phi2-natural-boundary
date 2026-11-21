import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Proof.Defs`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Phi2Proof

def c0 : ℂ := negLogDerivZeta 0

def V (x : ℝ) : ℂ := VerticalIntegral' (kernelL x) (-(1 / 2 : ℝ))

def L (s : ℂ) : ℂ := ∑' ρ : NontrivialZeros, zeroCoef ρ / (s - ρ)

abbrev C := cauchyT

def A (s : ℂ) : ℂ := E2L s - 2 * e1L (s - 1) +
  ∫ x in Ioc (0 : ℝ) 1, ((c0 + V x) ^ 2 - 2 * zeroSum x * V x) * (x : ℂ) ^ (s - 1)

def M0 (s : ℂ) : ℂ := phi2Main s - 2 * c0 * L s / Gamma s

def Phi2cHInf (s : ℂ) : ℂ := M0 s + (C s + A s) / Gamma s

def collisionIdx (s : ℂ) := {p : NontrivialZeros × NontrivialZeros //
  (p.1 : ℂ) + p.2 = s}

def collisionAtom (s : ℂ) : ℂ :=
  ∑' p : collisionIdx s, zeroCoef p.1.1 * zeroCoef p.1.2

def rightZeros : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ 1 / 2 < ρ.re}

def offLineZeros : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ ρ.re ≠ 1 / 2}

def bKerH (b c τ u : ℝ) : ℂ :=
  Gamma ((b : ℂ) + (u + τ : ℝ) * I) * Gamma ((c : ℂ) - (u : ℂ) * I)

def bAmp (b c τ u : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (-Real.pi * u - Real.pi * τ / 2) * u ^ (b + c - 1)

def bMain (b c τ u : ℝ) : ℂ :=
  (bAmp b c τ u : ℂ) * exp (((τ * Real.log u + Real.pi * (b - c) / 2 : ℝ) : ℂ) * I)

def coneRotation (τ u₀ : ℝ) : ℂ := exp (-((τ * Real.log u₀ : ℝ) : ℂ) * I)

def coneMargin (B : ℝ) : ℝ := Real.sin (Real.pi * (1 - B) / 2)

abbrev CriticalZero := {ρ : NontrivialZeros // (ρ : ℂ).re = 1 / 2}

def criticalVal (ρ : CriticalZero) : ℂ := ρ.1

def criticalC (s : ℂ) : ℂ := ∑' p : CriticalZero × CriticalZero,
  zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2) /
    (s - criticalVal p.1 - criticalVal p.2)

def criticalPairIdx (τ : ℝ) := {p : CriticalZero × CriticalZero //
  criticalVal p.1 + criticalVal p.2 = 1 + τ * I}

def criticalAtom (τ : ℝ) : ℂ := ∑' p : criticalPairIdx τ,
  zeroCoef (criticalVal p.1.1) * zeroCoef (criticalVal p.1.2)

def exceptionalC (s : ℂ) : ℂ :=
  ∑' p : {p : NontrivialZeros × NontrivialZeros //
      (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2},
    zeroCoef p.1.1 * zeroCoef p.1.2 / (s - p.1.1 - p.1.2)

def W (s : ℂ) : ℂ := M0 s + (exceptionalC s + A s) / Gamma s

end GoldbachBoundaries.Phi2HInf
