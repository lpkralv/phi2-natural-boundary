import Phi2NB.PhiR.Statement

/-! Extracted for v1.2 from `GoldbachBoundaries.ResidueAPI`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Asymptotics

namespace GoldbachBoundaries

variable {f g : ℂ → ℂ} {a b c c' : ℂ}

theorem HasResidue.congr (h : HasResidue f a c) (hfg : f =ᶠ[𝓝[≠] a] g) : HasResidue g a c :=
  h.congr' (hfg.mono fun z hz => by simp only [hz])

end GoldbachBoundaries
