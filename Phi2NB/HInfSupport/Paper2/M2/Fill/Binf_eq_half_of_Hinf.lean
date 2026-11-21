import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.HInfSupport.Paper2.M1.Fill.BCommon
import Phi2NB.HInfSupport.Paper2.M1.Fill.half_le_Binf

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M2.Fill.Binf_eq_half_of_Hinf`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem Binf_eq_half_of_Hinf (hZ1 : Z1) (hH : Hinf) : Binf = 1 / 2 := by
  refine le_antisymm ?_ (half_le_Binf hZ1)
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have hfin := hH (δ / 2) (by linarith)
  obtain ⟨T, hT⟩ := (hfin.image fun ρ : ℂ => |ρ.im|).bddAbove
  have hle : binfFam (T + 1) ≤ 1 / 2 + δ / 2 := by
    refine csSup_le (re_image_nonempty_height _) ?_
    rintro _ ⟨ρ, ⟨hρ, ht⟩, rfl⟩
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have := hT ⟨ρ, ⟨hρ, hcon⟩, rfl⟩
    linarith
  linarith [Binf_le_binfFam (T + 1)]

end GoldbachBoundaries.Paper2.M2
