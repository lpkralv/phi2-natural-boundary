import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Paper2.M1.Fill.BCommon`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

def binfFam (t : ℝ) : ℝ := sSup (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|})

lemma Binf_eq_iInf : Binf = ⨅ t : ℝ, binfFam t := rfl

lemma re_image_bddAbove {s : Set ℂ} (hs : s ⊆ NontrivialZeros) : BddAbove (re '' s) :=
  ⟨1, by rintro _ ⟨ρ, hρ, rfl⟩; exact (hs hρ).2.2.le⟩

lemma re_image_nonempty_height (t : ℝ) :
    (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|}).Nonempty := by
  obtain ⟨ρ, hρ, h⟩ := exists_nontrivialZero_im_gt |t|
  exact ⟨ρ.re, ρ, ⟨hρ, (le_abs_self t).trans (h.le.trans (le_abs_self _))⟩, rfl⟩

lemma nontrivialZeros_nonempty : NontrivialZeros.Nonempty := by
  obtain ⟨ρ, hρ, -⟩ := exists_nontrivialZero_im_gt 0
  exact ⟨ρ, hρ⟩

lemma binfFam_nonneg (t : ℝ) : 0 ≤ binfFam t :=
  Real.sSup_nonneg (by rintro _ ⟨ρ, hρ, rfl⟩; exact hρ.1.2.1.le)

lemma binfFam_bddBelow : BddBelow (range binfFam) :=
  ⟨0, by rintro _ ⟨t, rfl⟩; exact binfFam_nonneg t⟩

lemma Binf_le_binfFam (t : ℝ) : Binf ≤ binfFam t := ciInf_le binfFam_bddBelow t

lemma re_le_binfFam {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) {t : ℝ} (ht : t ≤ |ρ.im|) : ρ.re ≤ binfFam t :=
  le_csSup (re_image_bddAbove fun _ h => h.1) ⟨ρ, ⟨hρ, ht⟩, rfl⟩

lemma exists_binfFam_lt {δ : ℝ} (hδ : 0 < δ) : ∃ t, binfFam t < Binf + δ :=
  (ciInf_lt_iff binfFam_bddBelow).1 (by rw [← Binf_eq_iInf]; linarith)

lemma re_le_Bsup {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.re ≤ Bsup :=
  le_csSup (re_image_bddAbove subset_rfl) ⟨ρ, hρ, rfl⟩

end GoldbachBoundaries.Paper2.M1
