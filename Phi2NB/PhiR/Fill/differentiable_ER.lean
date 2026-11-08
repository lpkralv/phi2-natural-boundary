import Phi2NB.PhiR.Proof.Defs
import Phi2NB.Phi2.Fill.ACommon

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof.FillA

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- Exponential decay of `FL` makes every positive integral power's tail entire. -/
theorem differentiable_ER' {r : ℕ} (hr : 1 ≤ r) : Differentiable ℂ (ER r) := by
  obtain ⟨hc, C, hC⟩ := Phi2Proof.FillA.FL_continuousOn_and_le_exp
  apply TIdentity.differentiable_integral_Ioi_cpow (C := (max C 0) ^ r)
  · exact (Complex.continuous_ofReal.comp_continuousOn
      ((hc.mono (show Ioi (1 : ℝ) ⊆ Ioi 0 from
        fun t ht => lt_trans one_pos (mem_Ioi.mp ht))).pow r)).aestronglyMeasurable
      measurableSet_Ioi
  · intro t ht
    have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by have ht1 : 1 < t := ht; linarith)
    have hp : Real.exp (-t) ^ r ≤ Real.exp (-t) :=
      by simpa only [pow_one] using (pow_le_pow_of_le_one he0 he1 hr)
    rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (Phi2Proof.FillA.FL_nonneg' t) _)]
    calc FL t ^ r ≤ (max C 0 * Real.exp (-t)) ^ r :=
          pow_le_pow_left₀ (Phi2Proof.FillA.FL_nonneg' t)
            ((hC t ht.le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he0)) _
      _ = max C 0 ^ r * Real.exp (-t) ^ r := mul_pow _ _ _
      _ ≤ max C 0 ^ r * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left hp (pow_nonneg (le_max_right _ _) _)

end GoldbachBoundaries.PhiRProof.FillA
