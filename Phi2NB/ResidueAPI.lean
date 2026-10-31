import Phi2NB.Defs

/-!
# API for `HasResidue`

General facts about `HasResidue f a c := Tendsto (fun s => (s - a) * f s) (𝓝[≠] a) (𝓝 c)`
(`Defs.lean`): uniqueness, linearity, the model pole `c / (z - a)`, invariance under adding a function bounded
(or convergent, continuous, analytic) near `a`, the shift `z ↦ z - b`, and the bridge to `meromorphicOrderAt`
(a meromorphic function with a `HasResidue` has order `≥ -1`, and `= -1` if the residue is non-zero).

Every statement looks only at punctured neighbourhoods, so values at the pole (junk) never matter.
-/

noncomputable section

open Complex Filter Topology Set Asymptotics

namespace GoldbachBoundaries

variable {f g : ℂ → ℂ} {a b c c' : ℂ}

/-! ## Uniqueness -/

/-- A residue (in the `HasResidue` sense) is unique. -/
theorem HasResidue.unique (h : HasResidue f a c) (h' : HasResidue f a c') : c = c' :=
  tendsto_nhds_unique h h'

/-! ## Linearity -/

theorem HasResidue.add (hf : HasResidue f a c) (hg : HasResidue g a c') :
    HasResidue (f + g) a (c + c') := by
  unfold HasResidue at *
  simpa [mul_add] using hf.add hg

theorem HasResidue.add' (hf : HasResidue f a c) (hg : HasResidue g a c') :
    HasResidue (fun z => f z + g z) a (c + c') :=
  hf.add hg

theorem HasResidue.neg (hf : HasResidue f a c) : HasResidue (fun z => -f z) a (-c) := by
  unfold HasResidue at *
  simpa [mul_neg] using hf.neg

theorem HasResidue.sub (hf : HasResidue f a c) (hg : HasResidue g a c') :
    HasResidue (fun z => f z - g z) a (c - c') := by
  unfold HasResidue at *
  simpa [mul_sub] using hf.sub hg

/-- The model simple pole: `c / (z - a)` has residue `c` at `a`. -/
theorem hasResidue_div_sub (a c : ℂ) : HasResidue (fun z => c / (z - a)) a c := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  field_simp [sub_ne_zero.mpr hz]

/-! ## Bounded perturbations -/

/-- A function bounded on a punctured neighbourhood of `a` has residue `0` there. -/
theorem hasResidue_zero_of_isBigO (hg : g =O[𝓝[≠] a] (1 : ℂ → ℂ)) : HasResidue g a 0 := by
  have hp : (fun z : ℂ => z - a) =o[𝓝[≠] a] (1 : ℂ → ℂ) :=
    (isLittleO_one_iff ℂ).2
      (tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds))
  simpa [HasResidue] using (hp.mul_isBigO hg).tendsto_div_nhds_zero.congr (fun z => by simp)

/-- A function with a finite limit on the punctured neighbourhood has residue `0`. -/
theorem hasResidue_zero_of_tendsto {L : ℂ} (hg : Tendsto g (𝓝[≠] a) (𝓝 L)) :
    HasResidue g a 0 :=
  hasResidue_zero_of_isBigO (hg.isBigO_one ℂ)

/-- A function continuous at `a` has residue `0` there. -/
theorem hasResidue_zero_of_continuousAt (hg : ContinuousAt g a) : HasResidue g a 0 :=
  hasResidue_zero_of_tendsto (hg.tendsto.mono_left nhdsWithin_le_nhds)

/-- An analytic function has residue `0`. -/
theorem hasResidue_zero_of_analyticAt (hg : AnalyticAt ℂ g a) : HasResidue g a 0 :=
  hasResidue_zero_of_continuousAt hg.continuousAt

/-- Adding a function bounded near `a` does not change the residue. -/
theorem HasResidue.add_isBigO (hf : HasResidue f a c) (hg : g =O[𝓝[≠] a] (1 : ℂ → ℂ)) :
    HasResidue (fun z => f z + g z) a c := by
  simpa using hf.add' (hasResidue_zero_of_isBigO hg)

/-- Adding a function continuous at `a` does not change the residue. -/
theorem HasResidue.add_continuousAt (hf : HasResidue f a c) (hg : ContinuousAt g a) :
    HasResidue (fun z => f z + g z) a c := by
  simpa using hf.add' (hasResidue_zero_of_continuousAt hg)

/-- Adding a function analytic at `a` does not change the residue. -/
theorem HasResidue.add_analyticAt (hf : HasResidue f a c) (hg : AnalyticAt ℂ g a) :
    HasResidue (fun z => f z + g z) a c :=
  hf.add_continuousAt hg.continuousAt

/-- If `f - c / (z - a)` is bounded near `a` (punctured), then `f` has residue `c` at `a`. -/
theorem hasResidue_of_sub_isBigO
    (h : (fun z => f z - c / (z - a)) =O[𝓝[≠] a] (1 : ℂ → ℂ)) : HasResidue f a c := by
  have := (hasResidue_div_sub a c).add_isBigO h
  simpa using this

/-! ## Change of variables -/

/-- Shift: `z ↦ f (z - b)` has residue `c` at `a + b`. -/
theorem HasResidue.comp_sub_const (hf : HasResidue f a c) (b : ℂ) :
    HasResidue (fun z => f (z - b)) (a + b) c := by
  have hmap : Tendsto (fun z : ℂ => z - b) (𝓝[≠] (a + b)) (𝓝[≠] a) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z : ℂ => z - b) (𝓝 (a + b)) (𝓝 (a + b - b)) :=
        (continuous_sub_right b).tendsto _
      rw [add_sub_cancel_right] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro h
      apply hz
      simp only [Set.mem_singleton_iff] at h ⊢
      rw [← h]
      ring
  refine (hf.comp hmap).congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply]
  ring_nf

/-! ## Bridge to `meromorphicOrderAt` -/

/-- A meromorphic function with a `HasResidue` at `a` has a pole of order at most one there. -/
theorem HasResidue.neg_one_le_meromorphicOrderAt (hm : MeromorphicAt f a)
    (hf : HasResidue f a c) : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f a := by
  have hsub : MeromorphicAt (fun s : ℂ => s - a) a := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hprod : MeromorphicAt ((fun s : ℂ => s - a) * f) a := hsub.mul hm
  have h0 : 0 ≤ meromorphicOrderAt ((fun s : ℂ => s - a) * f) a :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hprod).1 ⟨c, hf⟩
  rw [meromorphicOrderAt_mul hsub hm, meromorphicOrderAt_id_sub_const] at h0
  cases ho : meromorphicOrderAt f a with
  | top => exact le_top
  | coe n =>
    rw [ho] at h0
    have : (0 : ℤ) ≤ 1 + n := by exact_mod_cast h0
    exact_mod_cast (by omega : (-1 : ℤ) ≤ n)

/-- A meromorphic function with a non-zero `HasResidue` at `a` has a simple pole there. -/
theorem HasResidue.meromorphicOrderAt_eq_neg_one (hm : MeromorphicAt f a)
    (hf : HasResidue f a c) (hc : c ≠ 0) : meromorphicOrderAt f a = ((-1 : ℤ) : WithTop ℤ) := by
  have hsub : MeromorphicAt (fun s : ℂ => s - a) a := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hprod : MeromorphicAt ((fun s : ℂ => s - a) * f) a := hsub.mul hm
  have h0 : meromorphicOrderAt ((fun s : ℂ => s - a) * f) a = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod).1 ⟨c, hc, hf⟩
  rw [meromorphicOrderAt_mul hsub hm, meromorphicOrderAt_id_sub_const] at h0
  cases ho : meromorphicOrderAt f a with
  | top => rw [ho] at h0; simp at h0
  | coe n =>
    rw [ho] at h0
    have : (1 : ℤ) + n = 0 := by exact_mod_cast h0
    exact_mod_cast (by omega : n = -1)

end GoldbachBoundaries
