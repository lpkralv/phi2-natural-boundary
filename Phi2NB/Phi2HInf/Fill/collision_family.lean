import Phi2NB.PhiR.Statement
import Phi2NB.HInfSupport.Paper2.Defs
import Phi2NB.Phi2HInf.Defs
import Phi2NB.Phi2HInf.Fill.collision_bin_le
import Phi2NB.Phi2HInf.Fill.sum_bKer_ne_zero_hinf
import Phi2NB.Phi2HInf.Proof.Defs

/-! Extracted for v1.2 from `GoldbachBoundaries.Phi2HInf.Fill.collision_family`.
Shared v1.1 declarations are imported; source helpers taking full `Z2` use the suffix `_fullZ2`. -/

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

def swapCollision {s : ℂ} (p : collisionIdx s) : collisionIdx s :=
  ⟨p.1.swap, by simpa only [Prod.swap, add_comm] using p.2⟩

def orientCollision {s : ℂ} (p : collisionIdx s) : collisionIdx s :=
  if (p.1.2 : ℂ).im < 0 then p else swapCollision p

theorem tagged_orientation_injective (s : ℂ) : Function.Injective
    (fun p : collisionIdx s => (decide ((p.1.2 : ℂ).im < 0), orientCollision p)) := by
  classical
  intro p q h
  have ht := congrArg Prod.fst h
  have ho := congrArg Prod.snd h
  by_cases hp : (p.1.2 : ℂ).im < 0 <;> by_cases hq : (q.1.2 : ℂ).im < 0
  · simpa only [orientCollision, if_pos hp, if_pos hq] using ho
  · simp [hp, hq] at ht
  · simp [hp, hq] at ht
  · have hh : swapCollision p = swapCollision q := by
      simpa only [orientCollision, if_neg hp, if_neg hq] using ho
    have hv := congrArg (fun r : collisionIdx s => r.1.swap) hh
    exact Subtype.ext hv

theorem finite_collision_bin (s : ℂ) (v : ℝ) :
    {p : collisionIdx s | -(p.1.2 : ℂ).im ∈ Ico v (v + 1)}.Finite := by
  let g : collisionIdx s → ℂ := fun p => p.1.2
  have hg : Function.Injective g := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hp := p.2
      change (p.1.2 : ℂ) = q.1.2 at hpq
      rw [hpq] at hp
      exact add_right_cancel (hp.trans q.2.symm)
    · exact Subtype.ext hpq
  refine ((M1.finite_zeros_abs_im_le (|v| + 1)).preimage hg.injOn).subset ?_
  intro p hp
  refine ⟨p.1.2.2, ?_⟩
  change |(p.1.2 : ℂ).im| ≤ |v| + 1
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2, le_abs_self v, neg_le_abs v]

theorem oriented_family_bins (hZ1 : Z1) (hZ2 : Z2) {Y : ℝ} (hY : 0 < Y) :
    ∃ K : ℝ, ∀ s : ℂ, |s.im| ≤ Y → ∀ {ι : Type} (p : ι → collisionIdx s),
      Function.Injective p →
      (∀ v : ℝ, {i | -( (orientCollision (p i)).1.2 : ℂ).im ∈ Ico v (v + 1)}.Finite) ∧
      (∀ v : ℝ, 0 ≤ v →
        ∑ᶠ i ∈ {i | -((orientCollision (p i)).1.2 : ℂ).im ∈ Ico v (v + 1)},
          ((zetaMult (p i).1.1 * zetaMult (p i).1.2 : ℕ) : ℝ) ≤
            K * Real.log (v + Y + 4) ^ 2) := by
  classical
  obtain ⟨K, hK⟩ := collision_bin_le hZ1 hZ2 hY
  refine ⟨2 * K, ?_⟩
  intro s hs ι p hp
  let e (i : ι) := (decide (((p i).1.2 : ℂ).im < 0), orientCollision (p i))
  have he : Function.Injective e := (tagged_orientation_injective s).comp hp
  let S (v : ℝ) := {i | -((orientCollision (p i)).1.2 : ℂ).im ∈ Ico v (v + 1)}
  let T (v : ℝ) := (Finset.univ : Finset Bool) ×ˢ (finite_collision_bin s v).toFinset
  have hmap (v : ℝ) : ∀ i ∈ S v, e i ∈ T v := by
    intro i hi
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (finite_collision_bin s v).mem_toFinset.mpr hi⟩
  have hfin (v : ℝ) : (S v).Finite :=
    ((T v).finite_toSet.preimage he.injOn).subset (hmap v)
  refine ⟨hfin, ?_⟩
  intro v hv
  have hweight (i : ι) :
      zetaMult (p i).1.1 * zetaMult (p i).1.2 =
        zetaMult (e i).2.1.1 * zetaMult (e i).2.1.2 := by
    dsimp [e, orientCollision]
    split_ifs <;> simp only [swapCollision, Prod.swap, mul_comm]
  have hle : ∑ i ∈ (hfin v).toFinset,
      ((zetaMult (p i).1.1 * zetaMult (p i).1.2 : ℕ) : ℝ) ≤
      ∑ a ∈ T v, ((zetaMult a.2.1.1 * zetaMult a.2.1.2 : ℕ) : ℝ) := by
    apply Finset.sum_le_sum_of_injOn e he.injOn
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
      exact hmap v i ((hfin v).mem_toFinset.mp hi)
    · intro i _
      exact le_of_eq (congrArg (fun n : ℕ => (n : ℝ)) (hweight i))
    · intros; exact Nat.cast_nonneg _
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin v)]
  calc
    _ ≤ ∑ a ∈ T v, ((zetaMult a.2.1.1 * zetaMult a.2.1.2 : ℕ) : ℝ) := hle
    _ = 2 * ∑ᶠ q ∈ {q : collisionIdx s | -(q.1.2 : ℂ).im ∈ Ico v (v + 1)},
        ((zetaMult q.1.1 * zetaMult q.1.2 : ℕ) : ℝ) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (finite_collision_bin s v)]
      simp [T, Finset.sum_product, two_mul]
    _ ≤ 2 * (K * Real.log (v + Y + 4) ^ 2) := mul_le_mul_of_nonneg_left (hK s hs v hv) (by norm_num)
    _ = (2 * K) * Real.log (v + Y + 4) ^ 2 := by ring

theorem pair_family_ne_zero_of_large (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {B Y : ℝ} (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ X : ℝ, Y ≤ X ∧ ∀ s : ℂ, |s.im| ≤ Y →
      ∀ {ι : Type} (p : ι → collisionIdx s), Function.Injective p → Nonempty ι →
      (∀ i, ((p i).1.1 : ℂ).re ∈ Icc (1 - B) B ∧ ((p i).1.2 : ℂ).re ∈ Icc (1 - B) B) →
      (∀ i, X < |((p i).1.1 : ℂ).im| ∧ X < |((p i).1.2 : ℂ).im|) →
      (∑' i, zeroCoef (p i).1.1 * zeroCoef (p i).1.2) ≠ 0 := by
  classical
  obtain ⟨K, hK⟩ := oriented_family_bins hZ1 hZ2 hY
  obtain ⟨U, hUY, hU⟩ := sum_bKer_ne_zero_hinf hStir (K := K) hB hB1 hY
  refine ⟨U, by linarith, ?_⟩
  intro s hs ι p hp hne hbc hlarge
  let o (i : ι) := orientCollision (p i)
  let b (i : ι) := ((o i).1.1 : ℂ).re
  let c (i : ι) := ((o i).1.2 : ℂ).re
  let u (i : ι) := -((o i).1.2 : ℂ).im
  let q (i : ι) := zetaMult (p i).1.1 * zetaMult (p i).1.2
  obtain ⟨hfin, hbin⟩ := hK s hs p hp
  have hbig (i : ι) : U < u i := by
    have him : ((p i).1.1 : ℂ).im + ((p i).1.2 : ℂ).im = s.im := by
      simpa only [add_im] using congrArg Complex.im (p i).2
    have hhi := hlarge i
    dsimp [u, o, orientCollision]
    split_ifs with hneg
    · simpa only [abs_of_neg hneg] using hhi.2
    · have hpos : 0 ≤ ((p i).1.2 : ℂ).im := le_of_not_gt hneg
      rw [abs_of_nonneg hpos] at hhi
      have hleft : ((p i).1.1 : ℂ).im < 0 := by linarith [le_abs_self s.im]
      simpa only [swapCollision, Prod.swap, abs_of_neg hleft] using hhi.1
  have hbc' (i : ι) : b i ∈ Icc (1 - B) B ∧ c i ∈ Icc (1 - B) B := by
    dsimp [b, c, o, orientCollision]
    split_ifs
    · exact hbc i
    · exact ⟨(hbc i).2, (hbc i).1⟩
  have hsumre (i : ι) : b i + c i = s.re := by
    simpa only [b, c, add_re] using congrArg Complex.re (o i).2
  obtain ⟨i₁⟩ := hne
  let S := {i : ι | u i ≤ u i₁}
  have hSfin : S.Finite := by
    refine (Set.Finite.biUnion (Finset.range (⌊u i₁⌋₊ + 1)).finite_toSet
      (fun k _ => hfin (k : ℝ))).subset ?_
    intro i hi
    have hui : 0 ≤ u i := by linarith [hbig i]
    simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_ofPred_eq]
    exact ⟨⌊u i⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor hi),
      Nat.floor_le hui, Nat.lt_floor_add_one _⟩
  obtain ⟨i₀, hi₀S, hi₀⟩ := hSfin.toFinset.exists_min_image u ⟨i₁, by simp [S]⟩
  have hmin (i : ι) : u i₀ ≤ u i := by
    by_cases hi : i ∈ S
    · exact hi₀ i (hSfin.mem_toFinset.mpr hi)
    · have h1 : u i₁ < u i := not_le.mp hi
      have h2 : u i₀ ≤ u i₁ := hSfin.mem_toFinset.mp hi₀S
      exact h2.trans h1.le
  have hmult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ zetaMult ρ :=
    one_le_zetaMult_of_zero (fun h => by
      have hh := hρ.2.2
      rw [h, Complex.one_re] at hh
      exact lt_irrefl _ hh) hρ.1
  have hq : 1 ≤ q i₀ := by
    have h1 := hmult (p i₀).1.1.2
    have h2 := hmult (p i₀).1.2.2
    dsimp [q]
    nlinarith
  have hnonzero := (hU s.im hs b c u q i₀ hbc'
    (fun i => (hsumre i).trans (hsumre i₀).symm) (hbig i₀).le hmin hq hfin hbin).2
  have hterm (i : ι) : zeroCoef (p i).1.1 * zeroCoef (p i).1.2 =
      (q i : ℂ) * bKerH (b i) (c i) s.im (u i) := by
    have him : ((o i).1.1 : ℂ).im + ((o i).1.2 : ℂ).im = s.im := by
      simpa only [add_im] using congrArg Complex.im (o i).2
    have hfirst : (b i : ℂ) + ((u i + s.im : ℝ) : ℂ) * I = (o i).1.1 := by
      apply Complex.ext <;> simp [b, u] <;> linarith
    have hsecond : (c i : ℂ) - (u i : ℂ) * I = (o i).1.2 := by
      apply Complex.ext <;> simp [c, u]
    rw [bKerH, hfirst, hsecond]
    dsimp [q, o, orientCollision]
    split_ifs <;> simp only [swapCollision, Prod.swap, zeroCoef, Nat.cast_mul] <;> ring
  simpa only [← hterm] using hnonzero

end GoldbachBoundaries.Phi2HInf
