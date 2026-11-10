/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps

/-!
# Pure Slab Bijection Preservation (`gmPushSlab`, `gmPopSlab`)

This module defines the pure `GlobalMeta` slab-stack updates (`gmPushSlab`, `gmUnlinkTopSlab`,
`gmCompactSlab`, `gmPopSlab`) and proves that they preserve `SlabBijection` and `TailBijection`
when promoting or demoting a full slab of `K = slabSize n_max` items.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPushSlab`: pure `GlobalMeta` update
  allocating a new full slab as the top slab of bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmUnlinkTopSlab`: Stage A of slab pop,
  unlinking the top slab of bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmCompactSlab`: Stage B of slab pop,
  compacting the physical slab pool into the vacated slab `p_del`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPopSlab`: composite `GlobalMeta` update
  popping the top slab of bucket `b` and compacting the slab pool.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPushSlab_fields`: field-by-field description
  of `gmPushSlab`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmPushSlab`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmPushSlab`: `gmPushSlab`
  preserves `TailBijection` and `SlabBijection`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmUnlinkTopSlab_fields`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmCompactSlab_fields_lt`: field-by-field
  descriptions of the two stages of `gmPopSlab`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmPopSlab`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmPopSlab`: `gmPopSlab`
  preserves `TailBijection` and `SlabBijection`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Finset

theorem nslabs_lt_maxFullSlabs_of_mul_le {n_max n_slabs : ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (hle : (n_slabs + 1) * slabSize n_max ≤ n_max) :
    n_slabs < maxFullSlabs n_max := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  unfold maxFullSlabs
  rw [ite_eq_right hb0]
  have hdiv : n_slabs + 1 ≤ n_max / slabSize n_max :=
    (Nat.le_div_iff_mul_le (slabSize_pos n_max)).mpr hle
  omega

theorem slabPtrOf_inj {n_max : ℕ} {gm q_fn : ℕ → ℕ} {n_slabs : ℕ}
    (hslab : SlabBijection n_max gm q_fn n_slabs)
    {b₁ : ℕ} (hb₁ : b₁ < numBuckets n_max) {s₁ : ℕ} (hs₁ : s₁ < q_fn b₁)
    {b₂ : ℕ} (hb₂ : b₂ < numBuckets n_max) {s₂ : ℕ} (hs₂ : s₂ < q_fn b₂)
    (heq : slabPtrOf n_max gm b₁ s₁ = slabPtrOf n_max gm b₂ s₂) :
    b₁ = b₂ ∧ s₁ = s₂ := by
  have hB : b₁ = b₂ := by
    rw [← hslab.ownerB_ptr b₁ hb₁ s₁ hs₁, heq, hslab.ownerB_ptr b₂ hb₂ s₂ hs₂]
  have hS : s₁ = s₂ := by
    rw [← hslab.ownerS_ptr b₁ hb₁ s₁ hs₁, heq, hslab.ownerS_ptr b₂ hb₂ s₂ hs₂]
  exact ⟨hB, hS⟩

/-! ## Section 1: Pure `gmPushSlab` and `SlabBijection` preservation -/

/-- Pure `GlobalMeta` update allocating a new full slab `p_new = gm 0` as the new top slab
`s_new = gm (gmQIdx b)` of bucket `b`. -/
@[expose]
def gmPushSlab (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let q_b := gm (gmQIdx b)
  let p_new := gm 0
  let top_old := gm (gmSlabTopIdx b)
  let gm₁ := Function.update
    (Function.update
      (Function.update gm (gmSlabOwnerBIdx n_max p_new) b)
      (gmSlabOwnerSIdx n_max p_new) q_b)
    (gmSlabBelowIdx n_max p_new) top_old
  let gm₂ := if 0 < q_b then Function.update gm₁ (gmSlabAboveIdx n_max top_old) p_new else gm₁
  let gm₃ := if q_b < dirSlabsPerBucket n_max then
    Function.update gm₂ (gmSlabDirIdx n_max b q_b) p_new else gm₂
  Function.update
    (Function.update
      (Function.update gm₃ (gmSlabTopIdx b) p_new)
      (gmQIdx b) (q_b + 1))
    0 (p_new + 1)

/-- Field-by-field description of `gmPushSlab` across all `GlobalMeta` sub-arrays. -/
theorem gmPushSlab_fields {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ} (hb : b < numBuckets n_max) :
    gmPushSlab n_max gm b 0 = gm 0 + 1 ∧
    gmPushSlab n_max gm b 1 = gm 1 ∧
    (∀ b' < numBuckets n_max, gmPushSlab n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ idx, gmTailPtrBase n_max ≤ idx → idx < gmSlabMetaBase n_max →
      gmPushSlab n_max gm b idx = gm idx) ∧
    (∀ b' < numBuckets n_max,
      gmPushSlab n_max gm b (gmQIdx b') =
        if b' = b then gm (gmQIdx b) + 1 else gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmPushSlab n_max gm b (gmSlabTopIdx b') =
        if b' = b then gm 0 else gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmPushSlab n_max gm b (gmSlabDirIdx n_max b' s) =
        if b' = b ∧ s = gm (gmQIdx b) then gm 0 else gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabOwnerBIdx n_max p) =
      if p = gm 0 then b else gm (gmSlabOwnerBIdx n_max p)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabOwnerSIdx n_max p) =
      if p = gm 0 then gm (gmQIdx b) else gm (gmSlabOwnerSIdx n_max p)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabBelowIdx n_max p) =
      if p = gm 0 then gm (gmSlabTopIdx b) else gm (gmSlabBelowIdx n_max p)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabAboveIdx n_max p) =
      if 0 < gm (gmQIdx b) ∧ p = gm (gmSlabTopIdx b) then gm 0
      else gm (gmSlabAboveIdx n_max p)) := by
  have hdir_bound : ∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      b' * dirSlabsPerBucket n_max + s < numBuckets n_max * dirSlabsPerBucket n_max := by
    intro b' hb' s hs
    have h1 : (b' + 1) * dirSlabsPerBucket n_max ≤
        numBuckets n_max * dirSlabsPerBucket n_max := Nat.mul_le_mul_right _ hb'
    nlinarith
  unfold gmPushSlab
  generalize gm (gmQIdx b) = q₀
  generalize gm 0 = p₀
  generalize gm (gmSlabTopIdx b) = t₀
  have hmul_b : q₀ < dirSlabsPerBucket n_max →
      b * dirSlabsPerBucket n_max + q₀ < numBuckets n_max * dirSlabsPerBucket n_max :=
    hdir_bound b hb q₀
  unfold gmQIdx gmRIdx gmSlabTopIdx gmSlabDirIdx gmSlabOwnerBIdx gmSlabOwnerSIdx
    gmSlabBelowIdx gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_self]
  · split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro b' hb'
    split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro idx hlo hhi
    split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro b' hb'
    rw [Function.update_of_ne (by omega)]
    by_cases hbeq : b' = b
    · subst hbeq
      simp only [↓reduceIte]
      rw [Function.update_self]
    · simp only [hbeq, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro b' hb'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    by_cases hbeq : b' = b
    · subst hbeq
      simp only [↓reduceIte]
      rw [Function.update_self]
    · simp only [hbeq, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro b' hb' s hs
    have hmul' := hdir_bound b' hb' s hs
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    by_cases hcond : b' = b ∧ s = q₀
    · rcases hcond with ⟨rfl, rfl⟩
      simp only [and_self, ↓reduceIte, hs]
      rw [Function.update_self]
    · simp only [hcond, ↓reduceIte]
      split_ifs with hq_dir hq_pos
      · have hne_idx : b' * dirSlabsPerBucket n_max + s ≠ b * dirSlabsPerBucket n_max + q₀ := by
          intro heq
          have h1 := mul_add_div_mod_of_lt (b := b') hs
          have h2 := mul_add_div_mod_of_lt (b := b) hq_dir
          exact hcond ⟨by rw [← h1.1, heq, h2.1], by rw [← h1.2, heq, h2.2]⟩
        repeat rw [Function.update_of_ne (by omega)]
      · have hne_idx : b' * dirSlabsPerBucket n_max + s ≠ b * dirSlabsPerBucket n_max + q₀ := by
          intro heq
          have h1 := mul_add_div_mod_of_lt (b := b') hs
          have h2 := mul_add_div_mod_of_lt (b := b) hq_dir
          exact hcond ⟨by rw [← h1.1, heq, h2.1], by rw [← h1.2, heq, h2.2]⟩
        repeat rw [Function.update_of_ne (by omega)]
      · repeat rw [Function.update_of_ne (by omega)]
      · repeat rw [Function.update_of_ne (by omega)]
  · intro p
    by_cases hp : p = p₀
    · subst hp
      simp only [↓reduceIte]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self])
    · simp only [hp, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro p
    by_cases hp : p = p₀
    · subst hp
      simp only [↓reduceIte]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self])
    · simp only [hp, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro p
    by_cases hp : p = p₀
    · subst hp
      simp only [↓reduceIte]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self])
    · simp only [hp, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro p
    by_cases hcond : 0 < q₀ ∧ p = t₀
    · rcases hcond with ⟨hq_pos, rfl⟩
      simp only [hq_pos, true_and, ↓reduceIte]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self])
    · simp only [hcond, ↓reduceIte]
      split_ifs with hq_dir hq_pos
      · have hp_ne : p ≠ t₀ := fun h => hcond ⟨hq_pos, h⟩
        repeat rw [Function.update_of_ne (by omega)]
      · repeat rw [Function.update_of_ne (by omega)]
      · rename_i hq_pos
        have hp_ne : p ≠ t₀ := fun h => hcond ⟨hq_pos, h⟩
        repeat rw [Function.update_of_ne (by omega)]
      · repeat rw [Function.update_of_ne (by omega)]

/-- `gmPushSlab` preserves `TailBijection`. -/
theorem tailBijection_gmPushSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmPushSlab n_max gm b)
      (fun b' => gmPushSlab n_max gm b (gmRIdx b')) (gmPushSlab n_max gm b 1) := by
  have hf := gmPushSlab_fields gm hb
  have hptr_eq : ∀ d < maxTailItems n_max,
      gmPushSlab n_max gm b (gmTailPtrFlatIdx n_max d) = gm (gmTailPtrFlatIdx n_max d) := by
    intro d hd
    exact hf.2.2.2.1 _ (by unfold gmTailPtrFlatIdx; omega)
      (by unfold gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase; omega)
  have hown_eq : ∀ t < maxTailItems n_max,
      gmPushSlab n_max gm b (gmTailOwnerIdx n_max t) = gm (gmTailOwnerIdx n_max t) := by
    intro t ht
    exact hf.2.2.2.1 _ (by unfold gmTailOwnerIdx gmTailOwnerBase; omega)
      (by unfold gmTailOwnerIdx gmSlabMetaBase; omega)
  refine ⟨rfl, by rw [hf.2.1]; exact htail.ntails_le, ?_, ?_, ?_, ?_⟩
  · intro b' hb'; rw [hf.2.2.1 b' hb']; exact htail.r_le b' hb'
  · intro b' hb' r hr
    rw [hf.2.2.1 b' hb'] at hr
    have hr_cap : r < tailCapPerBucket n_max := lt_of_lt_of_le hr (htail.r_le b' hb')
    have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
      unfold maxTailItems
      have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb'
      nlinarith
    rw [gmTailPtrIdx, hptr_eq _ hd_lt, hf.2.1]
    exact htail.ptr_lt b' hb' r hr
  · intro b' hb' r hr
    rw [hf.2.2.1 b' hb'] at hr
    have hr_cap : r < tailCapPerBucket n_max := lt_of_lt_of_le hr (htail.r_le b' hb')
    have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
      unfold maxTailItems
      have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb'
      nlinarith
    have ht_lt : gm (gmTailPtrIdx n_max b' r) < maxTailItems n_max :=
      lt_of_lt_of_le (htail.ptr_lt b' hb' r hr) htail.ntails_le
    rw [gmTailPtrIdx, hptr_eq _ hd_lt, ← gmTailPtrIdx, hown_eq _ ht_lt]
    exact htail.owner_ptr b' hb' r hr
  · intro t ht
    dsimp only
    rw [hf.2.1] at ht
    have ht_cap : t < maxTailItems n_max := lt_of_lt_of_le ht htail.ntails_le
    rw [hown_eq t ht_cap]
    have hv := htail.owner_valid t ht
    dsimp only at hv
    rcases hv with ⟨hb_d, hr_d, hptr_d⟩
    have hr_cap : gm (gmTailOwnerIdx n_max t) % tailCapPerBucket n_max < tailCapPerBucket n_max :=
      lt_of_lt_of_le hr_d (htail.r_le _ hb_d)
    have hd_lt : gm (gmTailOwnerIdx n_max t) < maxTailItems n_max := by
      have hdm := Nat.div_add_mod (gm (gmTailOwnerIdx n_max t)) (tailCapPerBucket n_max)
      rw [Nat.mul_comm] at hdm
      unfold maxTailItems
      have h1 : (gm (gmTailOwnerIdx n_max t) / tailCapPerBucket n_max + 1) *
          tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb_d
      nlinarith
    refine ⟨hb_d, ?_, ?_⟩
    · rw [hf.2.2.1 _ hb_d]; exact hr_d
    · rw [hptr_eq _ hd_lt, hptr_d]

/-- `gmPushSlab` assigns physical slab `gm 0` to `(b, gm (gmQIdx b))` and preserves
`SlabBijection`. -/
theorem slabBijection_gmPushSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hp_lt : gm 0 < maxFullSlabs n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    let gm' := gmPushSlab n_max gm b
    (∀ b' < numBuckets n_max, ∀ s < gm' (gmQIdx b'),
      slabPtrOf n_max gm' b' s =
        if b' = b ∧ s = gm (gmQIdx b) then gm 0 else slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max gm' (fun b' => gm' (gmQIdx b')) (gm' 0) := by
  dsimp only
  have hf := gmPushSlab_fields gm hb
  rcases hf with ⟨h0, _, _, _, hQ, hTop, hDir, hOwnB, hOwnS, hBel, hAbv⟩
  have hinj : ∀ p₁ < gmPushSlab n_max gm b 0, ∀ p₂ < gmPushSlab n_max gm b 0,
      gmPushSlab n_max gm b (gmSlabOwnerBIdx n_max p₁) =
        gmPushSlab n_max gm b (gmSlabOwnerBIdx n_max p₂) →
      gmPushSlab n_max gm b (gmSlabOwnerSIdx n_max p₁) =
        gmPushSlab n_max gm b (gmSlabOwnerSIdx n_max p₂) → p₁ = p₂ := by
    intro p₁ hp₁ p₂ hp₂ heqB heqS
    rw [h0] at hp₁ hp₂
    rw [hOwnB p₁, hOwnB p₂] at heqB
    rw [hOwnS p₁, hOwnS p₂] at heqS
    split_ifs at heqB heqS with h1 h2 h2
    · omega
    · obtain ⟨hb2, hs2, _⟩ := hslab.owner_valid p₂ (by omega)
      subst heqB; omega
    · obtain ⟨hb1, hs1, _⟩ := hslab.owner_valid p₁ (by omega)
      subst heqB; omega
    · obtain ⟨hb1, hs1, hptr1⟩ := hslab.owner_valid p₁ (by omega)
      obtain ⟨hb2, hs2, hptr2⟩ := hslab.owner_valid p₂ (by omega)
      rw [← hptr1, ← hptr2, heqB, heqS]
  have hptr : ∀ b' < numBuckets n_max, ∀ s < gmPushSlab n_max gm b (gmQIdx b'),
      slabPtrOf n_max (gmPushSlab n_max gm b) b' s =
        if b' = b ∧ s = gm (gmQIdx b) then gm 0 else slabPtrOf n_max gm b' s := by
    intro b' hb' s hs
    rw [hQ b' hb'] at hs
    by_cases hcond : b' = b ∧ s = gm (gmQIdx b)
    · rcases hcond with ⟨rfl, rfl⟩
      simp only [and_self, ↓reduceIte]
      refine slabPtrOf_eq_of_owner (by rw [h0]; omega) ?_ ?_ hinj
      · rw [hOwnB (gm 0), ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      · rw [hOwnS (gm 0), ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    · simp only [hcond, ↓reduceIte]
      have hs_old : s < gm (gmQIdx b') := by
        split_ifs at hs with hbeq
        · subst hbeq
          have : s ≠ gm (gmQIdx b') := fun h => hcond ⟨rfl, h⟩
          omega
        · exact hs
      have hp_old : slabPtrOf n_max gm b' s < gm 0 := hslab.ptr_lt b' hb' s hs_old
      refine slabPtrOf_eq_of_owner (by rw [h0]; omega) ?_ ?_ hinj
      · rw [hOwnB, ite_eq_right (by omega)]; exact hslab.ownerB_ptr b' hb' s hs_old
      · rw [hOwnS, ite_eq_right (by omega)]; exact hslab.ownerS_ptr b' hb' s hs_old
  refine ⟨hptr, ?_⟩
  refine ⟨rfl, by rw [h0]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b' hb' s hs
    rw [hptr b' hb' s hs, h0]
    split_ifs with hcond
    · omega
    · rw [hQ b' hb'] at hs
      have hs_old : s < gm (gmQIdx b') := by
        split_ifs at hs with hbeq
        · subst hbeq; have : s ≠ gm (gmQIdx b') := fun h => hcond ⟨rfl, h⟩; omega
        · exact hs
      have := hslab.ptr_lt b' hb' s hs_old
      omega
  · intro b' hb' s hs
    rw [hptr b' hb' s hs]
    split_ifs with hcond
    · rw [hOwnB (gm 0), ite_eq_left_iff.mpr (fun h => absurd rfl h), hcond.1]
    · rw [hQ b' hb'] at hs
      have hs_old : s < gm (gmQIdx b') := by
        split_ifs at hs with hbeq
        · subst hbeq; have : s ≠ gm (gmQIdx b') := fun h => hcond ⟨rfl, h⟩; omega
        · exact hs
      have hp_old := hslab.ptr_lt b' hb' s hs_old
      rw [hOwnB, ite_eq_right (by omega)]
      exact hslab.ownerB_ptr b' hb' s hs_old
  · intro b' hb' s hs
    rw [hptr b' hb' s hs]
    split_ifs with hcond
    · rw [hOwnS (gm 0), ite_eq_left_iff.mpr (fun h => absurd rfl h), hcond.2]
    · rw [hQ b' hb'] at hs
      have hs_old : s < gm (gmQIdx b') := by
        split_ifs at hs with hbeq
        · subst hbeq; have : s ≠ gm (gmQIdx b') := fun h => hcond ⟨rfl, h⟩; omega
        · exact hs
      have hp_old := hslab.ptr_lt b' hb' s hs_old
      rw [hOwnS, ite_eq_right (by omega)]
      exact hslab.ownerS_ptr b' hb' s hs_old
  · intro p hp
    dsimp only
    rw [h0] at hp
    rw [hOwnB p, hOwnS p]
    split_ifs with hp_eq
    · subst hp_eq
      have hq_lt : gm (gmQIdx b) < gmPushSlab n_max gm b (gmQIdx b) := by
        rw [hQ b hb, ite_eq_left_iff.mpr (fun h => absurd rfl h)]; omega
      refine ⟨hb, hq_lt, ?_⟩
      rw [hptr b hb _ hq_lt]
      simp
    · have hp_old : p < gm 0 := by omega
      obtain ⟨hb_p, hs_p, hptr_p⟩ := hslab.owner_valid p hp_old
      have hs_new : gm (gmSlabOwnerSIdx n_max p) <
          gmPushSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max p))) := by
        rw [hQ _ hb_p]
        split_ifs with hbeq
        · rw [hbeq] at hs_p; omega
        · exact hs_p
      refine ⟨hb_p, hs_new, ?_⟩
      rw [hptr _ hb_p _ hs_new, ite_eq_right (by intro ⟨h1, h2⟩; rw [h1, h2] at hs_p; omega),
        hptr_p]
  · intro b' hb' s hs hdir
    rw [hptr b' hb' s hs, hDir b' hb' s hdir]
    split_ifs with hcond
    · rfl
    · rw [hQ b' hb'] at hs
      have hs_old : s < gm (gmQIdx b') := by
        split_ifs at hs with hbeq
        · subst hbeq; have : s ≠ gm (gmQIdx b') := fun h => hcond ⟨rfl, h⟩; omega
        · exact hs
      exact hslab.dir_eq b' hb' s hs_old hdir
  · intro b' hb' s hs htop
    rw [hptr b' hb' s hs, hTop b' hb']
    rw [hQ b' hb'] at hs htop
    by_cases hbeq : b' = b
    · subst hbeq
      simp only [↓reduceIte, true_and] at hs htop ⊢
      have hs_eq : s = gm (gmQIdx b') := by omega
      simp [hs_eq]
    · simp only [hbeq, ↓reduceIte, false_and] at hs htop ⊢
      exact hslab.top_eq b' hb' s hs htop
  · intro b' hb' s hs hpos
    have hs1_lt : s - 1 < gmPushSlab n_max gm b (gmQIdx b') := by omega
    rw [hptr b' hb' s hs, hptr b' hb' (s - 1) hs1_lt]
    rw [hQ b' hb'] at hs
    by_cases hcond : b' = b ∧ s = gm (gmQIdx b)
    · rcases hcond with ⟨rfl, rfl⟩
      have hne1 : ¬(b' = b' ∧ gm (gmQIdx b') - 1 = gm (gmQIdx b')) := by omega
      rw [ite_eq_left_iff.mpr (fun h => absurd ⟨rfl, rfl⟩ h), ite_eq_right hne1]
      rw [hBel (gm 0), ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      exact hslab.top_eq b' hb' (gm (gmQIdx b') - 1) (by omega) (by omega)
    · have hs_old : s < gm (gmQIdx b') := by
        split_ifs at hs with hbeq
        · subst hbeq; have : s ≠ gm (gmQIdx b') := fun h => hcond ⟨rfl, h⟩; omega
        · exact hs
      have hne1 : ¬(b' = b ∧ s - 1 = gm (gmQIdx b)) := by
        rintro ⟨rfl, heq⟩; omega
      simp only [hcond, hne1, ↓reduceIte]
      have hp_old := hslab.ptr_lt b' hb' s hs_old
      rw [hBel, ite_eq_right (by omega)]
      exact hslab.below_eq b' hb' s hs_old hpos
  · intro b' hb' s hs habv
    have hs1_lt : s + 1 < gmPushSlab n_max gm b (gmQIdx b') := habv
    rw [hptr b' hb' s hs, hptr b' hb' (s + 1) hs1_lt]
    rw [hQ b' hb'] at hs habv
    have hnot_cond1 : ¬(b' = b ∧ s = gm (gmQIdx b)) := by
      rintro ⟨rfl, rfl⟩
      simp only [↓reduceIte] at habv
      omega
    rw [ite_eq_right hnot_cond1]
    by_cases hcond2 : b' = b ∧ s + 1 = gm (gmQIdx b)
    · rcases hcond2 with ⟨rfl, heq⟩
      simp only [and_self, heq, ↓reduceIte]
      have hs_old : s < gm (gmQIdx b') := by omega
      have htop_old : gm (gmSlabTopIdx b') = slabPtrOf n_max gm b' s :=
        hslab.top_eq b' hb' s hs_old heq
      rw [hAbv, ite_eq_left_iff.mpr (fun h => absurd ⟨by omega, htop_old.symm⟩ h)]
    · rw [ite_eq_right hcond2]
      have hs1_old : s + 1 < gm (gmQIdx b') := by
        split_ifs at habv with hbeq
        · subst hbeq
          have : s + 1 ≠ gm (gmQIdx b') := fun h => hcond2 ⟨rfl, h⟩
          omega
        · exact habv
      have hs_old : s < gm (gmQIdx b') := by omega
      have hne_top : ¬(0 < gm (gmQIdx b) ∧ slabPtrOf n_max gm b' s = gm (gmSlabTopIdx b)) := by
        rintro ⟨hq_pos, heq_p⟩
        have htop_b := hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)
        rw [htop_b] at heq_p
        obtain ⟨rfl, heq_s⟩ := slabPtrOf_inj hslab hb' hs_old hb (by omega) heq_p
        omega
      rw [hAbv, ite_eq_right hne_top]
      exact hslab.above_eq b' hb' s hs_old hs1_old

/-! ## Section 2: Pure `gmUnlinkTopSlab`, `gmCompactSlab`, `gmPopSlab` and `SlabBijection` -/

/-- Stage A of slab pop: unlink the top slab `p_del = gm (gmSlabTopIdx b)` of bucket `b` by setting
`gmSlabTopIdx b ↦ gm (gmSlabBelowIdx n_max p_del)` and decrementing `gmQIdx b`. -/
@[expose]
def gmUnlinkTopSlab (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let q_b := gm (gmQIdx b)
  let p_del := gm (gmSlabTopIdx b)
  let p_below := gm (gmSlabBelowIdx n_max p_del)
  Function.update
    (Function.update gm (gmSlabTopIdx b) p_below)
    (gmQIdx b) (q_b - 1)

/-- Stage B of slab pop: compact the physical slab pool by relocating `p_last = gmA 0 - 1` into the
vacated physical slab `p_del` (when `p_del < p_last`) and decrementing `gmA 0`. -/
@[expose]
def gmCompactSlab (n_max : ℕ) (gmA : ℕ → ℕ) (p_del : ℕ) : ℕ → ℕ :=
  let p_last := gmA 0 - 1
  if p_del < p_last then
    let b_last := gmA (gmSlabOwnerBIdx n_max p_last)
    let s_last := gmA (gmSlabOwnerSIdx n_max p_last)
    let bel_last := gmA (gmSlabBelowIdx n_max p_last)
    let abv_last := gmA (gmSlabAboveIdx n_max p_last)
    let q_last := gmA (gmQIdx b_last)
    let gm₁ := if s_last < dirSlabsPerBucket n_max then
      Function.update gmA (gmSlabDirIdx n_max b_last s_last) p_del else gmA
    let gm₂ := if s_last + 1 = q_last then
      Function.update gm₁ (gmSlabTopIdx b_last) p_del else gm₁
    let gm₃ := if 0 < s_last then
      Function.update gm₂ (gmSlabAboveIdx n_max bel_last) p_del else gm₂
    let gm₄ := if s_last + 1 < q_last then
      Function.update gm₃ (gmSlabBelowIdx n_max abv_last) p_del else gm₃
    let gm₅ := Function.update
      (Function.update
        (Function.update
          (Function.update gm₄ (gmSlabOwnerBIdx n_max p_del) b_last)
          (gmSlabOwnerSIdx n_max p_del) s_last)
        (gmSlabBelowIdx n_max p_del) bel_last)
      (gmSlabAboveIdx n_max p_del) abv_last
    Function.update gm₅ 0 p_last
  else
    Function.update gmA 0 p_last

/-- Pure `GlobalMeta` update popping the top slab of bucket `b` and compacting the physical slab
pool. -/
@[expose]
def gmPopSlab (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  gmCompactSlab n_max (gmUnlinkTopSlab n_max gm b) (gm (gmSlabTopIdx b))

/-- Field-by-field description of `gmUnlinkTopSlab` (Stage A of slab pop). -/
theorem gmUnlinkTopSlab_fields {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ} (hb : b < numBuckets n_max) :
    gmUnlinkTopSlab n_max gm b 0 = gm 0 ∧
    gmUnlinkTopSlab n_max gm b 1 = gm 1 ∧
    (∀ b' < numBuckets n_max, gmUnlinkTopSlab n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmUnlinkTopSlab n_max gm b (gmQIdx b') =
        if b' = b then gm (gmQIdx b) - 1 else gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmUnlinkTopSlab n_max gm b (gmSlabTopIdx b') =
        if b' = b then gm (gmSlabBelowIdx n_max (gm (gmSlabTopIdx b)))
        else gm (gmSlabTopIdx b')) ∧
    (∀ idx, gmSlabDirBase n_max ≤ idx → gmUnlinkTopSlab n_max gm b idx = gm idx) ∧
    (∀ b' s, slabPtrOf n_max (gmUnlinkTopSlab n_max gm b) b' s = slabPtrOf n_max gm b' s) := by
  have hge : gmSlabDirBase n_max ≤ gmSlabMetaBase n_max := by
    unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' _; unfold gmUnlinkTopSlab gmQIdx gmRIdx gmSlabTopIdx
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' _
    unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx
    split_ifs with hbeq
    · subst hbeq; rw [Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' _
    unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx
    rw [Function.update_of_ne (by omega)]
    split_ifs with hbeq
    · subst hbeq; rw [Function.update_self]
    · rw [Function.update_of_ne (by omega)]
  · intro idx hidx
    unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx
    unfold gmSlabDirBase at hidx
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' s
    refine slabPtrOf_congr ?_ ?_ ?_ b' s
    · unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro p _
      unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx gmSlabOwnerBIdx gmSlabMetaBase
        gmTailOwnerBase gmTailPtrBase gmSlabDirBase
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · intro p _
      unfold gmUnlinkTopSlab gmQIdx gmSlabTopIdx gmSlabOwnerSIdx gmSlabMetaBase
        gmTailOwnerBase gmTailPtrBase gmSlabDirBase
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- Field-by-field description of `gmCompactSlab` when `p_del < gmA 0 - 1` (Stage B of slab pop). -/
theorem gmCompactSlab_fields_lt {n_max : ℕ} (gmA : ℕ → ℕ) {p_del : ℕ}
    (hlt : p_del < gmA 0 - 1)
    (hb_last : gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)) < numBuckets n_max) :
    let p_last := gmA 0 - 1
    let b_last := gmA (gmSlabOwnerBIdx n_max p_last)
    let s_last := gmA (gmSlabOwnerSIdx n_max p_last)
    let bel_last := gmA (gmSlabBelowIdx n_max p_last)
    let abv_last := gmA (gmSlabAboveIdx n_max p_last)
    let q_last := gmA (gmQIdx b_last)
    gmCompactSlab n_max gmA p_del 0 = p_last ∧
    gmCompactSlab n_max gmA p_del 1 = gmA 1 ∧
    (∀ b' < numBuckets n_max, gmCompactSlab n_max gmA p_del (gmRIdx b') = gmA (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmCompactSlab n_max gmA p_del (gmQIdx b') = gmA (gmQIdx b')) ∧
    (∀ idx, gmTailPtrBase n_max ≤ idx → idx < gmSlabMetaBase n_max →
      gmCompactSlab n_max gmA p_del idx = gmA idx) ∧
    (∀ b' < numBuckets n_max,
      gmCompactSlab n_max gmA p_del (gmSlabTopIdx b') =
        if b' = b_last ∧ s_last + 1 = q_last then p_del else gmA (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmCompactSlab n_max gmA p_del (gmSlabDirIdx n_max b' s) =
        if b' = b_last ∧ s = s_last then p_del else gmA (gmSlabDirIdx n_max b' s)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabOwnerBIdx n_max p) =
      if p = p_del then b_last else gmA (gmSlabOwnerBIdx n_max p)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabOwnerSIdx n_max p) =
      if p = p_del then s_last else gmA (gmSlabOwnerSIdx n_max p)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabBelowIdx n_max p) =
      if p = p_del then bel_last
      else if s_last + 1 < q_last ∧ p = abv_last then p_del
      else gmA (gmSlabBelowIdx n_max p)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabAboveIdx n_max p) =
      if p = p_del then abv_last
      else if 0 < s_last ∧ p = bel_last then p_del
      else gmA (gmSlabAboveIdx n_max p)) := by
  dsimp only
  have hdir_bound : ∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      b' * dirSlabsPerBucket n_max + s < numBuckets n_max * dirSlabsPerBucket n_max := by
    intro b' hb' s hs
    have h1 : (b' + 1) * dirSlabsPerBucket n_max ≤
        numBuckets n_max * dirSlabsPerBucket n_max := Nat.mul_le_mul_right _ hb'
    nlinarith
  unfold gmCompactSlab
  rw [ite_eq_left_iff.mpr (fun h => absurd hlt h)]
  generalize gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)) = b₀ at hb_last ⊢
  generalize gmA (gmSlabOwnerSIdx n_max (gmA 0 - 1)) = s₀
  generalize gmA (gmSlabBelowIdx n_max (gmA 0 - 1)) = bel₀
  generalize gmA (gmSlabAboveIdx n_max (gmA 0 - 1)) = abv₀
  generalize gmA (gmQIdx b₀) = q₀
  generalize gmA 0 - 1 = p_last
  have hmul_b : s₀ < dirSlabsPerBucket n_max →
      b₀ * dirSlabsPerBucket n_max + s₀ < numBuckets n_max * dirSlabsPerBucket n_max :=
    hdir_bound b₀ hb_last s₀
  unfold gmQIdx gmRIdx gmSlabTopIdx gmSlabDirIdx gmSlabOwnerBIdx gmSlabOwnerSIdx
    gmSlabBelowIdx gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_self]
  · split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro b' _
    split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro b' _
    split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro idx hlo hhi
    split_ifs <;>
    repeat rw [Function.update_of_ne (by omega)]
  · intro b' hb'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    by_cases hcond : b' = b₀ ∧ s₀ + 1 = q₀
    · rcases hcond with ⟨rfl, htop⟩
      simp only [htop, and_self, ↓reduceIte]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self] | omega)
    · simp only [hcond, ↓reduceIte]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rfl)
  · intro b' hb' s hs
    have hmul' := hdir_bound b' hb' s hs
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    by_cases hcond : b' = b₀ ∧ s = s₀
    · rcases hcond with ⟨rfl, rfl⟩
      simp only [and_self, ↓reduceIte, hs]
      split_ifs <;>
      repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self] | omega)
    · simp only [hcond, ↓reduceIte]
      by_cases hs_dir : s₀ < dirSlabsPerBucket n_max
      · have hne_idx : b' * dirSlabsPerBucket n_max + s ≠ b₀ * dirSlabsPerBucket n_max + s₀ := by
          intro heq
          have h1 := mul_add_div_mod_of_lt (b := b') hs
          have h2 := mul_add_div_mod_of_lt (b := b₀) hs_dir
          exact hcond ⟨by rw [← h1.1, heq, h2.1], by rw [← h1.2, heq, h2.2]⟩
        simp only [hs_dir, ↓reduceIte]
        split_ifs <;>
        repeat rw [Function.update_of_ne (by omega)]
      · simp only [hs_dir, ↓reduceIte]
        split_ifs <;>
        repeat (first | rw [Function.update_of_ne (by omega)] | rfl)
  · intro p
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    by_cases hp : p = p_del
    · subst hp; simp [Function.update_self]
    · simp only [hp, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro p
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    by_cases hp : p = p_del
    · subst hp; simp [Function.update_self]
    · simp only [hp, ↓reduceIte]
      split_ifs <;>
      repeat rw [Function.update_of_ne (by omega)]
  · intro p
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    by_cases hp : p = p_del
    · subst hp; simp [Function.update_self]
    · simp only [hp, ↓reduceIte]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      by_cases hcond : s₀ + 1 < q₀ ∧ p = abv₀
      · rcases hcond with ⟨habv, rfl⟩
        simp only [habv, and_self, ↓reduceIte]
        rw [Function.update_self]
      · simp only [hcond, ↓reduceIte]
        split_ifs <;>
        repeat (first | rw [Function.update_of_ne (by omega)] | rfl)
  · intro p
    rw [Function.update_of_ne (by omega)]
    by_cases hp : p = p_del
    · subst hp; simp [Function.update_self]
    · simp only [hp, ↓reduceIte]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      by_cases hcond : 0 < s₀ ∧ p = bel₀
      · rcases hcond with ⟨hbel, rfl⟩
        simp only [hbel, and_self, ↓reduceIte]
        split_ifs <;>
        repeat (first | rw [Function.update_of_ne (by omega)] | rw [Function.update_self] | omega)
      · simp only [hcond, ↓reduceIte]
        split_ifs <;>
        repeat (first | rw [Function.update_of_ne (by omega)] | rfl)

/-- `gmPopSlab` decrements `gm 0` and `gm (gmQIdx b)` while preserving all tail fields. -/
theorem gmPopSlab_preserves_tail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    gmPopSlab n_max gm b 0 = gm 0 - 1 ∧
    gmPopSlab n_max gm b 1 = gm 1 ∧
    (∀ b' < numBuckets n_max, gmPopSlab n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmPopSlab n_max gm b (gmQIdx b') =
        if b' = b then gm (gmQIdx b) - 1 else gm (gmQIdx b')) ∧
    (∀ idx, gmTailPtrBase n_max ≤ idx → idx < gmSlabMetaBase n_max →
      gmPopSlab n_max gm b idx = gm idx) := by
  have hu := gmUnlinkTopSlab_fields gm hb
  unfold gmPopSlab
  by_cases hlt : gm (gmSlabTopIdx b) < gmUnlinkTopSlab n_max gm b 0 - 1
  · have hp_last_lt : gm 0 - 1 < gm 0 := by rw [hu.1] at hlt; omega
    have hb_last : gmUnlinkTopSlab n_max gm b
        (gmSlabOwnerBIdx n_max (gmUnlinkTopSlab n_max gm b 0 - 1)) < numBuckets n_max := by
      rw [hu.1, hu.2.2.2.2.2.1 _
        (by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega)]
      exact (hslab.owner_valid (gm 0 - 1) hp_last_lt).1
    have hc := gmCompactSlab_fields_lt (gmUnlinkTopSlab n_max gm b) hlt hb_last
    refine ⟨by rw [hc.1, hu.1], by rw [hc.2.1, hu.2.1],
      fun b' hb' => by rw [hc.2.2.1 b' hb', hu.2.2.1 b' hb'],
      fun b' hb' => by rw [hc.2.2.2.1 b' hb', hu.2.2.2.1 b' hb'],
      fun idx hlo hhi => by
        rw [hc.2.2.2.2.1 idx hlo hhi, hu.2.2.2.2.2.1 idx (by unfold gmTailPtrBase at hlo; omega)]⟩
  · unfold gmCompactSlab
    rw [ite_eq_right hlt]
    refine ⟨by rw [Function.update_self, hu.1],
      by rw [Function.update_of_ne (by decide), hu.2.1],
      fun b' hb' => by rw [Function.update_of_ne (by unfold gmRIdx; omega), hu.2.2.1 b' hb'],
      fun b' hb' => by rw [Function.update_of_ne (by unfold gmQIdx; omega), hu.2.2.2.1 b' hb'],
      fun idx hlo _ => by
        rw [Function.update_of_ne (by unfold gmTailPtrBase gmSlabDirBase at hlo; omega),
          hu.2.2.2.2.2.1 idx (by unfold gmTailPtrBase at hlo; omega)]⟩

/-- `gmPopSlab` preserves `TailBijection`. -/
theorem tailBijection_gmPopSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmPopSlab n_max gm b)
      (fun b' => gmPopSlab n_max gm b (gmRIdx b')) (gmPopSlab n_max gm b 1) := by
  have hp := gmPopSlab_preserves_tail hb hslab
  have hptr_eq : ∀ d < maxTailItems n_max,
      gmPopSlab n_max gm b (gmTailPtrFlatIdx n_max d) = gm (gmTailPtrFlatIdx n_max d) := by
    intro d hd
    exact hp.2.2.2.2 _ (by unfold gmTailPtrFlatIdx; omega)
      (by unfold gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase; omega)
  have hown_eq : ∀ t < maxTailItems n_max,
      gmPopSlab n_max gm b (gmTailOwnerIdx n_max t) = gm (gmTailOwnerIdx n_max t) := by
    intro t ht
    exact hp.2.2.2.2 _ (by unfold gmTailOwnerIdx gmTailOwnerBase; omega)
      (by unfold gmTailOwnerIdx gmSlabMetaBase; omega)
  refine ⟨rfl, by rw [hp.2.1]; exact htail.ntails_le, ?_, ?_, ?_, ?_⟩
  · intro b' hb'; rw [hp.2.2.1 b' hb']; exact htail.r_le b' hb'
  · intro b' hb' r hr
    rw [hp.2.2.1 b' hb'] at hr
    have hr_cap : r < tailCapPerBucket n_max := lt_of_lt_of_le hr (htail.r_le b' hb')
    have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
      unfold maxTailItems
      have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb'
      nlinarith
    rw [gmTailPtrIdx, hptr_eq _ hd_lt, hp.2.1]
    exact htail.ptr_lt b' hb' r hr
  · intro b' hb' r hr
    rw [hp.2.2.1 b' hb'] at hr
    have hr_cap : r < tailCapPerBucket n_max := lt_of_lt_of_le hr (htail.r_le b' hb')
    have hd_lt : b' * tailCapPerBucket n_max + r < maxTailItems n_max := by
      unfold maxTailItems
      have h1 : (b' + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb'
      nlinarith
    have ht_lt : gm (gmTailPtrIdx n_max b' r) < maxTailItems n_max :=
      lt_of_lt_of_le (htail.ptr_lt b' hb' r hr) htail.ntails_le
    rw [gmTailPtrIdx, hptr_eq _ hd_lt, ← gmTailPtrIdx, hown_eq _ ht_lt]
    exact htail.owner_ptr b' hb' r hr
  · intro t ht
    dsimp only
    rw [hp.2.1] at ht
    have ht_cap : t < maxTailItems n_max := lt_of_lt_of_le ht htail.ntails_le
    rw [hown_eq t ht_cap]
    have hv := htail.owner_valid t ht
    dsimp only at hv
    rcases hv with ⟨hb_d, hr_d, hptr_d⟩
    have hr_cap : gm (gmTailOwnerIdx n_max t) % tailCapPerBucket n_max < tailCapPerBucket n_max :=
      lt_of_lt_of_le hr_d (htail.r_le _ hb_d)
    have hd_lt : gm (gmTailOwnerIdx n_max t) < maxTailItems n_max := by
      have hdm := Nat.div_add_mod (gm (gmTailOwnerIdx n_max t)) (tailCapPerBucket n_max)
      rw [Nat.mul_comm] at hdm
      unfold maxTailItems
      have h1 : (gm (gmTailOwnerIdx n_max t) / tailCapPerBucket n_max + 1) *
          tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
        Nat.mul_le_mul_right _ hb_d
      nlinarith
    refine ⟨hb_d, ?_, ?_⟩
    · rw [hp.2.2.1 _ hb_d]; exact hr_d
    · rw [hptr_eq _ hd_lt, hptr_d]

/-- `gmPopSlab` relocates the last physical slab `gm 0 - 1` into `gm (gmSlabTopIdx b)` and
preserves `SlabBijection`. -/
theorem slabBijection_gmPopSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hq_pos : 1 ≤ gm (gmQIdx b))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
      slabPtrOf n_max (gmPopSlab n_max gm b) b' s =
        if slabPtrOf n_max gm b' s = gm 0 - 1 then gm (gmSlabTopIdx b)
        else slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmPopSlab n_max gm b)
      (fun b' => gmPopSlab n_max gm b (gmQIdx b')) (gmPopSlab n_max gm b 0) := by
  have hu := gmUnlinkTopSlab_fields gm hb
  rcases hu with ⟨hu0, _, _, huQ, huTop, huGe, huPtr⟩
  have htop_b : gm (gmSlabTopIdx b) = slabPtrOf n_max gm b (gm (gmQIdx b) - 1) :=
    hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)
  have hp_del_lt : gm (gmSlabTopIdx b) < gm 0 := by
    rw [htop_b]; exact hslab.ptr_lt b hb (gm (gmQIdx b) - 1) (by omega)
  have hs_old_of_new : ∀ b' < numBuckets n_max,
      ∀ s < gmUnlinkTopSlab n_max gm b (gmQIdx b'),
      s < gm (gmQIdx b') ∧ slabPtrOf n_max gm b' s ≠ gm (gmSlabTopIdx b) := by
    intro b' hb' s hs
    rw [huQ b' hb'] at hs
    have hs_old : s < gm (gmQIdx b') := by
      split_ifs at hs with hbeq
      · subst hbeq; omega
      · exact hs
    refine ⟨hs_old, ?_⟩
    intro heq
    rw [htop_b] at heq
    obtain ⟨rfl, hs_eq⟩ := slabPtrOf_inj hslab hb' hs_old hb (by omega) heq
    simp only [↓reduceIte] at hs
    omega
  have hB_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabOwnerBIdx n_max p :=
    fun _ => by unfold gmSlabOwnerBIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hS_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabOwnerSIdx n_max p :=
    fun _ => by unfold gmSlabOwnerSIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hBel_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabBelowIdx n_max p :=
    fun _ => by unfold gmSlabBelowIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hAbv_ge : ∀ p, gmSlabDirBase n_max ≤ gmSlabAboveIdx n_max p :=
    fun _ => by unfold gmSlabAboveIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase; omega
  have hDir_ge : ∀ b' s, gmSlabDirBase n_max ≤ gmSlabDirIdx n_max b' s :=
    fun _ _ => by unfold gmSlabDirIdx; omega
  by_cases hlt : gm (gmSlabTopIdx b) < gm 0 - 1
  · have hlt' : gm (gmSlabTopIdx b) < gmUnlinkTopSlab n_max gm b 0 - 1 := by rwa [hu0]
    have hp_last_lt : gm 0 - 1 < gm 0 := by omega
    obtain ⟨hb_last, hs_last_old, hptr_last⟩ := hslab.owner_valid (gm 0 - 1) hp_last_lt
    have hb_last' : gmUnlinkTopSlab n_max gm b
        (gmSlabOwnerBIdx n_max (gmUnlinkTopSlab n_max gm b 0 - 1)) < numBuckets n_max := by
      rw [hu0, huGe _ (hB_ge _)]; exact hb_last
    have hc := gmCompactSlab_fields_lt (gmUnlinkTopSlab n_max gm b) hlt' hb_last'
    dsimp only at hc
    rw [hu0, huGe _ (hB_ge _), huGe _ (hS_ge _), huGe _ (hBel_ge _), huGe _ (hAbv_ge _)] at hc
    rcases hc with ⟨hc0, _, _, hcQ, _, hcTop, hcDir, hcOwnB, hcOwnS, hcBel, hcAbv⟩
    change gmPopSlab n_max gm b 0 = _ at hc0
    change ∀ b' < numBuckets n_max, gmPopSlab n_max gm b (gmQIdx b') = _ at hcQ
    change ∀ b' < numBuckets n_max, gmPopSlab n_max gm b (gmSlabTopIdx b') = _ at hcTop
    change ∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmPopSlab n_max gm b (gmSlabDirIdx n_max b' s) = _ at hcDir
    change ∀ p, gmPopSlab n_max gm b (gmSlabOwnerBIdx n_max p) = _ at hcOwnB
    change ∀ p, gmPopSlab n_max gm b (gmSlabOwnerSIdx n_max p) = _ at hcOwnS
    change ∀ p, gmPopSlab n_max gm b (gmSlabBelowIdx n_max p) = _ at hcBel
    change ∀ p, gmPopSlab n_max gm b (gmSlabAboveIdx n_max p) = _ at hcAbv
    have hs_last_new : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) <
        gmUnlinkTopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) := by
      rw [huQ _ hb_last]
      split_ifs with hbeq
      · have hne : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) ≠ gm (gmQIdx b) - 1 := by
          intro heq
          have : gm 0 - 1 = gm (gmSlabTopIdx b) := by
            rw [← hptr_last, htop_b, hbeq, heq]
          omega
        have hs_b : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) < gm (gmQIdx b) := by
          rwa [hbeq] at hs_last_old
        omega
      · exact hs_last_old
    have hinj : ∀ p₁ < gmPopSlab n_max gm b 0, ∀ p₂ < gmPopSlab n_max gm b 0,
        gmPopSlab n_max gm b (gmSlabOwnerBIdx n_max p₁) =
          gmPopSlab n_max gm b (gmSlabOwnerBIdx n_max p₂) →
        gmPopSlab n_max gm b (gmSlabOwnerSIdx n_max p₁) =
          gmPopSlab n_max gm b (gmSlabOwnerSIdx n_max p₂) → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ heqB heqS
      rw [hc0] at hp₁ hp₂
      rw [hcOwnB p₁, hcOwnB p₂] at heqB
      rw [hcOwnS p₁, hcOwnS p₂] at heqS
      rw [huGe _ (hB_ge p₁), huGe _ (hB_ge p₂)] at heqB
      rw [huGe _ (hS_ge p₁), huGe _ (hS_ge p₂)] at heqS
      split_ifs at heqB heqS with h1 h2 h2
      · omega
      · obtain ⟨hb2, hs2, hptr2⟩ := hslab.owner_valid p₂ (by omega)
        have : gm 0 - 1 = p₂ := by rw [← hptr_last, heqB, heqS, hptr2]
        omega
      · obtain ⟨hb1, hs1, hptr1⟩ := hslab.owner_valid p₁ (by omega)
        have : gm 0 - 1 = p₁ := by rw [← hptr_last, ← heqB, ← heqS, hptr1]
        omega
      · obtain ⟨hb1, hs1, hptr1⟩ := hslab.owner_valid p₁ (by omega)
        obtain ⟨hb2, hs2, hptr2⟩ := hslab.owner_valid p₂ (by omega)
        rw [← hptr1, ← hptr2, heqB, heqS]
    have hptr : ∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
        slabPtrOf n_max (gmPopSlab n_max gm b) b' s =
          if slabPtrOf n_max gm b' s = gm 0 - 1 then gm (gmSlabTopIdx b)
          else slabPtrOf n_max gm b' s := by
      intro b' hb' s hs
      rw [hcQ b' hb'] at hs
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      split_ifs with heq_last
      · obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        refine slabPtrOf_eq_of_owner (by rw [hc0]; exact hlt) ?_ ?_ hinj
        · rw [hcOwnB, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        · rw [hcOwnS, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      · have hp_lt_old := hslab.ptr_lt b' hb' s hs_old
        refine slabPtrOf_eq_of_owner (by rw [hc0]; omega) ?_ ?_ hinj
        · rw [hcOwnB, ite_eq_right hne_del, huGe _ (hB_ge _)]
          exact hslab.ownerB_ptr b' hb' s hs_old
        · rw [hcOwnS, ite_eq_right hne_del, huGe _ (hS_ge _)]
          exact hslab.ownerS_ptr b' hb' s hs_old
    refine ⟨hptr, ?_⟩
    refine ⟨rfl, by rw [hc0]; have := hslab.nslabs_le; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b' hb' s hs
      rw [hptr b' hb' s hs, hc0]
      split_ifs with heq_last
      · exact hlt
      · rw [hcQ b' hb'] at hs
        have hs_old := (hs_old_of_new b' hb' s hs).1
        have := hslab.ptr_lt b' hb' s hs_old
        omega
    · intro b' hb' s hs
      rw [hptr b' hb' s hs]
      rw [hcQ b' hb'] at hs
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      split_ifs with heq_last
      · obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        rw [hcOwnB, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      · rw [hcOwnB, ite_eq_right hne_del, huGe _ (hB_ge _)]
        exact hslab.ownerB_ptr b' hb' s hs_old
    · intro b' hb' s hs
      rw [hptr b' hb' s hs]
      rw [hcQ b' hb'] at hs
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      split_ifs with heq_last
      · obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        rw [hcOwnS, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      · rw [hcOwnS, ite_eq_right hne_del, huGe _ (hS_ge _)]
        exact hslab.ownerS_ptr b' hb' s hs_old
    · intro p hp
      dsimp only
      rw [hc0] at hp
      rw [hcOwnB p, hcOwnS p, huGe _ (hB_ge p), huGe _ (hS_ge p)]
      split_ifs with hp_eq
      · subst hp_eq
        have hs_new' : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) <
            gmPopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) := by
          rwa [hcQ _ hb_last]
        refine ⟨hb_last, hs_new', ?_⟩
        rw [hptr _ hb_last _ hs_new', ite_eq_left_iff.mpr (fun h => absurd hptr_last h)]
      · obtain ⟨hb_p, hs_p, hptr_p⟩ := hslab.owner_valid p (by omega)
        have hs_new' : gm (gmSlabOwnerSIdx n_max p) <
            gmPopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max p))) := by
          rw [hcQ _ hb_p, huQ _ hb_p]
          split_ifs with hbeq
          · have : gm (gmSlabOwnerSIdx n_max p) ≠ gm (gmQIdx b) - 1 := by
              intro heq; apply hp_eq; rw [← hptr_p, htop_b, hbeq, heq]
            have hs_b : gm (gmSlabOwnerSIdx n_max p) < gm (gmQIdx b) := by
              rwa [hbeq] at hs_p
            omega
          · exact hs_p
        refine ⟨hb_p, hs_new', ?_⟩
        rw [hptr _ hb_p _ hs_new', hptr_p, ite_eq_right (by omega)]
    · intro b' hb' s hs hdir
      rw [hptr b' hb' s hs, hcDir b' hb' s hdir, huGe _ (hDir_ge b' s)]
      rw [hcQ b' hb'] at hs
      obtain ⟨hs_old, _⟩ := hs_old_of_new b' hb' s hs
      split_ifs with hcond heq_last heq_last
      · rfl
      · exfalso
        rcases hcond with ⟨rfl, rfl⟩
        exact heq_last hptr_last
      · exfalso
        obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        exact hcond ⟨rfl, rfl⟩
      · exact hslab.dir_eq b' hb' s hs_old hdir
    · intro b' hb' s hs htop
      rw [hptr b' hb' s hs, hcTop b' hb']
      rw [hcQ b' hb'] at hs htop
      obtain ⟨hs_old, _⟩ := hs_old_of_new b' hb' s hs
      split_ifs with hcond heq_last heq_last
      · rfl
      · exfalso
        rcases hcond with ⟨rfl, _⟩
        have hs_eq : s = gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) := by omega
        subst hs_eq
        exact heq_last hptr_last
      · exfalso
        obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        exact hcond ⟨rfl, htop⟩
      · rw [huTop b' hb']
        rw [huQ b' hb'] at htop
        split_ifs with hbeq
        · subst hbeq
          simp only [↓reduceIte] at htop
          rw [htop_b, hslab.below_eq b' hb' (gm (gmQIdx b') - 1) (by omega) (by omega)]
          congr 1
          omega
        · simp only [hbeq, ↓reduceIte] at htop
          exact hslab.top_eq b' hb' s hs_old htop
    · intro b' hb' s hs hpos
      have hs1_lt : s - 1 < gmPopSlab n_max gm b (gmQIdx b') := by omega
      rw [hptr b' hb' s hs, hptr b' hb' (s - 1) hs1_lt]
      rw [hcQ b' hb'] at hs hs1_lt
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      obtain ⟨hs1_old, _⟩ := hs_old_of_new b' hb' (s - 1) hs1_lt
      split_ifs with heq_last heq1_last heq1_last
      · exfalso
        obtain ⟨_, heq_s⟩ := slabPtrOf_inj hslab hb' hs_old hb' hs1_old
          (heq_last.trans heq1_last.symm)
        omega
      · obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        rw [hcBel, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        have hbel_eq := hslab.below_eq _ hb' _ hs_old hpos
        rwa [hptr_last] at hbel_eq
      · obtain ⟨rfl, hs_eq⟩ := slabPtrOf_inj hslab hb' hs1_old hb_last hs_last_old
          (heq1_last.trans hptr_last.symm)
        have hlt_q : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) + 1 <
            gmUnlinkTopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) := by
          omega
        have hs1_old' : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) + 1 <
            gm (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) := by omega
        have habv_last := hslab.above_eq _ hb' _ hs_last_old hs1_old'
        rw [hptr_last] at habv_last
        have hs_eq' : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) + 1 = s := by omega
        rw [hs_eq'] at habv_last
        rw [hcBel, ite_eq_right hne_del,
          ite_eq_left_iff.mpr (fun h => absurd ⟨hlt_q, habv_last.symm⟩ h)]
      · have hnot_abv : ¬(gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) + 1 <
            gmUnlinkTopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) ∧
            slabPtrOf n_max gm b' s = gm (gmSlabAboveIdx n_max (gm 0 - 1))) := by
          rintro ⟨hq_lt, heq_p⟩
          have hs_abv_old : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) + 1 <
              gm (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) :=
            (hs_old_of_new _ hb_last _ hq_lt).1
          have habv_eq := hslab.above_eq _ hb_last _ hs_last_old hs_abv_old
          rw [hptr_last] at habv_eq
          rw [habv_eq] at heq_p
          obtain ⟨rfl, hs_eq⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_abv_old heq_p
          have hs1_eq : s - 1 = gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) := by omega
          rw [hs1_eq] at heq1_last
          exact heq1_last hptr_last
        rw [hcBel, ite_eq_right hne_del, ite_eq_right hnot_abv, huGe _ (hBel_ge _)]
        exact hslab.below_eq b' hb' s hs_old hpos
    · intro b' hb' s hs habv
      have hs1_lt : s + 1 < gmPopSlab n_max gm b (gmQIdx b') := habv
      rw [hptr b' hb' s hs, hptr b' hb' (s + 1) hs1_lt]
      rw [hcQ b' hb'] at hs hs1_lt
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      obtain ⟨hs1_old, _⟩ := hs_old_of_new b' hb' (s + 1) hs1_lt
      split_ifs with heq_last heq1_last heq1_last
      · exfalso
        obtain ⟨_, heq_s⟩ := slabPtrOf_inj hslab hb' hs_old hb' hs1_old
          (heq_last.trans heq1_last.symm)
        omega
      · obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_last_old
          (heq_last.trans hptr_last.symm)
        rw [hcAbv, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
        have habv_eq := hslab.above_eq _ hb' _ hs_old hs1_old
        rwa [hptr_last] at habv_eq
      · obtain ⟨rfl, hs_eq⟩ := slabPtrOf_inj hslab hb' hs1_old hb_last hs_last_old
          (heq1_last.trans hptr_last.symm)
        have hpos_s : 0 < gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) := by omega
        have hbel_last := hslab.below_eq _ hb' _ hs_last_old hpos_s
        rw [hptr_last] at hbel_last
        have hs_eq' : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) - 1 = s := by omega
        rw [hs_eq'] at hbel_last
        rw [hcAbv, ite_eq_right hne_del,
          ite_eq_left_iff.mpr (fun h => absurd ⟨hpos_s, hbel_last.symm⟩ h)]
      · have hnot_bel : ¬(0 < gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) ∧
            slabPtrOf n_max gm b' s = gm (gmSlabBelowIdx n_max (gm 0 - 1))) := by
          rintro ⟨hpos_s, heq_p⟩
          have hs_bel_old : gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) - 1 <
              gm (gmQIdx (gm (gmSlabOwnerBIdx n_max (gm 0 - 1)))) := by omega
          have hbel_eq := hslab.below_eq _ hb_last _ hs_last_old hpos_s
          rw [hptr_last] at hbel_eq
          rw [hbel_eq] at heq_p
          obtain ⟨rfl, hs_eq⟩ := slabPtrOf_inj hslab hb' hs_old hb_last hs_bel_old heq_p
          have hs1_eq : s + 1 = gm (gmSlabOwnerSIdx n_max (gm 0 - 1)) := by omega
          rw [hs1_eq] at heq1_last
          exact heq1_last hptr_last
        rw [hcAbv, ite_eq_right hne_del, ite_eq_right hnot_bel, huGe _ (hAbv_ge _)]
        exact hslab.above_eq b' hb' s hs_old hs1_old
  · have hp_del_eq : gm (gmSlabTopIdx b) = gm 0 - 1 := by omega
    have hlt' : ¬(gm (gmSlabTopIdx b) < gmUnlinkTopSlab n_max gm b 0 - 1) := by
      rw [hu0]; exact hlt
    have hpop_eq : gmPopSlab n_max gm b =
        Function.update (gmUnlinkTopSlab n_max gm b) 0 (gm 0 - 1) := by
      unfold gmPopSlab gmCompactSlab
      rw [ite_eq_right hlt', hu0]
    have hptr : ∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
        slabPtrOf n_max (gmPopSlab n_max gm b) b' s =
          if slabPtrOf n_max gm b' s = gm 0 - 1 then gm (gmSlabTopIdx b)
          else slabPtrOf n_max gm b' s := by
      intro b' hb' s hs
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      have hne_last : slabPtrOf n_max gm b' s ≠ gm 0 - 1 := by rwa [← hp_del_eq]
      rw [ite_eq_right hne_last]
      have hp_lt_old := hslab.ptr_lt b' hb' s hs_old
      refine slabPtrOf_eq_of_owner
        (by rw [hpop_eq, Function.update_self]; omega)
        (by
          rw [hpop_eq, Function.update_of_ne
            (by have := hB_ge (slabPtrOf n_max gm b' s); unfold gmSlabDirBase at this; omega),
            huGe _ (hB_ge _)]
          exact hslab.ownerB_ptr b' hb' s hs_old)
        (by
          rw [hpop_eq, Function.update_of_ne
            (by have := hS_ge (slabPtrOf n_max gm b' s); unfold gmSlabDirBase at this; omega),
            huGe _ (hS_ge _)]
          exact hslab.ownerS_ptr b' hb' s hs_old) ?_
      intro p₁ hp₁ p₂ hp₂ heqB heqS
      rw [hpop_eq, Function.update_self] at hp₁ hp₂
      rw [hpop_eq, Function.update_of_ne (by have := hB_ge p₁; unfold gmSlabDirBase at this; omega),
        Function.update_of_ne (by have := hB_ge p₂; unfold gmSlabDirBase at this; omega),
        huGe _ (hB_ge p₁), huGe _ (hB_ge p₂)] at heqB
      rw [hpop_eq, Function.update_of_ne (by have := hS_ge p₁; unfold gmSlabDirBase at this; omega),
        Function.update_of_ne (by have := hS_ge p₂; unfold gmSlabDirBase at this; omega),
        huGe _ (hS_ge p₁), huGe _ (hS_ge p₂)] at heqS
      obtain ⟨_, _, hptr1⟩ := hslab.owner_valid p₁ (by omega)
      obtain ⟨_, _, hptr2⟩ := hslab.owner_valid p₂ (by omega)
      rw [← hptr1, ← hptr2, heqB, heqS]
    have hptr_simpl : ∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
        slabPtrOf n_max (gmPopSlab n_max gm b) b' s = slabPtrOf n_max gm b' s := by
      intro b' hb' s hs
      rw [hptr b' hb' s hs]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      have hne_del := (hs_old_of_new b' hb' s hs).2
      rw [hp_del_eq] at hne_del
      exact ite_eq_right hne_del
    refine ⟨hptr, ?_⟩
    refine ⟨rfl, by rw [hpop_eq, Function.update_self]; have := hslab.nslabs_le; omega,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b' hb' s hs
      rw [hptr_simpl b' hb' s hs, hpop_eq, Function.update_self]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      obtain ⟨hs_old, hne_del⟩ := hs_old_of_new b' hb' s hs
      have hp_lt_old := hslab.ptr_lt b' hb' s hs_old
      omega
    · intro b' hb' s hs
      rw [hptr_simpl b' hb' s hs, hpop_eq,
        Function.update_of_ne
          (by have := hB_ge (slabPtrOf n_max gm b' s); unfold gmSlabDirBase at this; omega),
        huGe _ (hB_ge _)]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      exact hslab.ownerB_ptr b' hb' s (hs_old_of_new b' hb' s hs).1
    · intro b' hb' s hs
      rw [hptr_simpl b' hb' s hs, hpop_eq,
        Function.update_of_ne
          (by have := hS_ge (slabPtrOf n_max gm b' s); unfold gmSlabDirBase at this; omega),
        huGe _ (hS_ge _)]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      exact hslab.ownerS_ptr b' hb' s (hs_old_of_new b' hb' s hs).1
    · intro p hp
      dsimp only
      rw [hpop_eq, Function.update_self] at hp
      have hp_ne_del : p ≠ gm (gmSlabTopIdx b) := by omega
      have hB_eq :
          gmPopSlab n_max gm b (gmSlabOwnerBIdx n_max p) = gm (gmSlabOwnerBIdx n_max p) := by
        rw [hpop_eq,
          Function.update_of_ne (by have := hB_ge p; unfold gmSlabDirBase at this; omega),
          huGe _ (hB_ge p)]
      have hS_eq :
          gmPopSlab n_max gm b (gmSlabOwnerSIdx n_max p) = gm (gmSlabOwnerSIdx n_max p) := by
        rw [hpop_eq,
          Function.update_of_ne (by have := hS_ge p; unfold gmSlabDirBase at this; omega),
          huGe _ (hS_ge p)]
      rw [hB_eq, hS_eq]
      obtain ⟨hb_p, hs_p, hptr_p⟩ := hslab.owner_valid p (by omega)
      have hs_new' : gm (gmSlabOwnerSIdx n_max p) <
          gmPopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max p))) := by
        rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega), huQ _ hb_p]
        split_ifs with hbeq
        · have : gm (gmSlabOwnerSIdx n_max p) ≠ gm (gmQIdx b) - 1 := by
            intro heq; apply hp_ne_del; rw [← hptr_p, htop_b, hbeq, heq]
          have hs_b : gm (gmSlabOwnerSIdx n_max p) < gm (gmQIdx b) := by
            rwa [hbeq] at hs_p
          omega
        · exact hs_p
      refine ⟨hb_p, hs_new', ?_⟩
      rw [hptr_simpl _ hb_p _ hs_new', hptr_p]
    · intro b' hb' s hs hdir
      rw [hptr_simpl b' hb' s hs, hpop_eq,
        Function.update_of_ne (by have := hDir_ge b' s; unfold gmSlabDirBase at this; omega),
        huGe _ (hDir_ge b' s)]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      exact hslab.dir_eq b' hb' s (hs_old_of_new b' hb' s hs).1 hdir
    · intro b' hb' s hs htop
      rw [hptr_simpl b' hb' s hs, hpop_eq,
        Function.update_of_ne (by unfold gmSlabTopIdx; omega), huTop b' hb']
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs htop
      obtain ⟨hs_old, _⟩ := hs_old_of_new b' hb' s hs
      rw [huQ b' hb'] at htop
      split_ifs with hbeq
      · subst hbeq
        simp only [↓reduceIte] at htop
        rw [htop_b, hslab.below_eq b' hb' (gm (gmQIdx b') - 1) (by omega) (by omega)]
        congr 1; omega
      · simp only [hbeq, ↓reduceIte] at htop
        exact hslab.top_eq b' hb' s hs_old htop
    · intro b' hb' s hs hpos
      have hs1_lt : s - 1 < gmPopSlab n_max gm b (gmQIdx b') := by omega
      rw [hptr_simpl b' hb' s hs, hptr_simpl b' hb' (s - 1) hs1_lt, hpop_eq,
        Function.update_of_ne
          (by have := hBel_ge (slabPtrOf n_max gm b' s); unfold gmSlabDirBase at this; omega),
        huGe _ (hBel_ge _)]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs
      exact hslab.below_eq b' hb' s (hs_old_of_new b' hb' s hs).1 hpos
    · intro b' hb' s hs habv
      have hs1_lt : s + 1 < gmPopSlab n_max gm b (gmQIdx b') := habv
      rw [hptr_simpl b' hb' s hs, hptr_simpl b' hb' (s + 1) hs1_lt, hpop_eq,
        Function.update_of_ne
          (by have := hAbv_ge (slabPtrOf n_max gm b' s); unfold gmSlabDirBase at this; omega),
        huGe _ (hAbv_ge _)]
      rw [hpop_eq, Function.update_of_ne (by unfold gmQIdx; omega)] at hs hs1_lt
      exact hslab.above_eq b' hb' s (hs_old_of_new b' hb' s hs).1
        (hs_old_of_new b' hb' (s + 1) hs1_lt).1

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
