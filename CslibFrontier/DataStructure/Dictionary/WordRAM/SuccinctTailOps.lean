/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctProg
import CslibFrontier.Tactic.Realize

/-!
# Tail Pool Allocation and Compaction Operations

This module defines the pure `GlobalMeta` updates (`gmAppendTail`, `gmRemoveTail`) and the
corresponding branch-free `Memory.Prog` operations (`appendTailItemProg`, `removeLastTailItemProg`,
realized to Word-RAM code via `realize`) that allocate and compact tail items while preserving
`TailBijection` and `SlabBijection`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmAppendTail`: pure `GlobalMeta` update
  appending one tail item to bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmRemoveTail`: pure `GlobalMeta` update
  removing the last tail item of bucket `b` and compacting the tail pool.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.appendTailItemProg`: `Memory.Prog` subroutine
  realizing `gmAppendTail`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.removeLastTailItemProg`: `Memory.Prog`
  subroutine realizing `gmRemoveTail` and relocating the compacted payload.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmAppendTail`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmAppendTail`: `gmAppendTail`
  preserves `TailBijection` and `SlabBijection`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmRemoveTail`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmRemoveTail`: `gmRemoveTail`
  preserves `TailBijection` and `SlabBijection`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.appendTailItemProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_appendTailItemGen`: effect and
  `Realizes` certificate for `appendTailItemProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.removeLastTailItemProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_removeLastTailItemGen`: effect and
  `Realizes` certificate for `removeLastTailItemProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Finset

/-! ## Section 1: Pure `gmAppendTail` and `gmRemoveTail` updates -/

/-- Pure `GlobalMeta` update appending one tail item to bucket `b`: assigns physical tail offset
`t_new = gm 1` to descriptor `d_new = b * tailCapPerBucket n_max + gm (gmRIdx b)` and increments
`gm (gmRIdx b)` and `gm 1`. -/
@[expose]
def gmAppendTail (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let r_b := gm (gmRIdx b)
  let t_new := gm 1
  let d_new := b * tailCapPerBucket n_max + r_b
  Function.update
    (Function.update
      (Function.update
        (Function.update gm (gmTailPtrFlatIdx n_max d_new) t_new)
        (gmTailOwnerIdx n_max t_new) d_new)
      (gmRIdx b) (r_b + 1))
    1 (t_new + 1)

/-- Pure `GlobalMeta` update removing the last tail item `r_del = gm (gmRIdx b) - 1` of bucket `b`
by relocating the last physical tail `t_last = gm 1 - 1` into
`t_del = gm (gmTailPtrIdx n_max b r_del)` and decrementing `gm (gmRIdx b)` and `gm 1`. When
`t_del = t_last`, the pointer updates are idempotent. -/
@[expose]
def gmRemoveTail (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let r_del := gm (gmRIdx b) - 1
  let t_del := gm (gmTailPtrIdx n_max b r_del)
  let t_last := gm 1 - 1
  let d_last := gm (gmTailOwnerIdx n_max t_last)
  Function.update
    (Function.update
      (Function.update
        (Function.update gm (gmTailPtrFlatIdx n_max d_last) t_del)
        (gmTailOwnerIdx n_max t_del) d_last)
      (gmRIdx b) r_del)
    1 t_last

/-- Quotient and remainder of a flat two-dimensional index `b * c + r` when `r < c`. -/
theorem mul_add_div_mod_of_lt {b c r : ℕ} (hr : r < c) :
    (b * c + r) / c = b ∧ (b * c + r) % c = r := by
  have hpos : 0 < c := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem flat_descriptor_inj {n_max b₁ r₁ b₂ r₂ : ℕ}
    (hr₁ : r₁ < tailCapPerBucket n_max) (hr₂ : r₂ < tailCapPerBucket n_max)
    (heq : b₁ * tailCapPerBucket n_max + r₁ = b₂ * tailCapPerBucket n_max + r₂) :
    b₁ = b₂ ∧ r₁ = r₂ := by
  have h1 := mul_add_div_mod_of_lt (b := b₁) hr₁
  have h2 := mul_add_div_mod_of_lt (b := b₂) hr₂
  refine ⟨?_, ?_⟩
  · rw [← h1.1, heq, h2.1]
  · rw [← h1.2, heq, h2.2]

/-- The four-cell `GlobalMeta` write shared by `gmAppendTail` and `gmRemoveTail`: point descriptor
`d` at physical tail `t`, record `d` as the owner of `t`, set bucket `b`'s tail count to `r` and the
total tail count to `nt`. -/
private def gmTailWrite (n_max : ℕ) (gm : ℕ → ℕ) (b d t r nt : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update
        (Function.update gm (gmTailPtrFlatIdx n_max d) t)
        (gmTailOwnerIdx n_max t) d)
      (gmRIdx b) r)
    1 nt

/-- `gmTailWrite` changes no cell outside the tail-pointer and tail-owner arrays other than the
total and bucket-`b` tail counts. -/
private theorem gmTailWrite_preserves_nonTail {n_max : ℕ} (gm : ℕ → ℕ) {b d t : ℕ} (r nt : ℕ)
    (hb : b < numBuckets n_max) (hd : d < maxTailItems n_max) (ht : t < maxTailItems n_max) :
    gmTailWrite n_max gm b d t r nt 0 = gm 0 ∧
    gmTailWrite n_max gm b d t r nt 1 = nt ∧
    gmTailWrite n_max gm b d t r nt (gmRIdx b) = r ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gmTailWrite n_max gm b d t r nt (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmTailWrite n_max gm b d t r nt (gmQIdx b') = gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmTailWrite n_max gm b d t r nt (gmSlabTopIdx b') = gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmTailWrite n_max gm b d t r nt (gmSlabDirIdx n_max b' s) = gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gmTailWrite n_max gm b d t r nt idx = gm idx) := by
  unfold gmTailWrite gmQIdx gmRIdx gmSlabTopIdx gmSlabDirIdx gmTailPtrFlatIdx gmTailOwnerIdx
    gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · intro b' hb' hne
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' hb'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' hb'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro b' hb' s hs
    have hmul : b' * dirSlabsPerBucket n_max + s < numBuckets n_max * dirSlabsPerBucket n_max := by
      have h1 : (b' + 1) * dirSlabsPerBucket n_max ≤
          numBuckets n_max * dirSlabsPerBucket n_max := Nat.mul_le_mul_right _ hb'
      nlinarith
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · intro idx hidx
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- `gmTailWrite` points descriptor `d` at `t` and makes `d` the owner of `t`, leaving the other
tail pointers and owners unchanged. -/
private theorem gmTailWrite_tail {n_max : ℕ} (gm : ℕ → ℕ) {b d : ℕ} (t r nt : ℕ)
    (hb : b < numBuckets n_max) (hd : d < maxTailItems n_max) :
    (∀ d' < maxTailItems n_max,
      gmTailWrite n_max gm b d t r nt (gmTailPtrFlatIdx n_max d') =
        if d' = d then t else gm (gmTailPtrFlatIdx n_max d')) ∧
    (∀ t' < maxTailItems n_max,
      gmTailWrite n_max gm b d t r nt (gmTailOwnerIdx n_max t') =
        if t' = t then d else gm (gmTailOwnerIdx n_max t')) := by
  unfold gmTailWrite gmRIdx gmTailPtrFlatIdx gmTailOwnerIdx gmTailOwnerBase gmTailPtrBase
    gmSlabDirBase
  refine ⟨?_, ?_⟩
  · intro d' hd'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    split_ifs with heq
    · rw [heq, Function.update_self]
    · rw [Function.update_of_ne (by omega)]
  · intro t' ht'
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    split_ifs with heq
    · rw [heq, Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem gmAppendTail_preserves_nonTail {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ}
    (hb : b < numBuckets n_max) (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max) :
    gmAppendTail n_max gm b 0 = gm 0 ∧
    gmAppendTail n_max gm b 1 = gm 1 + 1 ∧
    gmAppendTail n_max gm b (gmRIdx b) = gm (gmRIdx b) + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → gmAppendTail n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmAppendTail n_max gm b (gmQIdx b') = gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max, gmAppendTail n_max gm b (gmSlabTopIdx b') = gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmAppendTail n_max gm b (gmSlabDirIdx n_max b' s) = gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gmAppendTail n_max gm b idx = gm idx) := by
  have hd_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < maxTailItems n_max :=
    mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  exact gmTailWrite_preserves_nonTail gm (gm (gmRIdx b) + 1) (gm 1 + 1) hb hd_lt ht

theorem gmAppendTail_tail {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ}
    (hb : b < numBuckets n_max) (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (_ht : gm 1 < maxTailItems n_max) :
    (∀ d < maxTailItems n_max,
      gmAppendTail n_max gm b (gmTailPtrFlatIdx n_max d) =
        if d = b * tailCapPerBucket n_max + gm (gmRIdx b) then gm 1
        else gm (gmTailPtrFlatIdx n_max d)) ∧
    (∀ t < maxTailItems n_max,
      gmAppendTail n_max gm b (gmTailOwnerIdx n_max t) =
        if t = gm 1 then b * tailCapPerBucket n_max + gm (gmRIdx b)
        else gm (gmTailOwnerIdx n_max t)) := by
  have hd_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < maxTailItems n_max :=
    mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  exact gmTailWrite_tail gm (gm 1) (gm (gmRIdx b) + 1) (gm 1 + 1) hb hd_lt

theorem tailBijection_gmAppendTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmAppendTail n_max gm b)
      (fun b' => gmAppendTail n_max gm b (gmRIdx b')) (gmAppendTail n_max gm b 1) := by
  have hpres := gmAppendTail_preserves_nonTail gm hb hr ht
  obtain ⟨hptr_val, hown_val⟩ := gmAppendTail_tail gm hb hr ht
  have hd_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < maxTailItems n_max :=
    mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  have hr_fn : ∀ b' < numBuckets n_max,
      gmAppendTail n_max gm b (gmRIdx b') =
        if b' = b then gm (gmRIdx b) + 1 else gm (gmRIdx b') := by
    intro b' hb'
    split_ifs with heq
    · rw [heq]; exact hpres.2.2.1
    · exact hpres.2.2.2.1 b' hb' heq
  refine ⟨rfl, by rw [hpres.2.1]; omega, ?_, ?_, ?_, ?_⟩
  · intro b' hb'
    rw [hr_fn b' hb']
    split_ifs with heq
    · omega
    · exact htail.r_le b' hb'
  · intro b' hb' r' hr'
    rw [hr_fn b' hb'] at hr'
    have hr'_cap : r' < tailCapPerBucket n_max := by
      split_ifs at hr' with heq
      · omega
      · exact lt_of_lt_of_le hr' (htail.r_le b' hb')
    have hd'_lt : b' * tailCapPerBucket n_max + r' < maxTailItems n_max :=
      mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
    rw [gmTailPtrIdx, hptr_val _ hd'_lt, hpres.2.1]
    split_ifs with hdeq
    · omega
    · have hr'_old : r' < gm (gmRIdx b') := by
        split_ifs at hr' with heq
        · rw [heq]
          have : r' ≠ gm (gmRIdx b) := fun h => hdeq (by rw [heq, h])
          omega
        · exact hr'
      have hlt := htail.ptr_lt b' hb' r' hr'_old
      unfold gmTailPtrIdx at hlt
      omega
  · intro b' hb' r' hr'
    rw [hr_fn b' hb'] at hr'
    have hr'_cap : r' < tailCapPerBucket n_max := by
      split_ifs at hr' with heq
      · omega
      · exact lt_of_lt_of_le hr' (htail.r_le b' hb')
    have hd'_lt : b' * tailCapPerBucket n_max + r' < maxTailItems n_max :=
      mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
    rw [gmTailPtrIdx, hptr_val _ hd'_lt]
    split_ifs with hdeq
    · rw [hown_val (gm 1) ht]
      simp only [↓reduceIte, hdeq]
    · have hr'_old : r' < gm (gmRIdx b') := by
        split_ifs at hr' with heq
        · rw [heq]
          have : r' ≠ gm (gmRIdx b) := fun h => hdeq (by rw [heq, h])
          omega
        · exact hr'
      have ht'_lt : gm (gmTailPtrIdx n_max b' r') < gm 1 := htail.ptr_lt b' hb' r' hr'_old
      unfold gmTailPtrIdx at ht'_lt
      rw [hown_val _ (lt_trans ht'_lt ht), ite_eq_right (by omega)]
      exact htail.owner_ptr b' hb' r' hr'_old
  · intro t ht'
    dsimp only
    rw [hpres.2.1] at ht'
    rw [hown_val t (by omega)]
    split_ifs with hteq
    · have hdm := mul_add_div_mod_of_lt (b := b) hr
      rw [hdm.1, hdm.2, hr_fn b hb, hptr_val _ hd_lt]
      simp only [↓reduceIte]
      exact ⟨hb, by omega, hteq.symm⟩
    · have ht_old : t < gm 1 := by omega
      have hvalid := htail.owner_valid t ht_old
      dsimp only at hvalid
      rcases hvalid with ⟨hb_d, hr_d, hptr_d⟩
      set d := gm (gmTailOwnerIdx n_max t)
      have hr_cap : d % tailCapPerBucket n_max < tailCapPerBucket n_max :=
        lt_of_lt_of_le hr_d (htail.r_le _ hb_d)
      have hd_eq : (d / tailCapPerBucket n_max) * tailCapPerBucket n_max +
          d % tailCapPerBucket n_max = d := by
        rw [Nat.mul_comm, Nat.div_add_mod]
      have hd_max : d < maxTailItems n_max := htail.owner_lt_maxTailItems ht_old
      have hd_ne : d ≠ b * tailCapPerBucket n_max + gm (gmRIdx b) := by
        intro heq
        rw [← hd_eq] at heq
        obtain ⟨hb_eq, hr_eq⟩ := flat_descriptor_inj hr_cap hr heq
        rw [hb_eq, hr_eq] at hr_d
        omega
      refine ⟨hb_d, ?_, ?_⟩
      · rw [hr_fn _ hb_d]
        split_ifs with hbeq
        · rw [hbeq] at hr_d; omega
        · exact hr_d
      · rw [hptr_val d hd_max, ite_eq_right hd_ne, hptr_d]

theorem slabBijection_gmAppendTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' s, slabPtrOf n_max (gmAppendTail n_max gm b) b' s = slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmAppendTail n_max gm b)
      (fun b' => gmAppendTail n_max gm b (gmQIdx b')) (gmAppendTail n_max gm b 0) := by
  obtain ⟨h0, -, -, -, hq, htop, hdir, hmeta⟩ := gmAppendTail_preserves_nonTail gm hb hr ht
  exact ⟨slabPtrOf_congr_of_slabMeta h0 hmeta, hslab.congr h0 hq htop hdir hmeta⟩

theorem slotOf_gmAppendTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (hb : b < numBuckets n_max)
    (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    slotOf n_max (gmAppendTail n_max gm b) b (gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b)) =
      n_max - 1 - gm 1 ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm b',
      slotOf n_max (gmAppendTail n_max gm b) b' j = slotOf n_max gm b' j) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hpres := gmAppendTail_preserves_nonTail gm hb hr ht
  obtain ⟨hptr_val, _⟩ := gmAppendTail_tail gm hb hr ht
  have ⟨hptr, _⟩ := slabBijection_gmAppendTail hb hr ht hslab
  have hd_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < maxTailItems n_max :=
    mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  refine ⟨?_, ?_⟩
  · unfold slotOf
    rw [ite_eq_right hb0, hpres.2.2.2.2.1 b hb]
    have hnot : ¬(gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b) <
        gm (gmQIdx b) * slabSize n_max) := by omega
    rw [ite_eq_right hnot, Nat.add_sub_cancel_left, gmTailPtrIdx, hptr_val _ hd_lt]
    simp only [↓reduceIte]
  · intro b' hb' j hj
    unfold bCount at hj
    simp only [hb0, ↓reduceIte, hb'] at hj
    unfold slotOf
    rw [ite_eq_right hb0, ite_eq_right hb0, hpres.2.2.2.2.1 b' hb']
    split_ifs with hj_slab
    · rw [hptr]
    · have hr'_lt : j - gm (gmQIdx b') * slabSize n_max < gm (gmRIdx b') := by omega
      have hr'_cap : j - gm (gmQIdx b') * slabSize n_max < tailCapPerBucket n_max :=
        lt_of_lt_of_le hr'_lt (htail.r_le b' hb')
      have hd'_lt :
          b' * tailCapPerBucket n_max + (j - gm (gmQIdx b') * slabSize n_max) <
            maxTailItems n_max :=
        mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
      have hne : b' * tailCapPerBucket n_max + (j - gm (gmQIdx b') * slabSize n_max) ≠
          b * tailCapPerBucket n_max + gm (gmRIdx b) := by
        intro heq
        obtain ⟨rfl, hr_eq⟩ := flat_descriptor_inj hr'_cap hr heq
        omega
      rw [gmTailPtrIdx, hptr_val _ hd'_lt, ite_eq_right hne]

/-- The relocated tail `t_del` and the relinked descriptor `d_last` of `gmRemoveTail` are in
range. -/
private theorem gmRemoveTail_indices_lt {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) < maxTailItems n_max ∧
    gm (gmTailOwnerIdx n_max (gm 1 - 1)) < maxTailItems n_max := by
  have hr_del_lt : gm (gmRIdx b) - 1 < gm (gmRIdx b) := by omega
  have ht_del_lt : gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) < gm 1 :=
    htail.ptr_lt b hb _ hr_del_lt
  exact ⟨lt_of_lt_of_le ht_del_lt htail.ntails_le, htail.owner_lt_maxTailItems (by omega)⟩

theorem gmRemoveTail_preserves_nonTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    gmRemoveTail n_max gm b 0 = gm 0 ∧
    gmRemoveTail n_max gm b 1 = gm 1 - 1 ∧
    gmRemoveTail n_max gm b (gmRIdx b) = gm (gmRIdx b) - 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → gmRemoveTail n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmRemoveTail n_max gm b (gmQIdx b') = gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max, gmRemoveTail n_max gm b (gmSlabTopIdx b') = gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmRemoveTail n_max gm b (gmSlabDirIdx n_max b' s) = gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gmRemoveTail n_max gm b idx = gm idx) := by
  obtain ⟨ht_del_max, hd_last_max⟩ := gmRemoveTail_indices_lt hb hr_pos htail
  exact gmTailWrite_preserves_nonTail gm (gm (gmRIdx b) - 1) (gm 1 - 1) hb hd_last_max ht_del_max

theorem gmRemoveTail_tail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    (∀ d < maxTailItems n_max,
      gmRemoveTail n_max gm b (gmTailPtrFlatIdx n_max d) =
        if d = gm (gmTailOwnerIdx n_max (gm 1 - 1)) then
          gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))
        else gm (gmTailPtrFlatIdx n_max d)) ∧
    (∀ t < maxTailItems n_max,
      gmRemoveTail n_max gm b (gmTailOwnerIdx n_max t) =
        if t = gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) then
          gm (gmTailOwnerIdx n_max (gm 1 - 1))
        else gm (gmTailOwnerIdx n_max t)) := by
  obtain ⟨ht_del_max, hd_last_max⟩ := gmRemoveTail_indices_lt hb hr_pos htail
  exact gmTailWrite_tail gm (gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))) (gm (gmRIdx b) - 1)
    (gm 1 - 1) hb hd_last_max

theorem tailBijection_gmRemoveTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmRemoveTail n_max gm b)
      (fun b' => gmRemoveTail n_max gm b (gmRIdx b')) (gmRemoveTail n_max gm b 1) := by
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  obtain ⟨hptr_val, hown_val⟩ := gmRemoveTail_tail hb hr_pos htail
  set r_del := gm (gmRIdx b) - 1
  set d_del := b * tailCapPerBucket n_max + r_del
  set t_del := gm (gmTailPtrIdx n_max b r_del)
  set t_last := gm 1 - 1
  set d_last := gm (gmTailOwnerIdx n_max t_last)
  have hr_del_lt : r_del < gm (gmRIdx b) := by omega
  have hr_del_cap : r_del < tailCapPerBucket n_max :=
    lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt b hb r_del hr_del_lt
  have ht_del_max : t_del < maxTailItems n_max := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have ht_last_lt : t_last < gm 1 := by omega
  have hvalid_last := htail.owner_valid t_last ht_last_lt
  dsimp only at hvalid_last
  change d_last / tailCapPerBucket n_max < numBuckets n_max ∧
    d_last % tailCapPerBucket n_max < gm (gmRIdx (d_last / tailCapPerBucket n_max)) ∧
    gm (gmTailPtrFlatIdx n_max d_last) = t_last at hvalid_last
  rcases hvalid_last with ⟨hb_last, hr_last, hptr_last⟩
  have hd_last_eq : (d_last / tailCapPerBucket n_max) * tailCapPerBucket n_max +
      d_last % tailCapPerBucket n_max = d_last := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have hd_last_max : d_last < maxTailItems n_max := htail.owner_lt_maxTailItems ht_last_lt
  have hown_del : gm (gmTailOwnerIdx n_max t_del) = d_del :=
    htail.owner_ptr b hb r_del hr_del_lt
  have hr_fn : ∀ b' < numBuckets n_max,
      gmRemoveTail n_max gm b (gmRIdx b') = if b' = b then r_del else gm (gmRIdx b') := by
    intro b' hb'
    split_ifs with heq
    · rw [heq]; exact hpres.2.2.1
    · exact hpres.2.2.2.1 b' hb' heq
  refine ⟨rfl, by rw [hpres.2.1]; have := htail.ntails_le; omega, ?_, ?_, ?_, ?_⟩
  · intro b' hb'
    rw [hr_fn b' hb']
    split_ifs with heq
    · have := htail.r_le b hb
      omega
    · exact htail.r_le b' hb'
  · intro b' hb' r' hr'
    rw [hr_fn b' hb'] at hr'
    have hr'_old : r' < gm (gmRIdx b') := by
      split_ifs at hr' with heq
      · rw [heq]; omega
      · exact hr'
    have hr'_cap : r' < tailCapPerBucket n_max := lt_of_lt_of_le hr'_old (htail.r_le b' hb')
    have hd'_lt : b' * tailCapPerBucket n_max + r' < maxTailItems n_max :=
      mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
    have hd'_ne_del : b' * tailCapPerBucket n_max + r' ≠ d_del := by
      intro heq
      obtain ⟨rfl, hr_eq⟩ := flat_descriptor_inj hr'_cap hr_del_cap heq
      simp only [↓reduceIte] at hr'
      omega
    rw [gmTailPtrIdx, hptr_val _ hd'_lt, hpres.2.1]
    split_ifs with hdeq
    · have ht_ne_last : t_del ≠ t_last := by
        intro hteq
        apply hd'_ne_del
        rw [hdeq, ← hown_del, hteq]
      omega
    · have ht'_lt : gm (gmTailPtrIdx n_max b' r') < gm 1 := htail.ptr_lt b' hb' r' hr'_old
      have ht'_ne_last : gm (gmTailPtrIdx n_max b' r') ≠ t_last := by
        intro hteq
        apply hdeq
        rw [← htail.owner_ptr b' hb' r' hr'_old, hteq]
      unfold gmTailPtrIdx at ht'_lt ht'_ne_last
      omega
  · intro b' hb' r' hr'
    rw [hr_fn b' hb'] at hr'
    have hr'_old : r' < gm (gmRIdx b') := by
      split_ifs at hr' with heq
      · rw [heq]; omega
      · exact hr'
    have hr'_cap : r' < tailCapPerBucket n_max := lt_of_lt_of_le hr'_old (htail.r_le b' hb')
    have hd'_lt : b' * tailCapPerBucket n_max + r' < maxTailItems n_max :=
      mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
    have hd'_ne_del : b' * tailCapPerBucket n_max + r' ≠ d_del := by
      intro heq
      obtain ⟨rfl, hr_eq⟩ := flat_descriptor_inj hr'_cap hr_del_cap heq
      simp only [↓reduceIte] at hr'
      omega
    rw [gmTailPtrIdx, hptr_val _ hd'_lt]
    split_ifs with hdeq
    · rw [hown_val t_del ht_del_max]
      simp only [↓reduceIte, hdeq]
    · have ht'_lt : gm (gmTailPtrIdx n_max b' r') < gm 1 := htail.ptr_lt b' hb' r' hr'_old
      have ht'_ne_del : gm (gmTailPtrIdx n_max b' r') ≠ t_del := by
        intro hteq
        apply hd'_ne_del
        rw [← htail.owner_ptr b' hb' r' hr'_old, hteq, hown_del]
      unfold gmTailPtrIdx at ht'_lt ht'_ne_del
      rw [hown_val _ (lt_of_lt_of_le ht'_lt htail.ntails_le), ite_eq_right ht'_ne_del]
      exact htail.owner_ptr b' hb' r' hr'_old
  · intro t ht'
    dsimp only
    rw [hpres.2.1] at ht'
    have ht_old : t < gm 1 := by omega
    rw [hown_val t (lt_of_lt_of_le ht_old htail.ntails_le)]
    split_ifs with hteq
    · have hne_del : d_last ≠ d_del := by
        intro heq
        have : t_last = t_del := by rw [← hptr_last, heq, ← gmTailPtrIdx]
        omega
      refine ⟨hb_last, ?_, ?_⟩
      · rw [hr_fn _ hb_last]
        split_ifs with hbeq
        · rw [hbeq] at hr_last hd_last_eq
          have hne_r : d_last % tailCapPerBucket n_max ≠ r_del := by
            intro hreq
            apply hne_del
            rw [← hd_last_eq, hreq]
          omega
        · exact hr_last
      · rw [hptr_val d_last hd_last_max]
        simp only [↓reduceIte]
        exact hteq.symm
    · have hvalid_t := htail.owner_valid t ht_old
      dsimp only at hvalid_t
      set d_t := gm (gmTailOwnerIdx n_max t)
      change d_t / tailCapPerBucket n_max < numBuckets n_max ∧
        d_t % tailCapPerBucket n_max < gm (gmRIdx (d_t / tailCapPerBucket n_max)) ∧
        gm (gmTailPtrFlatIdx n_max d_t) = t at hvalid_t
      rcases hvalid_t with ⟨hb_t, hr_t, hptr_t⟩
      have hd_t_eq : (d_t / tailCapPerBucket n_max) * tailCapPerBucket n_max +
          d_t % tailCapPerBucket n_max = d_t := by
        rw [Nat.mul_comm, Nat.div_add_mod]
      have hd_t_max : d_t < maxTailItems n_max := htail.owner_lt_maxTailItems ht_old
      have hd_t_ne_del : d_t ≠ d_del := by
        intro heq
        apply hteq
        rw [← hptr_t, heq, ← gmTailPtrIdx]
      have hd_t_ne_last : d_t ≠ d_last := by
        intro heq
        have : t = t_last := by rw [← hptr_t, heq, hptr_last]
        omega
      refine ⟨hb_t, ?_, ?_⟩
      · rw [hr_fn _ hb_t]
        split_ifs with hbeq
        · rw [hbeq] at hr_t hd_t_eq
          have hne_r : d_t % tailCapPerBucket n_max ≠ r_del := by
            intro hreq
            apply hd_t_ne_del
            rw [← hd_t_eq, hreq]
          omega
        · exact hr_t
      · rw [hptr_val d_t hd_t_max, ite_eq_right hd_t_ne_last, hptr_t]

theorem slabBijection_gmRemoveTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' s, slabPtrOf n_max (gmRemoveTail n_max gm b) b' s = slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmRemoveTail n_max gm b)
      (fun b' => gmRemoveTail n_max gm b (gmQIdx b')) (gmRemoveTail n_max gm b 0) := by
  obtain ⟨h0, -, -, -, hq, htop, hdir, hmeta⟩ := gmRemoveTail_preserves_nonTail hb hr_pos htail
  exact ⟨slabPtrOf_congr_of_slabMeta h0 hmeta, hslab.congr h0 hq htop hdir hmeta⟩

theorem update_slotOf_gmRemoveTail {α : Type*} (arr : ℕ → α) {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (htot : gm 0 * slabSize n_max + gm 1 ≤ n_max) :
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmRemoveTail n_max gm b) b',
      Function.update arr (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (arr (n_max - 1 - (gm 1 - 1)))
        (slotOf n_max (gmRemoveTail n_max gm b) b' j) = arr (slotOf n_max gm b' j)) ∧
    (∀ g < n_max - gm 1,
      Function.update arr (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (arr (n_max - 1 - (gm 1 - 1))) g = arr g) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  obtain ⟨hptr_val, _⟩ := gmRemoveTail_tail hb hr_pos htail
  have ⟨hptr, _⟩ := slabBijection_gmRemoveTail hb hr_pos htail hslab
  set r_del := gm (gmRIdx b) - 1
  set t_del := gm (gmTailPtrIdx n_max b r_del)
  set t_last := gm 1 - 1
  set d_del := b * tailCapPerBucket n_max + r_del
  set d_last := gm (gmTailOwnerIdx n_max t_last)
  have hr_del_lt : r_del < gm (gmRIdx b) := by omega
  have hr_del_cap : r_del < tailCapPerBucket n_max := lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt b hb r_del hr_del_lt
  have hown_del : gm (gmTailOwnerIdx n_max t_del) = d_del :=
    htail.owner_ptr b hb r_del hr_del_lt
  have ht_last_lt : t_last < gm 1 := by omega
  have hvalid_last := htail.owner_valid t_last ht_last_lt
  dsimp only at hvalid_last
  change d_last / tailCapPerBucket n_max < numBuckets n_max ∧
    d_last % tailCapPerBucket n_max < gm (gmRIdx (d_last / tailCapPerBucket n_max)) ∧
    gm (gmTailPtrFlatIdx n_max d_last) = t_last at hvalid_last
  rcases hvalid_last with ⟨hb_last, hr_last, hptr_last⟩
  refine ⟨?_, ?_⟩
  · intro b' hb' j hj
    unfold bCount at hj
    simp only [hb0, ↓reduceIte, hb'] at hj
    rw [hpres.2.2.2.2.1 b' hb'] at hj
    unfold slotOf
    rw [ite_eq_right hb0, ite_eq_right hb0, hpres.2.2.2.2.1 b' hb']
    split_ifs with hj_slab
    · rw [hptr]
      have hs_lt : j / slabSize n_max < gm (gmQIdx b') :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hp_lt : slabPtrOf n_max gm b' (j / slabSize n_max) < gm 0 :=
        hslab.ptr_lt b' hb' _ hs_lt
      have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
      have hmod_lt : j % slabSize n_max < slabSize n_max := Nat.mod_lt j hK_pos
      have h1 : (slabPtrOf n_max gm b' (j / slabSize n_max) + 1) * slabSize n_max ≤
          gm 0 * slabSize n_max := Nat.mul_le_mul_right _ hp_lt
      rw [Nat.add_one_mul] at h1
      rw [Function.update_of_ne (by omega)]
    · set r' := j - gm (gmQIdx b') * slabSize n_max
      have hr'_new : r' < gmRemoveTail n_max gm b (gmRIdx b') := by omega
      have hr'_old : r' < gm (gmRIdx b') := by
        by_cases hbeq : b' = b
        · rw [hbeq] at hr'_new ⊢; rw [hpres.2.2.1] at hr'_new; omega
        · rw [hpres.2.2.2.1 b' hb' hbeq] at hr'_new; exact hr'_new
      have hr'_cap : r' < tailCapPerBucket n_max := lt_of_lt_of_le hr'_old (htail.r_le b' hb')
      have hd'_lt : b' * tailCapPerBucket n_max + r' < maxTailItems n_max :=
        mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
      have hd'_ne_del : b' * tailCapPerBucket n_max + r' ≠ d_del := by
        intro heq
        obtain ⟨rfl, hr_eq⟩ := flat_descriptor_inj hr'_cap hr_del_cap heq
        rw [hpres.2.2.1] at hr'_new
        omega
      rw [gmTailPtrIdx, hptr_val _ hd'_lt]
      split_ifs with hdeq
      · rw [Function.update_self, ← hptr_last, ← hdeq, ← gmTailPtrIdx]
      · have ht'_lt : gm (gmTailPtrIdx n_max b' r') < gm 1 := htail.ptr_lt b' hb' r' hr'_old
        have ht'_ne_del : gm (gmTailPtrIdx n_max b' r') ≠ t_del := by
          intro hteq
          apply hd'_ne_del
          rw [← htail.owner_ptr b' hb' r' hr'_old, hteq, hown_del]
        unfold gmTailPtrIdx at ht'_lt ht'_ne_del
        rw [Function.update_of_ne (by omega)]
  · intro g hg
    rw [Function.update_of_ne (by omega)]

/-! ## Section 2: `Memory.Prog` tail allocation and compaction operations (`realize`) -/

theorem lt_two_pow_globalPtrBits_of_le_n_max {n_max x : ℕ} (hx : x ≤ n_max) :
    x < 2 ^ globalPtrBits n_max := by
  unfold globalPtrBits
  have hpow : n_max + 1 ≤ 2 ^ Nat.clog 2 (n_max + 1) :=
    Nat.le_pow_clog (by decide : 1 < 2) (n_max + 1)
  omega

theorem lt_two_pow_globalPtrBits_of_le_globalMetaLen {n_max x : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hx : x ≤ globalMetaLen n_max) :
    x < 2 ^ globalPtrBits n_max :=
  lt_two_pow_globalPtrBits_of_le_n_max (hx.trans (globalMetaLen_le_of_bucketBits_pos hb_pos))

theorem ntails_lt_maxTailItems_of_r_lt {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hr_lt : gm (gmRIdx b) < tailCapPerBucket n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    gm 1 < maxTailItems n_max := by
  classical
  let d_new := b * tailCapPerBucket n_max + gm (gmRIdx b)
  have hd_new_lt : d_new < maxTailItems n_max := mul_tailCapPerBucket_add_lt_maxTailItems hb hr_lt
  have hinj : Set.InjOn (fun t => gm (gmTailOwnerIdx n_max t)) (Finset.range (gm 1)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at ht₁ ht₂
    have hv1 := (htail.owner_valid t₁ ht₁).2.2
    have hv2 := (htail.owner_valid t₂ ht₂).2.2
    dsimp only at hv1 hv2 heq
    rw [← hv1, ← hv2, heq]
  have hsub : (Finset.range (gm 1)).image (fun t => gm (gmTailOwnerIdx n_max t)) ⊆
      (Finset.range (maxTailItems n_max)).erase d_new := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨t, ht, rfl⟩
    rw [Finset.mem_range] at ht
    obtain ⟨-, hr_t, -⟩ := htail.owner_valid t ht
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (htail.owner_lt_maxTailItems ht)⟩
    intro heq
    rw [heq] at hr_t
    have hdm := mul_add_div_mod_of_lt (b := b) hr_lt
    change d_new / tailCapPerBucket n_max = b ∧
      d_new % tailCapPerBucket n_max = gm (gmRIdx b) at hdm
    rw [hdm.1, hdm.2] at hr_t
    exact Nat.lt_irrefl _ hr_t
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range,
    Finset.card_erase_of_mem (Finset.mem_range.mpr hd_new_lt), Finset.card_range] at hcard
  omega

/-- Parameter-free `Memory.Prog` operation appending one tail item to bucket `b = d.2.2` at
`base = d.2.1`. -/
def appendTailItemGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let r_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
  let t_new ← readGMGenProg (d.1, (d.2.1, 1))
  let d_new := d.2.2 * dpTailCap d.1 + r_b
  writeGMGenProg (d.1, ((d.2.1, dpGmTailPtrBase d.1 + d_new), t_new))
  writeGMGenProg (d.1, ((d.2.1, dpGmTailOwnerBase d.1 + t_new), d_new))
  writeGMGenProg (d.1, ((d.2.1, 4 + 3 * d.2.2 + 1), r_b + 1))
  let _ ← writeGMGenProg (d.1, ((d.2.1, 1), t_new + 1))
  pure t_new

/-- `Memory.Prog` operation appending one tail item to bucket `b = d.2` at `base = d.1`
(`0 < bucketBits n_max`) and returning the newly allocated physical tail offset `t_new = gm 1`. -/
def appendTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let r_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 1)
  let t_new ← readGMProg U V w n_max h_space (d.1, 1)
  let d_new := d.2 * tailCapPerBucket n_max + r_b
  writeGMProg U V w n_max h_space ((d.1, gmTailPtrBase n_max + d_new), t_new)
  writeGMProg U V w n_max h_space ((d.1, gmTailOwnerBase n_max + t_new), d_new)
  writeGMProg U V w n_max h_space ((d.1, 4 + 3 * d.2 + 1), r_b + 1)
  let _ ← writeGMProg U V w n_max h_space ((d.1, 1), t_new + 1)
  pure t_new

@[simp] theorem appendTailItemGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    appendTailItemGenProg (mkDictParams U V w n_max h_space, d) =
      appendTailItemProg U V w n_max h_space d := by rfl

@[simp]
theorem memoryCost_appendTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (appendTailItemProg U V w n_max h_space d) s = 20 := by
  simp [appendTailItemProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]

/-- Pure state effect and return value of `appendTailItemProg`. -/
theorem appendTailItemProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (htail : TailBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b => gmAt base U V w n_max h_space s.mem (gmRIdx b))
      (gmAt base U V w n_max h_space s.mem 1))
    (hr_lt : gmAt base U V w n_max h_space s.mem (gmRIdx b) < tailCapPerBucket n_max) :
    let s' := (Memory.spec 0).clientState s (appendTailItemProg U V w n_max h_space (base, b))
    (Memory.spec 0).clientResult s (appendTailItemProg U V w n_max h_space (base, b)) =
      gmAt base U V w n_max h_space s.mem 1 ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmAppendTail n_max (gmAt base U V w n_max h_space s.mem) b := by
  intro s'
  set gm := gmAt base U V w n_max h_space s.mem
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have h1_lt : 1 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have hptr_idx_lt : gmTailPtrBase n_max + (b * tailCapPerBucket n_max + gm (gmRIdx b)) <
      globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_lt
  have ht_cap : gm 1 < maxTailItems n_max :=
    ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have hmax_tail_le : maxTailItems n_max ≤ n_max := maxTailItems_le n_max
  have hown_idx_lt : gmTailOwnerBase n_max + gm 1 < globalMetaLen n_max :=
    gmTailOwnerIdx_lt hb_pos ht_cap
  have ht_val_lt : gm 1 < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hd_val_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase at hptr_idx_lt; omega)
  have hr1_val_lt : gm (gmRIdx b) + 1 < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase gmSlabDirBase at hptr_idx_lt; omega)
  have ht1_val_lt : gm 1 + 1 < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  unfold appendTailItemProg
  dsimp only at s' ⊢
  rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s hr_idx_lt,
    StateTransitionSpec.clientResult_bind, clientState_readGMProg,
    clientResult_readGMProg s h1_lt]
  simp only [StateTransitionSpec.clientResult_bind]
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState
          ((Memory.spec 0).clientState s
            (writeGMProg U V w n_max h_space
              ((base, gmTailPtrBase n_max + (b * tailCapPerBucket n_max + gm (gmRIdx b))), gm 1)))
          (writeGMProg U V w n_max h_space
            ((base, gmTailOwnerBase n_max + gm 1), b * tailCapPerBucket n_max + gm (gmRIdx b))))
        (writeGMProg U V w n_max h_space ((base, 4 + 3 * b + 1), gm (gmRIdx b) + 1)))
      (writeGMProg U V w n_max h_space ((base, 1), gm 1 + 1)) := by
    change (Memory.spec 0).clientState s (appendTailItemProg U V w n_max h_space (base, b)) = _
    unfold appendTailItemProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s hr_idx_lt,
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s h1_lt]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ := writeGMProg_effect (V := V) hw hptr_idx_lt ht_val_lt s
  set s₁ := (Memory.spec 0).clientState s
    (writeGMProg U V w n_max h_space
      ((base, gmTailPtrBase n_max + (b * tailCapPerBucket n_max + gm (gmRIdx b))), gm 1))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ := writeGMProg_effect (V := V) hw hown_idx_lt hd_val_lt s₁
  set s₂ := (Memory.spec 0).clientState s₁
    (writeGMProg U V w n_max h_space
      ((base, gmTailOwnerBase n_max + gm 1), b * tailCapPerBucket n_max + gm (gmRIdx b)))
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ := writeGMProg_effect (V := V) hw hr_idx_lt hr1_val_lt s₂
  set s₃ := (Memory.spec 0).clientState s₂
    (writeGMProg U V w n_max h_space ((base, 4 + 3 * b + 1), gm (gmRIdx b) + 1))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ := writeGMProg_effect (V := V) hw h1_lt ht1_val_lt s₃
  rw [hst]
  refine ⟨rfl, by rw [hf4, hf3, hf2, hf1],
    fun a ha => by rw [hout4 a ha, hout3 a ha, hout2 a ha, hout1 a ha],
    by rw [hq4, hq3, hq2, hq1], by rw [hv4, hv3, hv2, hv1], by rw [hl4, hl3, hl2, hl1], ?_⟩
  rw [hg4, hg3, hg2, hg1]
  rfl

/-- Precondition for `appendTailItemProg`. -/
@[expose]
def AppendTailItemPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  TailBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmRIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 1) ∧
  b < numBuckets n_max ∧
  gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) < tailCapPerBucket n_max ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `appendTailItemGenProg`. -/
@[expose]
def AppendTailItemGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  TailBijection (dpNMax d.1)
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    (fun b' => gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1)
      s.mem (gmRIdx b'))
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem 1) ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem (gmRIdx d.2.2) <
    tailCapPerBucket (dpNMax d.1) ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem appendTailItemGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    AppendTailItemGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      AppendTailItemPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

private theorem appendTailItem_bounds {U V w₀ n_max h_space w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (h : AppendTailItemPre U V w₀ n_max h_space w d.1 d.2 s) :
    let r_b := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1))
    let t_new := (Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1)))
      (readGMProg U V w₀ n_max h_space (d.1, 1))
    4 + 3 * d.2 + 1 < globalMetaLen n_max ∧
    1 < globalMetaLen n_max ∧
    gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + r_b) < globalMetaLen n_max ∧
    gmTailOwnerBase n_max + t_new < globalMetaLen n_max ∧
    r_b + 1 ≤ globalMetaLen n_max ∧
    t_new + 1 ≤ max n_max 1 := by
  rcases h with ⟨_, htail, hb, hr_lt, hb_pos⟩
  have hr_idx : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have h1_idx : 1 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have hrb_eq : (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1)) =
      gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx d.2) :=
    clientResult_readGMProg s hr_idx
  have htnew_eq : (Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1)))
      (readGMProg U V w₀ n_max h_space (d.1, 1)) =
      gmAt d.1 U V w₀ n_max h_space s.mem 1 := by
    rw [clientState_readGMProg]
    exact clientResult_readGMProg s h1_idx
  have hptr_lt : gmTailPtrBase n_max +
      (d.2 * tailCapPerBucket n_max + gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx d.2)) <
      globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_lt
  have ht_cap : gmAt d.1 U V w₀ n_max h_space s.mem 1 < maxTailItems n_max :=
    ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have hmax_tail_le : maxTailItems n_max ≤ n_max := maxTailItems_le n_max
  have hown_lt : gmTailOwnerBase n_max + gmAt d.1 U V w₀ n_max h_space s.mem 1 <
      globalMetaLen n_max := gmTailOwnerIdx_lt hb_pos ht_cap
  refine ⟨hr_idx, h1_idx, ?_, ?_, ?_, ?_⟩
  · rw [hrb_eq]; exact hptr_lt
  · rw [htnew_eq]; exact hown_lt
  · rw [hrb_eq]; have := tailCapPerBucket_le_globalMetaLen hb_pos; omega
  · rw [htnew_eq]; omega

theorem realizes_appendTailItemGen :
    Realizes .exact appendTailItemGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      AppendTailItemGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let r_idx ← pure (4 + 3 * d.2.2 + 1)
      let r_b ← readGMGenProg (d.1, (d.2.1, r_idx))
      let i1 ← pure 1
      let t_new ← readGMGenProg (d.1, (d.2.1, i1))
      let d_new ← pure (d.2.2 * dpTailCap d.1 + r_b)
      let ptr_idx ← pure (dpGmTailPtrBase d.1 + d_new)
      writeGMGenProg (d.1, ((d.2.1, ptr_idx), t_new))
      let own_idx ← pure (dpGmTailOwnerBase d.1 + t_new)
      writeGMGenProg (d.1, ((d.2.1, own_idx), d_new))
      let r_b1 ← pure (r_b + 1)
      writeGMGenProg (d.1, ((d.2.1, r_idx), r_b1))
      let t_new1 ← pure (t_new + 1)
      writeGMGenProg (d.1, ((d.2.1, i1), t_new1))
      pure t_new) ?_
    (fun d => by simp [appendTailItemGenProg, ← PFunctor.FreeM.bind_eq_bind])
  realizeDictWith [appendTailItemGenPre_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (appendTailItem_bounds h).1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (appendTailItem_bounds h).1
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact (appendTailItem_bounds h).2.1
  · have hbnd := (appendTailItem_bounds h).2.2.1
    exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU (by omega)
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (appendTailItem_bounds h).2.2.1)
  · exact (appendTailItem_bounds h).2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (appendTailItem_bounds h).2.2.2.1)
  · exact (appendTailItem_bounds h).2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (appendTailItem_bounds h).2.2.2.2.1
  · exact fits_of_le_max_n_one h.1 hw hnU hU (appendTailItem_bounds h).2.2.2.2.2

/-- Parameter-free `Memory.Prog` operation removing the last tail item of bucket `b = d.2.2` at
`base = d.2.1`. -/
def removeLastTailItemGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let r_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
  let r_del := r_b - 1
  let t_del ← readGMGenProg (d.1,
    (d.2.1, dpGmTailPtrBase d.1 + (d.2.2 * dpTailCap d.1 + r_del)))
  let n_tails ← readGMGenProg (d.1, (d.2.1, 1))
  let t_last := n_tails - 1
  let d_last ← readGMGenProg (d.1, (d.2.1, dpGmTailOwnerBase d.1 + t_last))
  let g_last := dpNMaxSubOne d.1 - t_last
  let g_del := dpNMaxSubOne d.1 - t_del
  let q_move ← readQuotGenProg (d.1, (d.2.1, g_last))
  writeQuotGenProg (d.1, ((d.2.1, g_del), q_move))
  let v_move ← readValGenProg (d.1, (d.2.1, g_last))
  writeValGenProg (d.1, ((d.2.1, g_del), v_move))
  writeGMGenProg (d.1, ((d.2.1, dpGmTailPtrBase d.1 + d_last), t_del))
  writeGMGenProg (d.1, ((d.2.1, dpGmTailOwnerBase d.1 + t_del), d_last))
  writeGMGenProg (d.1, ((d.2.1, 4 + 3 * d.2.2 + 1), r_del))
  writeGMGenProg (d.1, ((d.2.1, 1), t_last))

/-- `Memory.Prog` operation removing the last tail item of bucket `b = d.2` at `base = d.1`
(`0 < bucketBits n_max`, `1 ≤ gm (gmRIdx b)`), compacting the tail pool by moving the payload at
physical slot `(n_max - 1) - (gm 1 - 1)` into `(n_max - 1) - t_del` and updating `GlobalMeta` via
`gmRemoveTail`. -/
def removeLastTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit := do
  let r_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 1)
  let r_del := r_b - 1
  let t_del ← readGMProg U V w n_max h_space
    (d.1, gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + r_del))
  let n_tails ← readGMProg U V w n_max h_space (d.1, 1)
  let t_last := n_tails - 1
  let d_last ← readGMProg U V w n_max h_space (d.1, gmTailOwnerBase n_max + t_last)
  let g_last := (n_max - 1) - t_last
  let g_del := (n_max - 1) - t_del
  let q_move ← readQuotProg U w n_max h_space (d.1, g_last)
  writeQuotProg U w n_max h_space ((d.1, g_del), q_move)
  let v_move ← readValProg U V w n_max h_space (d.1, g_last)
  writeValProg U V w n_max h_space ((d.1, g_del), v_move)
  writeGMProg U V w n_max h_space ((d.1, gmTailPtrBase n_max + d_last), t_del)
  writeGMProg U V w n_max h_space ((d.1, gmTailOwnerBase n_max + t_del), d_last)
  writeGMProg U V w n_max h_space ((d.1, 4 + 3 * d.2 + 1), r_del)
  writeGMProg U V w n_max h_space ((d.1, 1), t_last)

@[simp] theorem removeLastTailItemGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    removeLastTailItemGenProg (mkDictParams U V w n_max h_space, d) =
      removeLastTailItemProg U V w n_max h_space d := by rfl

@[simp]
theorem memoryCost_removeLastTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    memoryCost (removeLastTailItemProg U V w n_max h_space d) s = 36 := by
  simp [removeLastTailItemProg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]

/-- Pure state effect of `removeLastTailItemProg`. -/
theorem removeLastTailItemProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (htail : TailBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b => gmAt base U V w n_max h_space s.mem (gmRIdx b))
      (gmAt base U V w n_max h_space s.mem 1))
    (hr_pos : 1 ≤ gmAt base U V w n_max h_space s.mem (gmRIdx b)) :
    let gm := gmAt base U V w n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space (base, b))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update (quotAt base U w n_max h_space s.mem)
        (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (quotAt base U w n_max h_space s.mem (n_max - 1 - (gm 1 - 1))) ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update (valAt base U V w n_max h_space s.mem)
        (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (valAt base U V w n_max h_space s.mem (n_max - 1 - (gm 1 - 1))) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmRemoveTail n_max gm b := by
  intro gm s'
  change 1 ≤ gm (gmRIdx b) at hr_pos
  have hnt_le : gm 1 ≤ n_max := htail.ntails_le.trans (maxTailItems_le n_max)
  set r_del := gm (gmRIdx b) - 1
  set t_del := gm (gmTailPtrIdx n_max b r_del)
  set t_last := gm 1 - 1
  set d_last := gm (gmTailOwnerIdx n_max t_last)
  set g_last := n_max - 1 - t_last
  set g_del := n_max - 1 - t_del
  have hr_del_lt : r_del < gm (gmRIdx b) := by omega
  have hr_del_cap : r_del < tailCapPerBucket n_max := lt_of_lt_of_le hr_del_lt (htail.r_le b hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt b hb r_del hr_del_lt
  have hgm1_pos : 1 ≤ gm 1 := by omega
  have ht_last_lt : t_last < gm 1 := by omega
  have hd_last_lt : d_last < maxTailItems n_max := htail.owner_lt_maxTailItems ht_last_lt
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have hptr_del_lt : gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_del) <
      globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_del_cap
  have h1_lt : 1 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have ht_last_cap : t_last < maxTailItems n_max := lt_of_lt_of_le ht_last_lt htail.ntails_le
  have hown_last_lt : gmTailOwnerBase n_max + t_last < globalMetaLen n_max :=
    gmTailOwnerIdx_lt hb_pos ht_last_cap
  have hg_last_lt : g_last < n_max := by omega
  have hg_del_lt : g_del < n_max := by omega
  have hptr_last_lt : gmTailPtrBase n_max + d_last < globalMetaLen n_max :=
    gmTailPtrFlatIdx_lt hb_pos hd_last_lt
  have ht_del_cap : t_del < maxTailItems n_max := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have hown_del_lt : gmTailOwnerBase n_max + t_del < globalMetaLen n_max :=
    gmTailOwnerIdx_lt hb_pos ht_del_cap
  have hq_val_lt : quotAt base U w n_max h_space s.mem g_last < 2 ^ quotientBits U n_max :=
    quotAt_lt _ _ _ _ _ _ _
  have hv_val_lt : valAt base U V w n_max h_space s.mem g_last < 2 ^ valBits V :=
    valAt_lt _ _ _ _ _ _ _ _
  have ht_del_val_lt : t_del < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  have hd_last_val_lt : d_last < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase at hptr_last_lt; omega)
  have hr_del_val_lt : r_del < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos
      (by unfold gmTailPtrBase gmSlabDirBase at hptr_del_lt; omega)
  have ht_last_val_lt : t_last < 2 ^ globalPtrBits n_max :=
    lt_two_pow_globalPtrBits_of_le_n_max (by omega)
  let s₁ := (Memory.spec 0).clientState s
    (writeQuotProg U w n_max h_space ((base, g_del), quotAt base U w n_max h_space s.mem g_last))
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hg_del_lt hq_val_lt s
  let s₂ := (Memory.spec 0).clientState s₁
    (writeValProg U V w n_max h_space ((base, g_del), valAt base U V w n_max h_space s.mem g_last))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hg_del_lt hv_val_lt s₁
  let s₃ := (Memory.spec 0).clientState s₂
    (writeGMProg U V w n_max h_space ((base, gmTailPtrBase n_max + d_last), t_del))
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw hptr_last_lt ht_del_val_lt s₂
  let s₄ := (Memory.spec 0).clientState s₃
    (writeGMProg U V w n_max h_space ((base, gmTailOwnerBase n_max + t_del), d_last))
  obtain ⟨hf4, hout4, hq4, hv4, hl4, hg4⟩ :=
    writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw hown_del_lt hd_last_val_lt s₃
  let s₅ := (Memory.spec 0).clientState s₄
    (writeGMProg U V w n_max h_space ((base, 4 + 3 * b + 1), r_del))
  obtain ⟨hf5, hout5, hq5, hv5, hl5, hg5⟩ :=
    writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw hr_idx_lt hr_del_val_lt s₄
  let s₆ := (Memory.spec 0).clientState s₅
    (writeGMProg U V w n_max h_space ((base, 1), t_last))
  obtain ⟨hf6, hout6, hq6, hv6, hl6, hg6⟩ :=
    writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw h1_lt ht_last_val_lt s₅
  have hst : s' = s₆ := by
    have hv1_at : valAt base U V w n_max h_space s₁.mem g_last =
        valAt base U V w n_max h_space s.mem g_last := congrFun hv1 g_last
    dsimp only [s₁, g_del, g_last, t_del, t_last, r_del, gm,
      gmTailPtrIdx, gmTailPtrFlatIdx, gmRIdx] at hv1_at
    change (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space (base, b)) = s₆
    unfold removeLastTailItemProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact hr_idx_lt),
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact hptr_del_lt),
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact h1_lt),
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s (by exact hown_last_lt),
      StateTransitionSpec.clientState_bind, clientState_readQuotProg,
      clientResult_readQuotProg s (by exact hg_last_lt),
      StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, clientState_readValProg,
      clientResult_readValProg _ (by exact hg_last_lt), hv1_at]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  rw [hst]
  refine ⟨by rw [hf6, hf5, hf4, hf3, hf2, hf1], ?_,
    by rw [hq6, hq5, hq4, hq3, hq2, hq1],
    by rw [hv6, hv5, hv4, hv3, hv2, hv1],
    by rw [hl6, hl5, hl4, hl3, hl2, hl1],
    by rw [hg6, hg5, hg4, hg3, hg2, hg1]; rfl⟩
  intro a ha
  rw [hout6 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout5 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout4 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout3 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout2 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
    hout1 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)]

/-- Precondition for `removeLastTailItemProg`. -/
@[expose]
def RemoveLastTailItemPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  TailBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmRIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 1) ∧
  b < numBuckets n_max ∧
  1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `removeLastTailItemGenProg`. -/
@[expose]
def RemoveLastTailItemGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1 ∧
  TailBijection (dpNMax d.1)
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    (fun b' => gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1)
      s.mem (gmRIdx b'))
    (gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem 1) ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem (gmRIdx d.2.2) ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem removeLastTailItemGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    RemoveLastTailItemGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      RemoveLastTailItemPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

private theorem removeLastTailItem_bounds {U V w₀ n_max h_space w : ℕ} {d : ℕ × ℕ}
    {s : Memory.State}
    (h : RemoveLastTailItemPre U V w₀ n_max h_space w d.1 d.2 s) :
    let e_rb := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1))
    let s1 := (Memory.spec 0).clientState s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1))
    let e_ptr_del_idx := gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + (e_rb - 1))
    let e_tdel := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (d.1, e_ptr_del_idx))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (d.1, e_ptr_del_idx))
    let e_ntails := (Memory.spec 0).clientResult s2
      (readGMProg U V w₀ n_max h_space (d.1, 1))
    let s3 := (Memory.spec 0).clientState s2
      (readGMProg U V w₀ n_max h_space (d.1, 1))
    let e_own_last_idx := gmTailOwnerBase n_max + (e_ntails - 1)
    let e_dlast := (Memory.spec 0).clientResult s3
      (readGMProg U V w₀ n_max h_space (d.1, e_own_last_idx))
    4 + 3 * d.2 + 1 < globalMetaLen n_max ∧
    1 ≤ e_rb ∧
    e_ptr_del_idx < globalMetaLen n_max ∧
    1 < globalMetaLen n_max ∧
    1 ≤ e_ntails ∧
    e_own_last_idx < globalMetaLen n_max ∧
    e_ntails - 1 ≤ n_max - 1 ∧
    e_tdel ≤ n_max - 1 ∧
    n_max - 1 - (e_ntails - 1) < n_max ∧
    n_max - 1 - e_tdel < n_max ∧
    gmTailPtrBase n_max + e_dlast < globalMetaLen n_max ∧
    gmTailOwnerBase n_max + e_tdel < globalMetaLen n_max := by
  rcases h with ⟨_, htail, hb, hr_pos, hb_pos⟩
  set gm := gmAt d.1 U V w₀ n_max h_space s.mem
  change 1 ≤ gm (gmRIdx d.2) at hr_pos
  have hnt_le : gm 1 ≤ n_max := htail.ntails_le.trans (maxTailItems_le n_max)
  set r_del := gm (gmRIdx d.2) - 1
  set t_del := gm (gmTailPtrIdx n_max d.2 r_del)
  set t_last := gm 1 - 1
  set d_last := gm (gmTailOwnerIdx n_max t_last)
  have hr_del_lt : r_del < gm (gmRIdx d.2) := by omega
  have hr_del_cap : r_del < tailCapPerBucket n_max := lt_of_lt_of_le hr_del_lt (htail.r_le d.2 hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt d.2 hb r_del hr_del_lt
  have hgm1_pos : 1 ≤ gm 1 := by omega
  have ht_last_lt : t_last < gm 1 := by omega
  have hd_last_lt : d_last < maxTailItems n_max := htail.owner_lt_maxTailItems ht_last_lt
  have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have hptr_del_lt : gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + r_del) <
      globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_del_cap
  have h1_lt : 1 < globalMetaLen n_max := by unfold globalMetaLen; omega
  have ht_last_cap : t_last < maxTailItems n_max := lt_of_lt_of_le ht_last_lt htail.ntails_le
  have hown_last_lt : gmTailOwnerBase n_max + t_last < globalMetaLen n_max :=
    gmTailOwnerIdx_lt hb_pos ht_last_cap
  have hptr_last_lt : gmTailPtrBase n_max + d_last < globalMetaLen n_max :=
    gmTailPtrFlatIdx_lt hb_pos hd_last_lt
  have ht_del_cap : t_del < maxTailItems n_max := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have hown_del_lt : gmTailOwnerBase n_max + t_del < globalMetaLen n_max :=
    gmTailOwnerIdx_lt hb_pos ht_del_cap
  intro e_rb s1 e_ptr_del_idx e_tdel s2 e_ntails s3 e_own_last_idx e_dlast
  have herb : e_rb = gm (gmRIdx d.2) := clientResult_readGMProg s hr_idx_lt
  have hs1 : s1 = s := rfl
  have heptr : e_ptr_del_idx = gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + r_del) := by
    dsimp only [e_ptr_del_idx]; rw [herb]
  have hetdel : e_tdel = t_del := by
    dsimp only [e_tdel]; rw [hs1, heptr]; exact clientResult_readGMProg s hptr_del_lt
  have hs2 : s2 = s := rfl
  have hentails : e_ntails = gm 1 := by
    dsimp only [e_ntails]; rw [hs2]; exact clientResult_readGMProg s h1_lt
  have hs3 : s3 = s := rfl
  have heown : e_own_last_idx = gmTailOwnerBase n_max + t_last := by
    dsimp only [e_own_last_idx]; rw [hentails]
  have hedlast : e_dlast = d_last := by
    dsimp only [e_dlast]; rw [hs3, heown]; exact clientResult_readGMProg s hown_last_lt
  refine ⟨hr_idx_lt, by rw [herb]; exact hr_pos, by rw [heptr]; exact hptr_del_lt, h1_lt,
    by rw [hentails]; exact hgm1_pos, by rw [heown]; exact hown_last_lt,
    by rw [hentails]; omega, by rw [hetdel]; omega,
    by rw [hentails]; omega, by rw [hetdel]; omega,
    by rw [hedlast]; exact hptr_last_lt, by rw [hetdel]; exact hown_del_lt⟩

theorem realizes_removeLastTailItemGen :
    Realizes .exact removeLastTailItemGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      RemoveLastTailItemGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  have hrq := realizes_readQuotGen
  have hwq := realizes_writeQuotGen
  have hrv := realizes_readValGen
  have hwv := realizes_writeValGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let r_idx ← pure (4 + 3 * d.2.2 + 1)
      let r_b ← readGMGenProg (d.1, (d.2.1, r_idx))
      let r_del ← pure (r_b - 1)
      let ptr_del_idx ← pure (dpGmTailPtrBase d.1 + (d.2.2 * dpTailCap d.1 + r_del))
      let t_del ← readGMGenProg (d.1, (d.2.1, ptr_del_idx))
      let i1 ← pure 1
      let n_tails ← readGMGenProg (d.1, (d.2.1, i1))
      let t_last ← pure (n_tails - 1)
      let own_last_idx ← pure (dpGmTailOwnerBase d.1 + t_last)
      let d_last ← readGMGenProg (d.1, (d.2.1, own_last_idx))
      let g_last ← pure (dpNMaxSubOne d.1 - t_last)
      let g_del ← pure (dpNMaxSubOne d.1 - t_del)
      let q_move ← readQuotGenProg (d.1, (d.2.1, g_last))
      writeQuotGenProg (d.1, ((d.2.1, g_del), q_move))
      let v_move ← readValGenProg (d.1, (d.2.1, g_last))
      writeValGenProg (d.1, ((d.2.1, g_del), v_move))
      let ptr_last_idx ← pure (dpGmTailPtrBase d.1 + d_last)
      writeGMGenProg (d.1, ((d.2.1, ptr_last_idx), t_del))
      let own_del_idx ← pure (dpGmTailOwnerBase d.1 + t_del)
      writeGMGenProg (d.1, ((d.2.1, own_del_idx), d_last))
      writeGMGenProg (d.1, ((d.2.1, r_idx), r_del))
      writeGMGenProg (d.1, ((d.2.1, i1), t_last))) ?_
    (fun d => by simp [removeLastTailItemGenProg, ← PFunctor.FreeM.bind_eq_bind])
  realizeDictWith [removeLastTailItemGenPre_mk]
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (removeLastTailItem_bounds h).1)
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact (removeLastTailItem_bounds h).1
  · exact (removeLastTailItem_bounds h).2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (removeLastTailItem_bounds h).2.2.1)
  · exact (removeLastTailItem_bounds h).2.2.1
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact (removeLastTailItem_bounds h).2.2.2.1
  · exact (removeLastTailItem_bounds h).2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (removeLastTailItem_bounds h).2.2.2.2.2.1)
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.1
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.2.1
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.2.2.1
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.2.2.2.1
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (removeLastTailItem_bounds h).2.2.2.2.2.2.2.2.2.2.1)
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.2.2.2.2.2.1
  · exact fits_of_le_globalMetaLen h.1 h.2.2.2.2 hw hnU hU
      (le_of_lt (removeLastTailItem_bounds h).2.2.2.2.2.2.2.2.2.2.2)
  · exact (removeLastTailItem_bounds h).2.2.2.2.2.2.2.2.2.2.2

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
