/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import Complexity.Tactic.Realize

/-!
# Amortized `O(1)` Slot Allocation and Deallocation in `Memory.Prog`

This module combines the tail-item operations (`appendTailItemProg`, `removeLastTailItemProg`) and
the `K`-step slab promotion/demotion loops (`promoteSlabProg`, `demoteSlabProg`) into the high-level
bucket-local slot operations:
* `lastSlotOfProg`: resolves the last logical slot `bCount n_max gm b - 1` of a non-empty bucket `b`
  in `O(1)` worst-case memory accesses;
* `pushBackSlotProg`: appends `(q_val, v_val)` at logical slot `bCount n_max gm b` of bucket `b`,
  promoting `K` tail items into a full slab when `r_b + 1 = 2 * K`, with `O(1)` amortized cost
  against `66 * slotPotential n_max gm`;
* `popBackSlotProg`: removes the last logical slot `bCount n_max gm b - 1` of bucket `b`, demoting
  the top full slab into `K` tail items when `r_b' = 0 ∧ 0 < q_b`, with `O(1)` amortized cost
  against `66 * slotPotential n_max gm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.totalSlots`: total active slots across all
  buckets (`gm 0` in the single-bucket regime, `gm 0 * slabSize n_max + gm 1` in the multi-bucket
  regime).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lastSlotOfProg`: `Memory.Prog` operation
  resolving `slotOf n_max gm b (bCount n_max gm b - 1)`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.pushBackSlotProg`: `Memory.Prog` operation
  appending `(q_val, v_val)` to bucket `b` with hysteresis promotion.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.popBackSlotProg`: `Memory.Prog` operation
  removing the last item of bucket `b` with hysteresis demotion.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slotPotential_pushBack_le`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slotPotential_popBack_le`: global hysteresis
  potential bounds under `pushBackCounts` and `popBackCounts`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.totalSlots_eq_sum_bCount`: `totalSlots` equals
  the sum of `bCount` across all buckets.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.pushBackSlotProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_pushBackSlotGen`: effect, amortized
  `memoryCost` bound, and `Realizes` certificate for `pushBackSlotProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.popBackSlotProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_popBackSlotGen`: effect, amortized
  `memoryCost` bound, and `Realizes` certificate for `popBackSlotProg`.
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

/-! ## Section 1: `totalSlots`, hysteresis potential bounds, and `lastSlotOfProg` -/

/-- Total number of active slots across all buckets in `GlobalMeta`:
* `gm 0` in the single-bucket regime (`bucketBits n_max = 0`);
* `gm 0 * slabSize n_max + gm 1` in the multi-bucket regime (`0 < bucketBits n_max`). -/
@[expose]
def totalSlots (n_max : ℕ) (gm : ℕ → ℕ) : ℕ :=
  if bucketBits n_max = 0 then gm 0
  else gm 0 * slabSize n_max + gm 1

theorem totalSlots_of_zero (n_max : ℕ) {gm : ℕ → ℕ} (hzero : ∀ i, gm i = 0) :
    totalSlots n_max gm = 0 := by
  unfold totalSlots
  split_ifs <;> simp [hzero]

theorem totalSlots_le {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm) :
    totalSlots n_max gm ≤ n_max := by
  unfold totalSlots
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · rw [ite_eq_left hb0]
    exact hinv.single_valid hb0
  · rw [ite_eq_right (by omega)]
    exact hinv.multi_total_le hb_pos

theorem bCount_le_totalSlots {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm)
    (b : ℕ) (hb : b < numBuckets n_max) :
    bCount n_max gm b ≤ totalSlots n_max gm := by
  unfold bCount totalSlots
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · simp only [hb0, ↓reduceIte]
    split_ifs <;> omega
  · have hb_ne : bucketBits n_max ≠ 0 := by omega
    simp only [hb_ne, ↓reduceIte, hb]
    have hq_le := q_le_nslabs_of_slabBijection (hinv.multi_slab hb_pos) hb
    have hr_le := r_le_ntails_of_tailBijection (hinv.multi_tail hb_pos) hb
    have hmul : gm (gmQIdx b) * slabSize n_max ≤ gm 0 * slabSize n_max :=
      Nat.mul_le_mul_right _ hq_le
    omega

theorem pos_gmRIdx_of_pos_bCount {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hinv : SlotStoreInv n_max gm)
    (hb : b < numBuckets n_max) (hbc : 1 ≤ bCount n_max gm b) :
    1 ≤ gm (gmRIdx b) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  unfold bCount at hbc
  simp only [hb0, ↓reduceIte, hb] at hbc
  have hrb := (hinv.multi_r_bounds hb_pos b hb).2
  by_cases hq : 0 < gm (gmQIdx b)
  · exact hrb hq
  · have hq0 : gm (gmQIdx b) = 0 := by omega
    rw [hq0, Nat.zero_mul, Nat.zero_add] at hbc
    exact hbc

/-- Global potential bound when bucket `b` transitions according to `pushBackCounts`. -/
theorem slotPotential_pushBack_le {n_max b : ℕ} {gm gm' : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hb_upd : gm' (gmQIdx b) = (pushBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).1 ∧
      gm' (gmRIdx b) = (pushBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).2)
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm (gmQIdx b') ∧ gm' (gmRIdx b') = gm (gmRIdx b')) :
    slotPotential n_max gm' + pushBackWork (slabSize n_max) (gm (gmRIdx b)) ≤
      slotPotential n_max gm + 1 := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  unfold slotPotential
  rw [ite_eq_right hb0, ite_eq_right hb0]
  have hmem : b ∈ Finset.range (numBuckets n_max) := Finset.mem_range.mpr hb
  rw [← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase (Finset.range (numBuckets n_max))
      (fun b' => bucketPotential (slabSize n_max) (gm (gmQIdx b')) (gm (gmRIdx b'))) hmem]
  have hsum_eq :
      ∑ x ∈ (Finset.range (numBuckets n_max)).erase b,
        bucketPotential (slabSize n_max) (gm' (gmQIdx x)) (gm' (gmRIdx x)) =
      ∑ x ∈ (Finset.range (numBuckets n_max)).erase b,
        bucketPotential (slabSize n_max) (gm (gmQIdx x)) (gm (gmRIdx x)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hx
    rw [Finset.mem_range] at hlt
    rw [(hother x hlt hne).1, (hother x hlt hne).2]
  rw [hsum_eq, hb_upd.1, hb_upd.2]
  have hpt := bucketPotential_pushBack_le (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))
  omega

/-- Global potential bound when bucket `b` transitions according to `popBackCounts`. -/
theorem slotPotential_popBack_le {n_max b : ℕ} {gm gm' : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hr1 : 1 ≤ gm (gmRIdx b)) (hr2 : gm (gmRIdx b) < 2 * slabSize n_max)
    (hb_upd : gm' (gmQIdx b) = (popBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).1 ∧
      gm' (gmRIdx b) = (popBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).2)
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm (gmQIdx b') ∧ gm' (gmRIdx b') = gm (gmRIdx b')) :
    slotPotential n_max gm' + popBackWork (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b)) ≤
      slotPotential n_max gm + 1 := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  unfold slotPotential
  rw [ite_eq_right hb0, ite_eq_right hb0]
  have hmem : b ∈ Finset.range (numBuckets n_max) := Finset.mem_range.mpr hb
  rw [← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase (Finset.range (numBuckets n_max))
      (fun b' => bucketPotential (slabSize n_max) (gm (gmQIdx b')) (gm (gmRIdx b'))) hmem]
  have hsum_eq :
      ∑ x ∈ (Finset.range (numBuckets n_max)).erase b,
        bucketPotential (slabSize n_max) (gm' (gmQIdx x)) (gm' (gmRIdx x)) =
      ∑ x ∈ (Finset.range (numBuckets n_max)).erase b,
        bucketPotential (slabSize n_max) (gm (gmQIdx x)) (gm (gmRIdx x)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hx
    rw [Finset.mem_range] at hlt
    rw [(hother x hlt hne).1, (hother x hlt hne).2]
  rw [hsum_eq, hb_upd.1, hb_upd.2]
  have hpt := bucketPotential_popBack_le (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b)) hr1 hr2
  omega

/-- Under `SlabBijection`, `n_slabs` equals the sum of per-bucket slab counts `q_fn b`. -/
theorem nslabs_eq_sum {n_max : ℕ} {gm : ℕ → ℕ} {q_fn : ℕ → ℕ} {n_slabs : ℕ}
    (hslab : SlabBijection n_max gm q_fn n_slabs) :
    n_slabs = ∑ b ∈ Finset.range (numBuckets n_max), q_fn b := by
  have hcard :
      ((Finset.range (numBuckets n_max)).sigma (fun b => Finset.range (q_fn b))).card =
        (Finset.range n_slabs).card := by
    refine Finset.card_bij (fun x _ => slabPtrOf n_max gm x.1 x.2) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hx
      exact Finset.mem_range.mpr (hslab.ptr_lt x.1 hx.1 x.2 hx.2)
    · intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hx₁ hx₂
      have hB1 := hslab.ownerB_ptr x₁.1 hx₁.1 x₁.2 hx₁.2
      have hB2 := hslab.ownerB_ptr x₂.1 hx₂.1 x₂.2 hx₂.2
      have hS1 := hslab.ownerS_ptr x₁.1 hx₁.1 x₁.2 hx₁.2
      have hS2 := hslab.ownerS_ptr x₂.1 hx₂.1 x₂.2 hx₂.2
      rw [heq] at hB1 hS1
      ext
      · exact hB1.symm.trans hB2
      · exact heq_of_eq (hS1.symm.trans hS2)
    · intro p hp
      rw [Finset.mem_range] at hp
      obtain ⟨hb, hs, hptr⟩ := hslab.owner_valid p hp
      refine ⟨⟨gm (gmSlabOwnerBIdx n_max p), gm (gmSlabOwnerSIdx n_max p)⟩, ?_, hptr⟩
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
      exact ⟨hb, hs⟩
  rw [Finset.card_sigma, Finset.card_range] at hcard
  rw [← hcard]
  exact Finset.sum_congr rfl fun b _ => Finset.card_range (q_fn b)

/-- Under `TailBijection`, `n_tails` equals the sum of per-bucket tail counts `r_fn b`. -/
theorem ntails_eq_sum {n_max : ℕ} {gm : ℕ → ℕ} {r_fn : ℕ → ℕ} {n_tails : ℕ}
    (htail : TailBijection n_max gm r_fn n_tails) :
    n_tails = ∑ b ∈ Finset.range (numBuckets n_max), r_fn b := by
  have hcard :
      ((Finset.range (numBuckets n_max)).sigma (fun b => Finset.range (r_fn b))).card =
        (Finset.range n_tails).card := by
    refine Finset.card_bij (fun x _ => gm (gmTailPtrIdx n_max x.1 x.2)) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hx
      exact Finset.mem_range.mpr (htail.ptr_lt x.1 hx.1 x.2 hx.2)
    · intro x₁ hx₁ x₂ hx₂ heq
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hx₁ hx₂
      have hO1 := htail.owner_ptr x₁.1 hx₁.1 x₁.2 hx₁.2
      have hO2 := htail.owner_ptr x₂.1 hx₂.1 x₂.2 hx₂.2
      have hr1 := lt_of_lt_of_le hx₁.2 (htail.r_le x₁.1 hx₁.1)
      have hr2 := lt_of_lt_of_le hx₂.2 (htail.r_le x₂.1 hx₂.1)
      have hC : 0 < tailCapPerBucket n_max := by omega
      rw [heq] at hO1
      have hd_eq : x₁.1 * tailCapPerBucket n_max + x₁.2 =
          x₂.1 * tailCapPerBucket n_max + x₂.2 := hO1.symm.trans hO2
      have hdiv : (x₁.1 * tailCapPerBucket n_max + x₁.2) / tailCapPerBucket n_max =
          (x₂.1 * tailCapPerBucket n_max + x₂.2) / tailCapPerBucket n_max :=
        congrArg (· / tailCapPerBucket n_max) hd_eq
      rw [Nat.mul_comm x₁.1, Nat.mul_add_div hC, Nat.div_eq_of_lt hr1, Nat.add_zero,
        Nat.mul_comm x₂.1, Nat.mul_add_div hC, Nat.div_eq_of_lt hr2, Nat.add_zero] at hdiv
      ext
      · exact hdiv
      · apply heq_of_eq
        rw [hdiv] at hd_eq
        omega
    · intro t ht
      rw [Finset.mem_range] at ht
      obtain ⟨hb, hr, hptr⟩ := htail.owner_valid t ht
      let d := gm (gmTailOwnerIdx n_max t)
      refine ⟨⟨d / tailCapPerBucket n_max, d % tailCapPerBucket n_max⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
        exact ⟨hb, hr⟩
      · dsimp only [gmTailPtrIdx]
        rw [Nat.div_add_mod' d (tailCapPerBucket n_max)]
        exact hptr
  rw [Finset.card_sigma, Finset.card_range] at hcard
  rw [← hcard]
  exact Finset.sum_congr rfl fun b _ => Finset.card_range (r_fn b)

/-- In the multi-bucket regime (`0 < bucketBits n_max`), the total active slot count
`gm 0 * slabSize n_max + gm 1` equals the sum of per-bucket item counts `bCount n_max gm b`. -/
theorem total_eq_sum_bCount {n_max : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max gm (fun b => gm (gmRIdx b)) (gm 1))
    (hslab : SlabBijection n_max gm (fun b => gm (gmQIdx b)) (gm 0)) :
    gm 0 * slabSize n_max + gm 1 =
      ∑ b ∈ Finset.range (numBuckets n_max), bCount n_max gm b := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  rw [nslabs_eq_sum hslab, ntails_eq_sum htail, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mem_range] at hb
  unfold bCount
  simp [hb0, hb]

/-- Under `SlotStoreInv n_max gm`, `totalSlots n_max gm` equals the sum of `bCount n_max gm b`
over all buckets `b < numBuckets n_max`. -/
theorem totalSlots_eq_sum_bCount {n_max : ℕ} {gm : ℕ → ℕ}
    (hinv : SlotStoreInv n_max gm) :
    totalSlots n_max gm =
      ∑ b ∈ Finset.range (numBuckets n_max), bCount n_max gm b := by
  unfold totalSlots
  by_cases hb0 : bucketBits n_max = 0
  · have hB1 : numBuckets n_max = 1 := by simp [numBuckets, hb0]
    simp [hb0, hB1, bCount]
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    rw [ite_eq_right hb0]
    exact total_eq_sum_bCount hb_pos (hinv.multi_tail hb_pos) (hinv.multi_slab hb_pos)

/-- `promoteSlabProg` preserves `gm 0 * slabSize n_max + gm 1`. -/
theorem promoteSlabProg_tot_eq {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hpre : PromoteSlabInv U V w n_max h_space base b s) :
    gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b))).mem 0 *
        slabSize n_max +
      gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b))).mem 1 =
      gmAt base U V w n_max h_space s.mem 0 * slabSize n_max +
        gmAt base U V w n_max h_space s.mem 1 := by
  obtain ⟨_, _, _, hinv', _, _, _, hbc, _, _⟩ := promoteSlabProg_effect hw hb_pos s hpre
  rw [total_eq_sum_bCount hb_pos (hinv'.multi_tail hb_pos) (hinv'.multi_slab hb_pos),
    total_eq_sum_bCount hb_pos hpre.2.1 hpre.2.2.1]
  exact Finset.sum_congr rfl fun b' hb' => hbc b' (Finset.mem_range.mp hb')

/-- `demoteSlabProg` preserves `gm 0 * slabSize n_max + gm 1`. -/
theorem demoteSlabProg_tot_eq {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hpre : DemoteSlabInv U V w n_max h_space base b s) :
    gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b))).mem 0 *
        slabSize n_max +
      gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b))).mem 1 =
      gmAt base U V w n_max h_space s.mem 0 * slabSize n_max +
        gmAt base U V w n_max h_space s.mem 1 := by
  obtain ⟨_, _, _, hinv', _, _, _, hbc, _, _⟩ := demoteSlabProg_effect hw hb_pos s hpre
  rw [total_eq_sum_bCount hb_pos (hinv'.multi_tail hb_pos) (hinv'.multi_slab hb_pos),
    total_eq_sum_bCount hb_pos hpre.2.1 hpre.2.2.1]
  exact Finset.sum_congr rfl fun b' hb' => hbc b' (Finset.mem_range.mp hb')

/-- Parameter-free `Memory.Prog` operation resolving the physical slot
`slotOf n_max gm b (bCount n_max gm b - 1)` of the last item in a non-empty bucket `b = d.2.2`
at `base = d.2.1` (`1 ≤ bCount n_max gm b`). -/
def lastSlotOfGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  if dpBucketBits d.1 = 0 then do
    let c ← readGMGenProg (d.1, (d.2.1, 0))
    pure (c - 1)
  else do
    let r_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
    let t_last ← readGMGenProg
      (d.1, (d.2.1, dpGmTailPtrBase d.1 + (d.2.2 * dpTailCap d.1 + (r_b - 1))))
    pure (dpNMaxSubOne d.1 - t_last)

/-- `Memory.Prog` operation resolving the physical slot `slotOf n_max gm b (bCount n_max gm b - 1)`
of the last item in a non-empty bucket `b = d.2` at `base = d.1` (`1 ≤ bCount n_max gm b`). -/
def lastSlotOfProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  if bucketBits n_max = 0 then do
    let c ← readGMProg U V w n_max h_space (d.1, 0)
    pure (c - 1)
  else do
    let r_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 1)
    let t_last ← readGMProg U V w n_max h_space
      (d.1, gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + (r_b - 1)))
    pure ((n_max - 1) - t_last)

@[simp] theorem lastSlotOfGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    lastSlotOfGenProg (mkDictParams U V w n_max h_space, d) =
      lastSlotOfProg U V w n_max h_space d := by
  by_cases hb0 : bucketBits n_max = 0 <;>
    simp [lastSlotOfGenProg, lastSlotOfProg, hb0, ← PFunctor.FreeM.bind_eq_bind]

/-- Parameter-free precondition for `lastSlotOfGenProg`. -/
@[expose]
def LastSlotOfGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 d.2.1 ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm d.2.2

@[simp] theorem lastSlotOfGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    LastSlotOfGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      (DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1 ∧
        SlotStoreInv n_max (gmAt d.1 U V w₀ n_max h_space s.mem) ∧
        d.2 < numBuckets n_max ∧
        1 ≤ bCount n_max (gmAt d.1 U V w₀ n_max h_space s.mem) d.2) := Iff.rfl

theorem clientState_lastSlotOfProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (lastSlotOfProg U V w n_max h_space d) = s := by
  unfold lastSlotOfProg
  split_ifs <;> rfl

theorem memoryCost_lastSlotOfProg_le (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (lastSlotOfProg U V w n_max h_space d) s ≤ 4 := by
  unfold lastSlotOfProg
  split_ifs
  · change 2 ≤ 4; omega
  · change 4 ≤ 4; omega

theorem clientResult_lastSlotOfProg {U V w n_max h_space : ℕ} (d : ℕ × ℕ) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem))
    (hb : d.2 < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2) :
    (Memory.spec 0).clientResult s (lastSlotOfProg U V w n_max h_space d) =
      slotOf n_max (gmAt d.1 U V w n_max h_space s.mem) d.2
        (bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 - 1) := by
  let gm := gmAt d.1 U V w n_max h_space s.mem
  unfold lastSlotOfProg
  by_cases hb0 : bucketBits n_max = 0
  · have hd2 : d.2 = 0 := by
      have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
      omega
    have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    simp only [hb0, ↓reduceIte, StateTransitionSpec.clientResult_bind,
      clientResult_readGMProg s h0_lt]
    unfold slotOf bCount
    simp only [hb0, ↓reduceIte, hd2]
    rfl
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hr_pos : 1 ≤ gm (gmRIdx d.2) := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hr_cap : gm (4 + 3 * d.2 + 1) - 1 < tailCapPerBucket n_max := by
      have : gm (gmRIdx d.2) < tailCapPerBucket n_max := (hinv.multi_r_bounds hb_pos d.2 hb).1
      unfold gmRIdx at this
      omega
    have hptr_lt :
        gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + (gm (4 + 3 * d.2 + 1) - 1)) <
          globalMetaLen n_max := gmTailPtrIdx_lt hb_pos hb hr_cap
    simp only [hb0, ↓reduceIte]
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hr_idx_lt,
      StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s hptr_lt]
    unfold slotOf bCount
    simp only [hb0, ↓reduceIte, hb]
    have hnot : ¬(gm (gmQIdx d.2) * slabSize n_max + gm (gmRIdx d.2) - 1 <
        gm (gmQIdx d.2) * slabSize n_max) := by omega
    rw [ite_eq_right hnot]
    have hsub : gm (gmQIdx d.2) * slabSize n_max + gm (gmRIdx d.2) - 1 -
        gm (gmQIdx d.2) * slabSize n_max = gm (gmRIdx d.2) - 1 := by omega
    rw [hsub]
    rfl

theorem realizes_lastSlotOfGen :
    Realizes .exact lastSlotOfGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      LastSlotOfGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let z ← pure 0
      if dpBucketBits d.1 = z then
        let c ← readGMGenProg (d.1, (d.2.1, z))
        pure (c - 1)
      else
        let r_idx ← pure (4 + 3 * d.2.2 + 1)
        let r_b ← readGMGenProg (d.1, (d.2.1, r_idx))
        let ptr_idx ← pure (dpGmTailPtrBase d.1 + (d.2.2 * dpTailCap d.1 + (r_b - 1)))
        let t_last ← readGMGenProg (d.1, (d.2.1, ptr_idx))
        pure (dpNMaxSubOne d.1 - t_last)) ?_
    (fun d => by
      simp only [lastSlotOfGenProg, ← PFunctor.FreeM.bind_eq_bind, pure_bind])
  realizeDictWith [lastSlotOfGenPre_mk]
  · exact h.1
  · unfold globalMetaLen; omega
  · have hd2 : d.2 = 0 := by
      have := h.2.2.1
      have : numBuckets n_max = 1 := by simp [numBuckets, hc]
      omega
    have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg _ h0_lt]
    have hbc := h.2.2.2
    unfold bCount at hbc
    simp only [hc, ↓reduceIte, hd2] at hbc
    exact hbc
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmRIdx_lt hb_pos h.2.2.1))
  · refine fits_const_of_dictEnv h.1 ?_; omega
  · exact h.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact gmRIdx_lt hb_pos h.2.2.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.2.1
    rw [clientResult_readGMProg _ hr_idx_lt]
    exact pos_gmRIdx_of_pos_bCount hb_pos h.2.1 h.2.2.1 h.2.2.2
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.2.1
    rw [clientResult_readGMProg _ hr_idx_lt]
    have hr_cap :
        gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2 + 1) - 1 < tailCapPerBucket n_max := by
      have := (h.2.1.multi_r_bounds hb_pos d.2 h.2.2.1).1; unfold gmRIdx at this; omega
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU
      (le_of_lt (gmTailPtrIdx_lt hb_pos h.2.2.1 hr_cap))
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.2.1
    rw [clientResult_readGMProg _ hr_idx_lt]
    have hr_cap :
        gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2 + 1) - 1 < tailCapPerBucket n_max := by
      have := (h.2.1.multi_r_bounds hb_pos d.2 h.2.2.1).1; unfold gmRIdx at this; omega
    exact gmTailPtrIdx_lt hb_pos h.2.2.1 hr_cap
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    have hr_idx_lt : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos h.2.2.1
    have hr_pos := pos_gmRIdx_of_pos_bCount hb_pos h.2.1 h.2.2.1 h.2.2.2
    have hr_cap :
        gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2 + 1) - 1 < tailCapPerBucket n_max := by
      have := (h.2.1.multi_r_bounds hb_pos d.2 h.2.2.1).1; unfold gmRIdx at this; omega
    have hptr_lt : gmTailPtrBase n_max +
        (d.2 * tailCapPerBucket n_max +
          (gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2 + 1) - 1)) <
        globalMetaLen n_max := gmTailPtrIdx_lt hb_pos h.2.2.1 hr_cap
    rw [clientState_readGMProg, clientResult_readGMProg _ hr_idx_lt,
      clientResult_readGMProg _ hptr_lt]
    have htail := h.2.1.multi_tail hb_pos
    unfold gmRIdx at hr_pos
    have ht_lt := htail.ptr_lt d.2 h.2.2.1
      (gmAt d.1 U V w₀ n_max h_space s.mem (4 + 3 * d.2 + 1) - 1)
      (by unfold gmRIdx; omega)
    have htot := h.2.1.multi_total_le hb_pos
    unfold gmTailPtrIdx gmTailPtrFlatIdx at ht_lt
    omega

/-! ## Section 2: `pushBackSlotProg` via `realize` -/

/-- Parameter-free helper `Memory.Prog` for the multi-bucket prefix of `pushBackSlotGenProg`. -/
def pushBackTailWriteGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let dp := d.1.1.1
  let base := d.1.1.2.1
  let b := d.1.1.2.2
  let q_val := d.1.2
  let v_val := d.2
  let t_new ← appendTailItemGenProg (dp, (base, b))
  let g_new := dpNMaxSubOne dp - t_new
  writeQuotGenProg (dp, ((base, g_new), q_val))
  writeValGenProg (dp, ((base, g_new), v_val))
  readGMGenProg (dp, (base, 4 + 3 * b + 1))

/-- Helper `Memory.Prog` for the multi-bucket prefix of `pushBackSlotProg`: appends one tail item
to bucket `b = d.1.1.2` at `base = d.1.1.1`, writes `(q_val, v_val) = (d.1.2, d.2)` into its
physical slot, and returns the updated tail count `r_b_new = gm' (gmRIdx b)`. -/
def pushBackTailWriteProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let base := d.1.1.1
  let b := d.1.1.2
  let q_val := d.1.2
  let v_val := d.2
  let t_new ← appendTailItemProg U V w n_max h_space (base, b)
  let g_new := (n_max - 1) - t_new
  writeQuotProg U w n_max h_space ((base, g_new), q_val)
  writeValProg U V w n_max h_space ((base, g_new), v_val)
  readGMProg U V w n_max h_space (base, 4 + 3 * b + 1)

@[simp] theorem pushBackTailWriteGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    pushBackTailWriteGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      pushBackTailWriteProg U V w n_max h_space ((d1, d2), d3) := by
  simp only [pushBackTailWriteGenProg, pushBackTailWriteProg, p_nMaxSubOne_mk,
    appendTailItemGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, readGMGenProg_mk]

@[simp]
theorem memoryCost_pushBackTailWriteProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (pushBackTailWriteProg U V w n_max h_space d) s = 30 := by
  simp [pushBackTailWriteProg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]

/-- Pure state effect and return value of `pushBackTailWriteProg`. -/
theorem pushBackTailWriteProg_effect {U V w n_max h_space base b q_val v_val : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (htot : totalSlots n_max (gmAt base U V w n_max h_space s.mem) < n_max)
    (hq_lt : q_val < 2 ^ quotientBits U n_max)
    (hv_lt : v_val < 2 ^ valBits V) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let d := (((base, b), q_val), v_val)
    let s₁ := (Memory.spec 0).clientState s (pushBackTailWriteProg U V w n_max h_space d)
    let gm₁ := gmAt base U V w n_max h_space s₁.mem
    (Memory.spec 0).clientResult s (pushBackTailWriteProg U V w n_max h_space d) =
      gm₀ (gmRIdx b) + 1 ∧
    s₁.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s₁.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s₁.mem = lmAt base U V w n_max h_space s.mem ∧
    gm₁ = gmAppendTail n_max gm₀ b ∧
    TailBijection n_max gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) ∧
    SlabBijection n_max gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) ∧
    gm₁ 0 * slabSize n_max + gm₁ 1 = gm₀ 0 * slabSize n_max + gm₀ 1 + 1 ∧
    gm₁ (gmQIdx b) = gm₀ (gmQIdx b) ∧
    gm₁ (gmRIdx b) = gm₀ (gmRIdx b) + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm₁ (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm₁ (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    bCount n_max gm₁ b = bCount n_max gm₀ b + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm₁ b' = bCount n_max gm₀ b') ∧
    quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b (bCount n_max gm₀ b)) = q_val ∧
    valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b (bCount n_max gm₀ b)) = v_val ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
      quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) := by
  intro gm₀ d s₁ gm₁
  change SlotStoreInv n_max gm₀ at hinv
  change totalSlots n_max gm₀ < n_max at htot
  have hb0 : bucketBits n_max ≠ 0 := by omega
  unfold totalSlots at htot
  rw [ite_eq_right hb0] at htot
  have htail₀ := hinv.multi_tail hb_pos
  have hslab₀ := hinv.multi_slab hb_pos
  have hr_lt : gm₀ (gmRIdx b) < tailCapPerBucket n_max := (hinv.multi_r_bounds hb_pos b hb).1
  have ht_lt : gm₀ 1 < maxTailItems n_max := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  obtain ⟨hres_app, hf_app, hout_app, hq_app, hv_app, hl_app, hgm_app⟩ :=
    appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail₀ hr_lt
  let s_app := (Memory.spec 0).clientState s (appendTailItemProg U V w n_max h_space (base, b))
  let g_new := (n_max - 1) - gm₀ 1
  have hg_new_lt : g_new < n_max := by dsimp only [g_new]; omega
  obtain ⟨hf_wq, hout_wq, hq_wq, hv_wq, hl_wq, hgm_wq⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw hg_new_lt hq_lt s_app
  let s_wq := (Memory.spec 0).clientState s_app
    (writeQuotProg U w n_max h_space ((base, g_new), q_val))
  obtain ⟨hf_wv, hout_wv, hq_wv, hv_wv, hl_wv, hgm_wv⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw hg_new_lt hv_lt s_wq
  let s_wv := (Memory.spec 0).clientState s_wq
    (writeValProg U V w n_max h_space ((base, g_new), v_val))
  have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have hst : s₁ = s_wv := by
    change (Memory.spec 0).clientState s (pushBackTailWriteProg U V w n_max h_space d) = s_wv
    unfold pushBackTailWriteProg
    dsimp only [d]
    rw [StateTransitionSpec.clientState_bind, hres_app,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readGMProg]
  have hgm1_eq : gm₁ = gmAppendTail n_max gm₀ b := by
    dsimp only [gm₁]; rw [hst, hgm_wv, hgm_wq, hgm_app]
  have hpres := gmAppendTail_preserves_nonTail gm₀ hb hr_lt ht_lt
  have hres : (Memory.spec 0).clientResult s (pushBackTailWriteProg U V w n_max h_space d) =
      gm₀ (gmRIdx b) + 1 := by
    unfold pushBackTailWriteProg
    dsimp only [d]
    rw [StateTransitionSpec.clientResult_bind, hres_app,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      clientResult_readGMProg s_wv hr_idx_lt, ← hst]
    change gm₁ (gmRIdx b) = gm₀ (gmRIdx b) + 1
    rw [hgm1_eq, hpres.2.2.1]
  have htail₁ := tailBijection_gmAppendTail hb hr_lt ht_lt htail₀
  have ⟨_, hslab₁⟩ := slabBijection_gmAppendTail hb hr_lt ht_lt hslab₀
  have hslot_app := slotOf_gmAppendTail hb_pos hb hr_lt ht_lt htail₀ hslab₀
  have hbc_b0 : bCount n_max gm₀ b = gm₀ (gmQIdx b) * slabSize n_max + gm₀ (gmRIdx b) := by
    unfold bCount; simp [hb0, hb]
  have hbc_b1 : bCount n_max gm₁ b = bCount n_max gm₀ b + 1 := by
    unfold bCount
    simp only [hb0, ↓reduceIte, hb, hgm1_eq, hpres.2.2.2.2.1 b hb, hpres.2.2.1]
    omega
  have hbc_other : ∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm₁ b' = bCount n_max gm₀ b' := by
    intro b' hb' hne
    unfold bCount
    simp only [hb0, ↓reduceIte, hb', hgm1_eq, hpres.2.2.2.2.1 b' hb', hpres.2.2.2.1 b' hb' hne]
  have hslot_new : slotOf n_max gm₁ b (bCount n_max gm₀ b) = g_new := by
    rw [hgm1_eq, hbc_b0, hslot_app.1]
  have hslot_old_ne : ∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
      slotOf n_max gm₀ b' j ≠ g_new := by
    intro b' hb' j hj
    unfold bCount at hj
    simp only [hb0, ↓reduceIte, hb'] at hj
    unfold slotOf
    rw [ite_eq_right hb0]
    split_ifs with hj_slab
    · have hs_lt : j / slabSize n_max < gm₀ (gmQIdx b') :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hp_lt : slabPtrOf n_max gm₀ b' (j / slabSize n_max) < gm₀ 0 :=
        hslab₀.ptr_lt b' hb' _ hs_lt
      have hmod_lt : j % slabSize n_max < slabSize n_max := Nat.mod_lt j (slabSize_pos n_max)
      have h1 : (slabPtrOf n_max gm₀ b' (j / slabSize n_max) + 1) * slabSize n_max ≤
          gm₀ 0 * slabSize n_max := Nat.mul_le_mul_right _ hp_lt
      rw [Nat.add_one_mul] at h1
      dsimp only [g_new]
      omega
    · have hr'_lt : j - gm₀ (gmQIdx b') * slabSize n_max < gm₀ (gmRIdx b') := by omega
      have ht'_lt : gm₀ (gmTailPtrIdx n_max b' (j - gm₀ (gmQIdx b') * slabSize n_max)) < gm₀ 1 :=
        htail₀.ptr_lt b' hb' _ hr'_lt
      dsimp only [g_new]
      omega
  refine ⟨hres, by rw [hst, hf_wv, hf_wq, hf_app],
    fun a ha => by
      rw [hst,
        hout_wv a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
        hout_wq a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
        hout_app a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)],
    by rw [hst, hl_wv, hl_wq, hl_app],
    hgm1_eq,
    by rw [hgm1_eq]; exact htail₁,
    by rw [hgm1_eq]; exact hslab₁,
    by rw [hgm1_eq, hpres.1, hpres.2.1]; omega,
    by rw [hgm1_eq, hpres.2.2.2.2.1 b hb],
    by rw [hgm1_eq, hpres.2.2.1],
    fun b' hb' hne => ⟨by rw [hgm1_eq, hpres.2.2.2.2.1 b' hb'],
      by rw [hgm1_eq, hpres.2.2.2.1 b' hb' hne]⟩,
    hbc_b1, hbc_other,
    by rw [hst, hq_wv, hq_wq, hslot_new, Function.update_self],
    by rw [hst, hv_wv, hslot_new, Function.update_self],
    fun b' hb' j hj => ?_⟩
  rw [hst, hq_wv, hq_wq, hq_app, hv_wv, hv_wq, hv_app, hgm1_eq, hslot_app.2 b' hb' j hj,
    Function.update_of_ne (hslot_old_ne b' hb' j hj),
    Function.update_of_ne (hslot_old_ne b' hb' j hj)]
  exact ⟨rfl, rfl⟩

/-- Precondition for `pushBackSlotProg` in `Realizes`. -/
@[expose]
def PushBackSlotPre (U V w₀ n_max h_space w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  let base := d.1.1.1
  let b := d.1.1.2
  let q_val := d.1.2
  let v_val := d.2
  let gm := gmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max gm ∧
  b < numBuckets n_max ∧
  totalSlots n_max gm < n_max ∧
  q_val < 2 ^ quotientBits U n_max ∧
  v_val < 2 ^ valBits V

/-- Parameter-free precondition for `pushBackSlotGenProg`. -/
@[expose]
def PushBackSlotGenPre (w : ℕ) (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  let dp := d.1.1.1
  let base := d.1.1.2.1
  let b := d.1.1.2.2
  let q_val := d.1.2
  let v_val := d.2
  let gm := gmAt base (dpU dp) (dpV dp) (dpW dp) (dpNMax dp) (dpHSpace dp) s.mem
  DictEnvGen w dp base ∧
  SlotStoreInv (dpNMax dp) gm ∧
  b < numBuckets (dpNMax dp) ∧
  totalSlots (dpNMax dp) gm < dpNMax dp ∧
  q_val < 2 ^ quotientBits (dpU dp) (dpNMax dp) ∧
  v_val < 2 ^ valBits (dpV dp)

@[simp] theorem pushBackSlotGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) (s : Memory.State) :
    PushBackSlotGenPre w (((mkDictParams U V w₀ n_max h_space, d1), d2), d3) s ↔
      PushBackSlotPre U V w₀ n_max h_space w ((d1, d2), d3) s := Iff.rfl

/-- Parameter-free precondition for `pushBackTailWriteGenProg`. -/
@[expose]
def PushBackTailWriteGenPre (w : ℕ) (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  PushBackSlotGenPre w d s ∧ 0 < bucketBits (dpNMax d.1.1.1)

@[simp] theorem pushBackTailWriteGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) (s : Memory.State) :
    PushBackTailWriteGenPre w (((mkDictParams U V w₀ n_max h_space, d1), d2), d3) s ↔
      (PushBackSlotPre U V w₀ n_max h_space w ((d1, d2), d3) s ∧ 0 < bucketBits n_max) := Iff.rfl

private theorem appendTailItem_lt_n_max {U V w₀ n_max h_space w : ℕ}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State)
    (h : PushBackSlotPre U V w₀ n_max h_space w d s) :
    (Memory.spec 0).clientResult s (appendTailItemProg U V w₀ n_max h_space d.1.1) < n_max := by
  have hres := (appendTailItemProg_effect hw hb_pos h.2.2.1 s (h.2.1.multi_tail hb_pos)
    (h.2.1.multi_r_bounds hb_pos d.1.1.2 h.2.2.1).1).1
  have htot := h.2.2.2.1
  unfold totalSlots at htot
  rw [ite_eq_right (by omega)] at htot
  rcases d with ⟨⟨⟨base, b⟩, q_val⟩, v_val⟩
  dsimp only at hres htot ⊢
  omega

private theorem appendTailItem_le_n_max_sub_one {U V w₀ n_max h_space w : ℕ}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State)
    (h : PushBackSlotPre U V w₀ n_max h_space w d s) :
    (Memory.spec 0).clientResult s (appendTailItemProg U V w₀ n_max h_space d.1.1) ≤ n_max - 1 := by
  have := appendTailItem_lt_n_max hw hb_pos d s h
  omega

private theorem appendTailItem_sub_lt_n_max {U V w₀ n_max h_space w : ℕ}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State)
    (h : PushBackSlotPre U V w₀ n_max h_space w d s) :
    n_max - 1 - (Memory.spec 0).clientResult s (appendTailItemProg U V w₀ n_max h_space d.1.1) <
      n_max := by
  have := appendTailItem_lt_n_max hw hb_pos d s h
  omega

theorem realizes_pushBackTailWriteGen :
    Realizes .exact pushBackTailWriteGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PushBackTailWriteGenPre
      (fun _ _ => 0) := by
  have happ := realizes_appendTailItemGen
  have hwq := realizes_writeQuotGen
  have hwv := realizes_writeValGen
  have hrg := realizes_readGMGen
  refine Realizes.congr (p := fun d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ => do
      let t_new ← appendTailItemGenProg d.1.1
      let g_new ← pure (dpNMaxSubOne d.1.1.1 - t_new)
      writeQuotGenProg (d.1.1.1, ((d.1.1.2.1, g_new), d.1.2))
      writeValGenProg (d.1.1.1, ((d.1.1.2.1, g_new), d.2))
      let r_idx ← pure (4 + 3 * d.1.1.2.2 + 1)
      readGMGenProg (d.1.1.1, (d.1.1.2.1, r_idx))) ?_
    (fun d => by simp only [pushBackTailWriteGenProg, ← PFunctor.FreeM.bind_eq_bind, pure_bind])
  realize
  all_goals (
    rcases d with ⟨⟨⟨dp, base, b⟩, q_val⟩, v_val⟩
    let d : ((ℕ × ℕ) × ℕ) × ℕ := (((base, b), q_val), v_val)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1.1
    simpDictParamsWith [pushBackTailWriteGenPre_mk, pushBackSlotGenPre_mk,
      appendTailItemGenPre_mk, appendTailItemGenProg_mk]
    try dsimp only [d, PushBackSlotPre] at *
  )
  · exact ⟨h.1.1, h.1.2.1.multi_tail h.2, h.1.2.2.1,
      (h.1.2.1.multi_r_bounds h.2 d.1.1.2 h.1.2.2.1).1, h.2⟩
  · exact appendTailItem_le_n_max_sub_one hw h.2 d s h.1
  · exact h.1.1
  · exact appendTailItem_sub_lt_n_max hw h.2 d s h.1
  · refine fits_of_le_globalMetaLen h.1.1 h.2 hw hnU hU ?_
    have := gmRIdx_lt h.2 h.1.2.2.1; unfold gmRIdx at this; omega
  · refine fits_of_le_globalMetaLen h.1.1 h.2 hw hnU hU ?_
    have := gmRIdx_lt h.2 h.1.2.2.1; unfold gmRIdx at this; omega
  · exact gmRIdx_lt h.2 h.1.2.2.1

/-- Parameter-free `Memory.Prog` operation appending `(q_val, v_val) = (d.1.2, d.2)` at logical
slot `bCount n_max gm b` of bucket `b = d.1.1.2.2` at `base = d.1.1.2.1`. -/
def pushBackSlotGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog Unit :=
  if dpBucketBits d.1.1.1 = 0 then do
    let dp := d.1.1.1
    let base := d.1.1.2.1
    let q_val := d.1.2
    let v_val := d.2
    let c ← readGMGenProg (dp, (base, 0))
    writeQuotGenProg (dp, ((base, c), q_val))
    writeValGenProg (dp, ((base, c), v_val))
    writeGMGenProg (dp, ((base, 0), c + 1))
  else do
    let r_b_new ← pushBackTailWriteGenProg d
    if r_b_new = dpTwoSlabSize d.1.1.1 then
      promoteSlabGenProg d.1.1
    else
      pure ()

/-- `Memory.Prog` operation appending `(q_val, v_val) = (d.1.2, d.2)` at logical slot
`bCount n_max gm b` of bucket `b = d.1.1.2` at `base = d.1.1.1`, promoting `K` tail items into a
new full slab when `r_b + 1 = 2 * K`. -/
def pushBackSlotProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  if bucketBits n_max = 0 then do
    let base := d.1.1.1
    let q_val := d.1.2
    let v_val := d.2
    let c ← readGMProg U V w n_max h_space (base, 0)
    writeQuotProg U w n_max h_space ((base, c), q_val)
    writeValProg U V w n_max h_space ((base, c), v_val)
    writeGMProg U V w n_max h_space ((base, 0), c + 1)
  else do
    let r_b_new ← pushBackTailWriteProg U V w n_max h_space d
    if r_b_new = 2 * slabSize n_max then
      promoteSlabProg U V w n_max h_space d.1.1
    else
      pure ()

@[simp] theorem pushBackSlotGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    pushBackSlotGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      pushBackSlotProg U V w n_max h_space ((d1, d2), d3) := by
  simp only [pushBackSlotGenProg, pushBackSlotProg, p_bucketBits_mk, p_twoSlabSize_mk,
    readGMGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, writeGMGenProg_mk,
    pushBackTailWriteGenProg_mk, promoteSlabGenProg_mk]

/-- Pure state effect and amortized `memoryCost` bound of `pushBackSlotProg`. -/
theorem pushBackSlotProg_effect {U V w n_max h_space base b q_val v_val : ℕ}
    (hw : 0 < w) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (htot : totalSlots n_max (gmAt base U V w n_max h_space s.mem) < n_max)
    (hq_lt : q_val < 2 ^ quotientBits U n_max)
    (hv_lt : v_val < 2 ^ valBits V) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let d := (((base, b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s (pushBackSlotProg U V w n_max h_space d)
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    totalSlots n_max gm' = totalSlots n_max gm₀ + 1 ∧
    bCount n_max gm' b = bCount n_max gm₀ b + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b (bCount n_max gm₀ b)) = q_val ∧
    valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b (bCount n_max gm₀ b)) = v_val ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (pushBackSlotProg U V w n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 134 := by
  intro gm₀ d s' gm'
  change SlotStoreInv n_max gm₀ at hinv
  change totalSlots n_max gm₀ < n_max at htot
  by_cases hb0 : bucketBits n_max = 0
  · have hb_eq : b = 0 := by
      have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
      omega
    subst hb_eq
    unfold totalSlots at htot
    rw [ite_eq_left hb0] at htot
    change gm₀ 0 < n_max at htot
    have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    have hc1_lt : gm₀ 0 + 1 < 2 ^ globalPtrBits n_max :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
      writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw htot hq_lt s
    let s₁ := (Memory.spec 0).clientState s
      (writeQuotProg U w n_max h_space ((base, gm₀ 0), q_val))
    obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
      writeValProg_effect (base := base) (h_space := h_space) hw htot hv_lt s₁
    let s₂ := (Memory.spec 0).clientState s₁
      (writeValProg U V w n_max h_space ((base, gm₀ 0), v_val))
    obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
      writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw h0_lt hc1_lt s₂
    let s₃ := (Memory.spec 0).clientState s₂
      (writeGMProg U V w n_max h_space ((base, 0), gm₀ 0 + 1))
    have hst : s' = s₃ := by
      change (Memory.spec 0).clientState s (pushBackSlotProg U V w n_max h_space d) = s₃
      unfold pushBackSlotProg
      simp only [hb0, ↓reduceIte, d]
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s h0_lt]
      repeat rw [StateTransitionSpec.clientState_bind]
    have hgm'_eq : gm' = Function.update gm₀ 0 (gm₀ 0 + 1) := by
      dsimp only [gm']; rw [hst, hg3, hg2, hg1]
    have hinv' : SlotStoreInv n_max gm' := by
      refine ⟨fun _ => by rw [hgm'_eq, Function.update_self]; omega,
        fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
    have hbc0 : bCount n_max gm₀ 0 = gm₀ 0 := by unfold bCount; simp [hb0]
    have hbc' : bCount n_max gm' 0 = gm₀ 0 + 1 := by
      unfold bCount; simp [hb0, hgm'_eq]
    have hslot_eq : ∀ b' j, slotOf n_max gm' b' j = j ∧ slotOf n_max gm₀ b' j = j := by
      intro b' j; unfold slotOf; simp [hb0]
    refine ⟨by rw [hst, hf3, hf2, hf1],
      fun a ha => by
        rw [hst,
          hout3 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
          hout2 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega),
          hout1 a (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)],
      by rw [hst, hl3, hl2, hl1],
      hinv',
      by unfold totalSlots; simp [hb0, hgm'_eq],
      by rw [hbc', hbc0],
      fun b' hb' hne => by
        have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
        omega,
      by rw [hst, hq3, hq2, hq1, (hslot_eq 0 _).1, hbc0, Function.update_self],
      by rw [hst, hv3, hv2, (hslot_eq 0 _).1, hbc0, Function.update_self],
      fun b' hb' j hj => ?_, ?_⟩
    · have hb'_eq : b' = 0 := by
        have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
        omega
      subst hb'_eq
      rw [hbc0] at hj
      rw [hst, hq3, hq2, hq1, hv3, hv2, hv1, (hslot_eq 0 j).1, (hslot_eq 0 j).2,
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact ⟨rfl, rfl⟩
    · have hcost : memoryCost (pushBackSlotProg U V w n_max h_space d) s = 14 := by
        unfold pushBackSlotProg
        simp [hb0, d, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      have hpot' : slotPotential n_max gm' = 0 := by unfold slotPotential; simp [hb0]
      have hpot0 : slotPotential n_max gm₀ = 0 := by unfold slotPotential; simp [hb0]
      rw [hcost, hpot', hpot0]
      omega
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
    have hr0_lt : gm₀ (gmRIdx b) < 2 * slabSize n_max := by
      have := (hinv.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this
      rw [ite_eq_right hb0] at this
      exact this
    obtain ⟨hres1, hf1, hout1, hl1, hgm1_eq, htail1, hslab1, htot1, hqb1, hrb1, hother1,
        hbc_b1, hbc_other1, hq_new1, hv_new1, hold1⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos s hinv hb htot hq_lt hv_lt
    let s₁ := (Memory.spec 0).clientState s (pushBackTailWriteProg U V w n_max h_space d)
    let gm₁ := gmAt base U V w n_max h_space s₁.mem
    change (Memory.spec 0).clientResult s (pushBackTailWriteProg U V w n_max h_space d) =
      gm₀ (gmRIdx b) + 1 at hres1
    change gm₁ = gmAppendTail n_max gm₀ b at hgm1_eq
    change TailBijection n_max gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) at htail1
    change SlabBijection n_max gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) at hslab1
    change gm₁ 0 * slabSize n_max + gm₁ 1 = gm₀ 0 * slabSize n_max + gm₀ 1 + 1 at htot1
    change gm₁ (gmQIdx b) = gm₀ (gmQIdx b) at hqb1
    change gm₁ (gmRIdx b) = gm₀ (gmRIdx b) + 1 at hrb1
    change ∀ b' < numBuckets n_max, b' ≠ b →
      gm₁ (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm₁ (gmRIdx b') = gm₀ (gmRIdx b') at hother1
    change bCount n_max gm₁ b = bCount n_max gm₀ b + 1 at hbc_b1
    change ∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm₁ b' = bCount n_max gm₀ b' at hbc_other1
    change quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b (bCount n_max gm₀ b)) =
      q_val at hq_new1
    change valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b (bCount n_max gm₀ b)) =
      v_val at hv_new1
    change ∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
      quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j) at hold1
    have htot0_lt : gm₀ 0 * slabSize n_max + gm₀ 1 < n_max := by
      unfold totalSlots at htot; rw [ite_eq_right hb0] at htot; exact htot
    by_cases hprom : gm₀ (gmRIdx b) + 1 = 2 * slabSize n_max
    · have hst : s' = (Memory.spec 0).clientState s₁
          (promoteSlabProg U V w n_max h_space (base, b)) := by
        change (Memory.spec 0).clientState s (pushBackSlotProg U V w n_max h_space d) = _
        unfold pushBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1, ite_eq_left hprom]
      have hcost : memoryCost (pushBackSlotProg U V w n_max h_space d) s =
          30 + memoryCost (promoteSlabProg U V w n_max h_space (base, b)) s₁ := by
        unfold pushBackSlotProg
        simp only [hb0, ↓reduceIte, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, memoryCost_pushBackTailWriteProg, hres1, ite_eq_left hprom]
      have hpre_prom : PromoteSlabInv U V w n_max h_space base b s₁ := by
        refine ⟨hb, htail1, hslab1, ?_, fun b' hb' hne => ?_, ?_⟩
        · change gm₁ (gmRIdx b) = 2 * slabSize n_max
          rw [hrb1, hprom]
        · change gm₁ (gmRIdx b') < tailCapPerBucket n_max ∧
            (0 < gm₁ (gmQIdx b') → 1 ≤ gm₁ (gmRIdx b'))
          rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
          exact hinv.multi_r_bounds hb_pos b' hb'
        · change gm₁ 0 * slabSize n_max + gm₁ 1 ≤ n_max
          omega
      obtain ⟨hf2, hout2, hl2, hinv2, hqb2, hrb2, hother2, hbc2, hslot2, hcost2⟩ :=
        promoteSlabProg_effect hw hb_pos s₁ hpre_prom
      have htot2 := promoteSlabProg_tot_eq hw hb_pos s₁ hpre_prom
      rw [← hst] at hf2 hout2 hl2 hinv2 hqb2 hrb2 hother2 hbc2 hslot2 htot2
      change SlotStoreInv n_max gm' at hinv2
      change gm' (gmQIdx b) = gm₁ (gmQIdx b) + 1 at hqb2
      change gm' (gmRIdx b) = slabSize n_max at hrb2
      change ∀ b' < numBuckets n_max, b' ≠ b →
        gm' (gmQIdx b') = gm₁ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₁ (gmRIdx b') at hother2
      change ∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₁ b' at hbc2
      change ∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
        quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
          quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) ∧
        valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
          valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) at hslot2
      change gm' 0 * slabSize n_max + gm' 1 = gm₁ 0 * slabSize n_max + gm₁ 1 at htot2
      have hupd : gm' (gmQIdx b) =
            (pushBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          gm' (gmRIdx b) =
            (pushBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold pushBackCounts
        rw [ite_eq_left hprom]
        exact ⟨by rw [hqb2, hqb1], hrb2⟩
      have hother_all : ∀ b' < numBuckets n_max, b' ≠ b →
          gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        exact ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
          (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
      have hpot := slotPotential_pushBack_le hb_pos hb hupd hother_all
      have hwork : pushBackWork (slabSize n_max) (gm₀ (gmRIdx b)) = slabSize n_max := by
        unfold pushBackWork; rw [ite_eq_left hprom]
      rw [hwork] at hpot
      have hbc_new_lt : bCount n_max gm₀ b < bCount n_max gm' b := by
        rw [hbc2 b hb, hbc_b1]; omega
      refine ⟨hf2.trans hf1, fun a ha => (hout2 a ha).trans (hout1 a ha), hl2.trans hl1,
        hinv2,
        by unfold totalSlots; rw [ite_eq_right hb0, ite_eq_right hb0, htot2, htot1],
        (hbc2 b hb).trans hbc_b1,
        fun b' hb' hne => (hbc2 b' hb').trans (hbc_other1 b' hb' hne),
        by rw [(hslot2 b hb (bCount n_max gm₀ b) hbc_new_lt).1, hq_new1],
        by rw [(hslot2 b hb (bCount n_max gm₀ b) hbc_new_lt).2, hv_new1],
        fun b' hb' j hj => ?_, ?_⟩
      · have hj' : j < bCount n_max gm' b' := by
          rw [hbc2 b' hb']
          by_cases hbeq : b' = b
          · subst b'; rw [hbc_b1]; omega
          · rw [hbc_other1 b' hb' hbeq]; exact hj
        exact ⟨((hslot2 b' hb' j hj').1).trans (hold1 b' hb' j hj).1,
          ((hslot2 b' hb' j hj').2).trans (hold1 b' hb' j hj).2⟩
      · rw [hcost]
        omega
    · have hst : s' = s₁ := by
        change (Memory.spec 0).clientState s (pushBackSlotProg U V w n_max h_space d) = s₁
        unfold pushBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hres1, ite_eq_right hprom]
        rfl
      have hgm'_eq : gm' = gm₁ := by dsimp only [gm', gm₁]; rw [hst]
      have hcost : memoryCost (pushBackSlotProg U V w n_max h_space d) s = 30 := by
        unfold pushBackSlotProg
        simp only [hb0, ↓reduceIte, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, memoryCost_pushBackTailWriteProg, hres1, ite_eq_right hprom,
          memoryCost_pure, Nat.add_zero]
      have hinv1 : SlotStoreInv n_max gm₁ := by
        refine ⟨fun h0 => by omega, fun _ => htail1, fun _ => hslab1, fun _ b' hb' => ?_,
          fun _ => by omega⟩
        by_cases hbeq : b' = b
        · subst b'
          rw [hqb1, hrb1]
          unfold tailCapPerBucket
          rw [ite_eq_right hb0]
          omega
        · rw [(hother1 b' hb' hbeq).1, (hother1 b' hb' hbeq).2]
          exact hinv.multi_r_bounds hb_pos b' hb'
      have hupd : gm' (gmQIdx b) =
            (pushBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          gm' (gmRIdx b) =
            (pushBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold pushBackCounts
        rw [ite_eq_right hprom, hgm'_eq]
        exact ⟨hqb1, hrb1⟩
      have hother_all : ∀ b' < numBuckets n_max, b' ≠ b →
          gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne; rw [hgm'_eq]; exact hother1 b' hb' hne
      have hpot := slotPotential_pushBack_le hb_pos hb hupd hother_all
      have hwork : pushBackWork (slabSize n_max) (gm₀ (gmRIdx b)) = 0 := by
        unfold pushBackWork; rw [ite_eq_right hprom]
      rw [hwork, Nat.add_zero] at hpot
      refine ⟨by rw [hst, hf1],
        fun a ha => by rw [hst, hout1 a ha],
        by rw [hst, hl1],
        by rw [hgm'_eq]; exact hinv1,
        by unfold totalSlots; rw [ite_eq_right hb0, ite_eq_right hb0, hgm'_eq, htot1],
        by rw [hgm'_eq, hbc_b1],
        fun b' hb' hne => by rw [hgm'_eq, hbc_other1 b' hb' hne],
        by rw [hst, hgm'_eq, hq_new1],
        by rw [hst, hgm'_eq, hv_new1],
        fun b' hb' j hj => by rw [hst, hgm'_eq]; exact hold1 b' hb' j hj,
        ?_⟩
      rw [hcost]
      omega

theorem realizes_pushBackSlotGen :
    Realizes .exact pushBackSlotGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      PushBackSlotGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwq := realizes_writeQuotGen
  have hwv := realizes_writeValGen
  have hwg := realizes_writeGMGen
  have htw := realizes_pushBackTailWriteGen
  have hprom := realizes_promoteSlabGen
  refine Realizes.congr (p := fun d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ => do
      let i0 ← pure 0
      if dpBucketBits d.1.1.1 = i0 then
        let c ← readGMGenProg (d.1.1.1, (d.1.1.2.1, i0))
        writeQuotGenProg (d.1.1.1, ((d.1.1.2.1, c), d.1.2))
        writeValGenProg (d.1.1.1, ((d.1.1.2.1, c), d.2))
        let c1 ← pure (c + 1)
        writeGMGenProg (d.1.1.1, ((d.1.1.2.1, i0), c1))
      else
        let r_b_new ← pushBackTailWriteGenProg d
        if r_b_new = dpTwoSlabSize d.1.1.1 then
          promoteSlabGenProg d.1.1
        else
          pure ()) ?_
    (fun d => by
      simp only [pushBackSlotGenProg, ← PFunctor.FreeM.bind_eq_bind, pure_bind])
  realize
  all_goals (
    rcases d with ⟨⟨⟨dp, base, b⟩, q_val⟩, v_val⟩
    let d : ((ℕ × ℕ) × ℕ) × ℕ := (((base, b), q_val), v_val)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [pushBackSlotGenPre_mk, pushBackTailWriteGenPre_mk,
      pushBackTailWriteGenProg_mk, promoteSlabGenPre_mk, promoteSlabGenProg_mk]
    try dsimp only [d, PushBackSlotPre] at *
  )
  · exact h.1
  · unfold globalMetaLen; omega
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg _ h0_lt]
    have htot := h.2.2.2.1
    unfold totalSlots at htot
    rw [ite_eq_left hc] at htot
    exact htot
  · have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg _ h0_lt]
    have htot := h.2.2.2.1
    unfold totalSlots at htot
    rw [ite_eq_left hc] at htot
    refine fits_of_le_max_n_one h.1 hw hnU hU ?_
    omega
  · exact ⟨h, Nat.pos_of_ne_zero hc⟩
  · rename_i hc0
    have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc0
    rcases h with ⟨hdict, hinv, hb, htot, hq_lt, hv_lt⟩
    obtain ⟨hres1, _, _, _, _, htail1, hslab1, htot1, _, hrb1, hother1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos s hinv hb htot hq_lt hv_lt
    rw [hres1] at hc
    have htot0_lt : gmAt base U V w₀ n_max h_space s.mem 0 * slabSize n_max +
        gmAt base U V w₀ n_max h_space s.mem 1 < n_max := by
      unfold totalSlots at htot; rw [ite_eq_right hc0] at htot; exact htot
    refine ⟨hdict, ⟨hb, htail1, hslab1, by rw [hrb1, hc], fun b' hb' hne => ?_, by omega⟩,
      hb_pos⟩
    rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
    exact hinv.multi_r_bounds hb_pos b' hb'

/-! ## Section 3: `popBackSlotProg` via `realize` -/

/-- Parameter-free `Memory.Prog` operation removing the last logical slot `bCount n_max gm b - 1`
of a non-empty bucket `b = d.2.2` at `base = d.2.1`. -/
def popBackSlotGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit :=
  if dpBucketBits d.1 = 0 then do
    let c ← readGMGenProg (d.1, (d.2.1, 0))
    writeGMGenProg (d.1, ((d.2.1, 0), c - 1))
  else do
    removeLastTailItemGenProg d
    let r_b_new ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
    let q_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2))
    if r_b_new = 0 then
      if 0 < q_b then
        demoteSlabGenProg d
      else
        pure ()
    else
      pure ()

/-- `Memory.Prog` operation removing the last logical slot `bCount n_max gm b - 1` of a non-empty
bucket `b = d.2` at `base = d.1`, demoting the top full slab into `K = slabSize n_max` tail items
when `r_b - 1 = 0 ∧ 0 < q_b`. -/
def popBackSlotProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit :=
  if bucketBits n_max = 0 then do
    let c ← readGMProg U V w n_max h_space (d.1, 0)
    writeGMProg U V w n_max h_space ((d.1, 0), c - 1)
  else do
    removeLastTailItemProg U V w n_max h_space d
    let r_b_new ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2 + 1)
    let q_b ← readGMProg U V w n_max h_space (d.1, 4 + 3 * d.2)
    if r_b_new = 0 then
      if 0 < q_b then
        demoteSlabProg U V w n_max h_space d
      else
        pure ()
    else
      pure ()

@[simp] theorem popBackSlotGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    popBackSlotGenProg (mkDictParams U V w n_max h_space, d) =
      popBackSlotProg U V w n_max h_space d := by
  simp only [popBackSlotGenProg, popBackSlotProg, p_bucketBits_mk,
    readGMGenProg_mk, writeGMGenProg_mk, removeLastTailItemGenProg_mk, demoteSlabGenProg_mk]

/-- Precondition for `popBackSlotProg` in `Realizes`. -/
@[expose]
def PopBackSlotPre (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) : Prop :=
  let base := d.1
  let b := d.2
  let gm := gmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max gm ∧
  b < numBuckets n_max ∧
  1 ≤ bCount n_max gm b

/-- Parameter-free precondition for `popBackSlotGenProg`. -/
@[expose]
def PopBackSlotGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 d.2.1 ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm d.2.2

@[simp] theorem popBackSlotGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    PopBackSlotGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      PopBackSlotPre U V w₀ n_max h_space w d s := Iff.rfl

/-- Pure state effect and amortized `memoryCost` bound of `popBackSlotProg`. -/
theorem popBackSlotProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w n_max h_space s.mem) b) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let d := (base, b)
    let s' := (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space d)
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    totalSlots n_max gm' + 1 = totalSlots n_max gm₀ ∧
    bCount n_max gm' b = bCount n_max gm₀ b - 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (popBackSlotProg U V w n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 174 := by
  intro gm₀ d s' gm'
  change SlotStoreInv n_max gm₀ at hinv
  change 1 ≤ bCount n_max gm₀ b at hbc
  by_cases hb0 : bucketBits n_max = 0
  · have hb_eq : b = 0 := by
      have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
      omega
    subst hb_eq
    unfold bCount at hbc
    simp only [hb0, ↓reduceIte] at hbc
    change 1 ≤ gm₀ 0 at hbc
    have hc_le : gm₀ 0 ≤ n_max := hinv.single_valid hb0
    have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    have hc1_lt : gm₀ 0 - 1 < 2 ^ globalPtrBits n_max :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
      writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw h0_lt hc1_lt s
    let s₁ := (Memory.spec 0).clientState s
      (writeGMProg U V w n_max h_space ((base, 0), gm₀ 0 - 1))
    have hst : s' = s₁ := by
      change (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space d) = s₁
      unfold popBackSlotProg
      simp only [hb0, ↓reduceIte, d]
      rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
        clientResult_readGMProg s h0_lt]
    have hgm'_eq : gm' = Function.update gm₀ 0 (gm₀ 0 - 1) := by
      dsimp only [gm']; rw [hst, hg1]
    have hinv' : SlotStoreInv n_max gm' := by
      refine ⟨fun _ => by rw [hgm'_eq, Function.update_self]; omega,
        fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩
    have hbc0 : bCount n_max gm₀ 0 = gm₀ 0 := by unfold bCount; simp [hb0]
    have hbc' : bCount n_max gm' 0 = gm₀ 0 - 1 := by
      unfold bCount; simp [hb0, hgm'_eq]
    have hslot_eq : ∀ b' j, slotOf n_max gm' b' j = j ∧ slotOf n_max gm₀ b' j = j := by
      intro b' j; unfold slotOf; simp [hb0]
    refine ⟨by rw [hst, hf1],
      fun a ha => by
        rw [hst, hout1 a
          (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha ⊢; omega)],
      by rw [hst, hl1],
      hinv',
      by unfold totalSlots; simp only [hb0, ↓reduceIte, hgm'_eq, Function.update_self]; omega,
      by rw [hbc', hbc0],
      fun b' hb' hne => by
        have : numBuckets n_max = 1 := by simp [numBuckets, hb0]
        omega,
      fun b' _ j _ => by
        rw [hst, hq1, hv1, (hslot_eq b' j).1, (hslot_eq b' j).2]
        exact ⟨rfl, rfl⟩,
      ?_⟩
    have hcost : memoryCost (popBackSlotProg U V w n_max h_space d) s = 6 := by
      unfold popBackSlotProg
      simp [hb0, d, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    have hpot' : slotPotential n_max gm' = 0 := by unfold slotPotential; simp [hb0]
    have hpot0 : slotPotential n_max gm₀ = 0 := by unfold slotPotential; simp [hb0]
    rw [hcost, hpot', hpot0]
    omega
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
    have hr0_pos : 1 ≤ gm₀ (gmRIdx b) := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have hr0_lt : gm₀ (gmRIdx b) < 2 * slabSize n_max := by
      have := (hinv.multi_r_bounds hb_pos b hb).1
      unfold tailCapPerBucket at this
      rw [ite_eq_right hb0] at this
      exact this
    have htail₀ := hinv.multi_tail hb_pos
    have hslab₀ := hinv.multi_slab hb_pos
    have htot₀ := hinv.multi_total_le hb_pos
    obtain ⟨hf1, hout1, hq1, hv1, hl1, hgm1_eq⟩ :=
      removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos hb s htail₀ hr0_pos
    let s₁ := (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space d)
    let gm₁ := gmAt base U V w n_max h_space s₁.mem
    change gm₁ = gmRemoveTail n_max gm₀ b at hgm1_eq
    have hpres1 := gmRemoveTail_preserves_nonTail hb hr0_pos htail₀
    have htail1 : TailBijection n_max gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) := by
      rw [hgm1_eq]; exact tailBijection_gmRemoveTail hb hr0_pos htail₀
    have hslab1 : SlabBijection n_max gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) := by
      rw [hgm1_eq]; exact (slabBijection_gmRemoveTail hb hr0_pos htail₀ hslab₀).2
    have hgm1_pos : 1 ≤ gm₀ 1 := by
      have := r_le_ntails_of_tailBijection htail₀ hb
      omega
    have htot1 : gm₁ 0 * slabSize n_max + gm₁ 1 + 1 = gm₀ 0 * slabSize n_max + gm₀ 1 := by
      rw [hgm1_eq, hpres1.1, hpres1.2.1]; omega
    have hqb1 : gm₁ (gmQIdx b) = gm₀ (gmQIdx b) := by
      rw [hgm1_eq, hpres1.2.2.2.2.1 b hb]
    have hrb1 : gm₁ (gmRIdx b) = gm₀ (gmRIdx b) - 1 := by
      rw [hgm1_eq, hpres1.2.2.1]
    have hother1 : ∀ b' < numBuckets n_max, b' ≠ b →
        gm₁ (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm₁ (gmRIdx b') = gm₀ (gmRIdx b') := by
      intro b' hb' hne
      exact ⟨by rw [hgm1_eq, hpres1.2.2.2.2.1 b' hb'],
        by rw [hgm1_eq, hpres1.2.2.2.1 b' hb' hne]⟩
    have hbc_b1 : bCount n_max gm₁ b = bCount n_max gm₀ b - 1 := by
      unfold bCount
      simp only [hb0, ↓reduceIte, hb, hqb1, hrb1]
      omega
    have hbc_other1 : ∀ b' < numBuckets n_max, b' ≠ b →
        bCount n_max gm₁ b' = bCount n_max gm₀ b' := by
      intro b' hb' hne
      unfold bCount
      simp only [hb0, ↓reduceIte, hb', (hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
    have hq_slot1 := (update_slotOf_gmRemoveTail (quotAt base U w n_max h_space s.mem)
      hb_pos hb hr0_pos htail₀ hslab₀ htot₀).1
    have hv_slot1 := (update_slotOf_gmRemoveTail (valAt base U V w n_max h_space s.mem)
      hb_pos hb hr0_pos htail₀ hslab₀ htot₀).1
    have hold1 : ∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₁ b',
        quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
          quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
        valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
          valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j) := by
      intro b' hb' j hj
      rw [hq1, hv1, hgm1_eq]
      rw [hgm1_eq] at hj
      exact ⟨hq_slot1 b' hb' j hj, hv_slot1 b' hb' j hj⟩
    have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hq_idx_lt : 4 + 3 * b < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    have hres_r : (Memory.spec 0).clientResult s₁
        (readGMProg U V w n_max h_space (base, 4 + 3 * b + 1)) = gm₁ (gmRIdx b) :=
      clientResult_readGMProg s₁ hr_idx_lt
    have hres_q : (Memory.spec 0).clientResult s₁
        (readGMProg U V w n_max h_space (base, 4 + 3 * b)) = gm₁ (gmQIdx b) :=
      clientResult_readGMProg s₁ hq_idx_lt
    by_cases hdem : gm₀ (gmRIdx b) = 1 ∧ 0 < gm₀ (gmQIdx b)
    · have hr1_eq0 : gm₁ (gmRIdx b) = 0 := by rw [hrb1, hdem.1]
      have hq1_pos : 0 < gm₁ (gmQIdx b) := by rw [hqb1]; exact hdem.2
      have hst : s' = (Memory.spec 0).clientState s₁
          (demoteSlabProg U V w n_max h_space (base, b)) := by
        change (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space d) = _
        unfold popBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_r,
          StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_q,
          ite_eq_left hr1_eq0, ite_eq_left hq1_pos]
      have hcost : memoryCost (popBackSlotProg U V w n_max h_space d) s =
          40 + memoryCost (demoteSlabProg U V w n_max h_space (base, b)) s₁ := by
        unfold popBackSlotProg
        simp only [hb0, ↓reduceIte, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, memoryCost_removeLastTailItemProg,
          memoryCost_bind, memoryCost_readGMProg, clientState_readGMProg, hres_r,
          memoryCost_bind, memoryCost_readGMProg, clientState_readGMProg, hres_q,
          ite_eq_left hr1_eq0, ite_eq_left hq1_pos]
        dsimp only [d]
        change 36 + (2 + (2 + memoryCost (demoteSlabProg U V w n_max h_space (base, b)) s₁)) =
          40 + memoryCost (demoteSlabProg U V w n_max h_space (base, b)) s₁
        omega
      have hpre_dem : DemoteSlabInv U V w n_max h_space base b s₁ := by
        refine ⟨hb, htail1, hslab1, hr1_eq0, hq1_pos, fun b' hb' hne => ?_, ?_⟩
        · change gm₁ (gmRIdx b') < tailCapPerBucket n_max ∧
            (0 < gm₁ (gmQIdx b') → 1 ≤ gm₁ (gmRIdx b'))
          rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
          exact hinv.multi_r_bounds hb_pos b' hb'
        · change gm₁ 0 * slabSize n_max + gm₁ 1 ≤ n_max
          omega
      obtain ⟨hf2, hout2, hl2, hinv2, hqb2, hrb2, hother2, hbc2, hslot2, hcost2⟩ :=
        demoteSlabProg_effect hw hb_pos s₁ hpre_dem
      have htot2 := demoteSlabProg_tot_eq hw hb_pos s₁ hpre_dem
      rw [← hst] at hf2 hout2 hl2 hinv2 hqb2 hrb2 hother2 hbc2 hslot2 htot2
      change SlotStoreInv n_max gm' at hinv2
      change gm' (gmQIdx b) = gm₁ (gmQIdx b) - 1 at hqb2
      change gm' (gmRIdx b) = slabSize n_max at hrb2
      change ∀ b' < numBuckets n_max, b' ≠ b →
        gm' (gmQIdx b') = gm₁ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₁ (gmRIdx b') at hother2
      change ∀ b' < numBuckets n_max, bCount n_max gm' b' = bCount n_max gm₁ b' at hbc2
      change ∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
        quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
          quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) ∧
        valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
          valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) at hslot2
      change gm' 0 * slabSize n_max + gm' 1 = gm₁ 0 * slabSize n_max + gm₁ 1 at htot2
      have hupd : gm' (gmQIdx b) =
            (popBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          gm' (gmRIdx b) =
            (popBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold popBackCounts
        rw [ite_eq_left hdem]
        exact ⟨by rw [hqb2, hqb1], hrb2⟩
      have hother_all : ∀ b' < numBuckets n_max, b' ≠ b →
          gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne
        exact ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
          (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
      have hpot := slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt hupd hother_all
      have hwork : popBackWork (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b)) =
          slabSize n_max := by
        unfold popBackWork; rw [ite_eq_left hdem]
      rw [hwork] at hpot
      refine ⟨hf2.trans hf1, fun a ha => (hout2 a ha).trans (hout1 a ha), hl2.trans hl1,
        hinv2,
        by unfold totalSlots; rw [ite_eq_right hb0, ite_eq_right hb0, htot2, htot1],
        (hbc2 b hb).trans hbc_b1,
        fun b' hb' hne => (hbc2 b' hb').trans (hbc_other1 b' hb' hne),
        fun b' hb' j hj => ?_, ?_⟩
      · have hj1 : j < bCount n_max gm₁ b' := by rw [← hbc2 b' hb']; exact hj
        exact ⟨((hslot2 b' hb' j hj).1).trans (hold1 b' hb' j hj1).1,
          ((hslot2 b' hb' j hj).2).trans (hold1 b' hb' j hj1).2⟩
      · rw [hcost]
        omega
    · have hst : s' = s₁ := by
        change (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space d) = s₁
        unfold popBackSlotProg
        simp only [hb0, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_r,
          StateTransitionSpec.clientState_bind, clientState_readGMProg, hres_q]
        by_cases hr1_eq0 : gm₁ (gmRIdx b) = 0
        · have hnot_q : ¬(0 < gm₁ (gmQIdx b)) := by
            intro hq_pos
            apply hdem
            rw [hrb1] at hr1_eq0
            rw [hqb1] at hq_pos
            exact ⟨by omega, hq_pos⟩
          rw [ite_eq_left hr1_eq0, ite_eq_right hnot_q]
          rfl
        · rw [ite_eq_right hr1_eq0]
          rfl
      have hcost : memoryCost (popBackSlotProg U V w n_max h_space d) s = 40 := by
        unfold popBackSlotProg
        simp only [hb0, ↓reduceIte, ← PFunctor.FreeM.bind_eq_bind]
        rw [memoryCost_bind, memoryCost_removeLastTailItemProg,
          memoryCost_bind, memoryCost_readGMProg, clientState_readGMProg, hres_r,
          memoryCost_bind, memoryCost_readGMProg, clientState_readGMProg, hres_q]
        by_cases hr1_eq0 : gm₁ (gmRIdx b) = 0
        · have hnot_q : ¬(0 < gm₁ (gmQIdx b)) := by
            intro hq_pos
            apply hdem
            rw [hrb1] at hr1_eq0
            rw [hqb1] at hq_pos
            exact ⟨by omega, hq_pos⟩
          rw [ite_eq_left hr1_eq0, ite_eq_right hnot_q]
          rfl
        · rw [ite_eq_right hr1_eq0]
          rfl
      have hgm'_eq : gm' = gm₁ := by dsimp only [gm', gm₁]; rw [hst]
      have hinv1 : SlotStoreInv n_max gm₁ := by
        refine ⟨fun h0 => by omega, fun _ => htail1, fun _ => hslab1, fun _ b' hb' => ?_,
          fun _ => by omega⟩
        by_cases hbeq : b' = b
        · subst b'
          rw [hqb1, hrb1]
          unfold tailCapPerBucket
          rw [ite_eq_right hb0]
          refine ⟨by omega, fun hq => ?_⟩
          by_contra hlt
          exact hdem ⟨by omega, hq⟩
        · rw [(hother1 b' hb' hbeq).1, (hother1 b' hb' hbeq).2]
          exact hinv.multi_r_bounds hb_pos b' hb'
      have hupd : gm' (gmQIdx b) =
            (popBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).1 ∧
          gm' (gmRIdx b) =
            (popBackCounts (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b))).2 := by
        unfold popBackCounts
        rw [ite_eq_right hdem, hgm'_eq]
        exact ⟨hqb1, hrb1⟩
      have hother_all : ∀ b' < numBuckets n_max, b' ≠ b →
          gm' (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm' (gmRIdx b') = gm₀ (gmRIdx b') := by
        intro b' hb' hne; rw [hgm'_eq]; exact hother1 b' hb' hne
      have hpot := slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt hupd hother_all
      have hwork : popBackWork (slabSize n_max) (gm₀ (gmQIdx b)) (gm₀ (gmRIdx b)) = 0 := by
        unfold popBackWork; rw [ite_eq_right hdem]
      rw [hwork, Nat.add_zero] at hpot
      refine ⟨by rw [hst, hf1],
        fun a ha => by rw [hst, hout1 a ha],
        by rw [hst, hl1],
        by rw [hgm'_eq]; exact hinv1,
        by unfold totalSlots; rw [ite_eq_right hb0, ite_eq_right hb0, hgm'_eq, htot1],
        by rw [hgm'_eq, hbc_b1],
        fun b' hb' hne => by rw [hgm'_eq, hbc_other1 b' hb' hne],
        fun b' hb' j hj => by rw [hst, hgm'_eq]; rw [hgm'_eq] at hj; exact hold1 b' hb' j hj,
        ?_⟩
      rw [hcost]
      omega

theorem realizes_popBackSlotGen :
    Realizes .exact popBackSlotGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      PopBackSlotGenPre
      (fun _ _ => 0) := by
  have hrg := realizes_readGMGen
  have hwg := realizes_writeGMGen
  have hrem := realizes_removeLastTailItemGen
  have hdem := realizes_demoteSlabGen
  refine Realizes.congr (p := fun d : DictParams × (ℕ × ℕ) => do
      let z ← pure 0
      if dpBucketBits d.1 = z then
        let c ← readGMGenProg (d.1, (d.2.1, z))
        let c_sub ← pure (c - 1)
        writeGMGenProg (d.1, ((d.2.1, z), c_sub))
      else
        removeLastTailItemGenProg d
        let r_idx ← pure (4 + 3 * d.2.2 + 1)
        let r_b_new ← readGMGenProg (d.1, (d.2.1, r_idx))
        let q_idx ← pure (4 + 3 * d.2.2)
        let q_b ← readGMGenProg (d.1, (d.2.1, q_idx))
        if r_b_new = z then
          if z < q_b then
            demoteSlabGenProg d
          else
            pure ()
        else
          pure ()) ?_
    (fun d => by
      simp only [popBackSlotGenProg, ← PFunctor.FreeM.bind_eq_bind, pure_bind])
  realizeDictWith [popBackSlotGenPre_mk, removeLastTailItemGenPre_mk, removeLastTailItemGenProg_mk,
    demoteSlabGenPre_mk, demoteSlabGenProg_mk]
  · exact h.1
  · unfold globalMetaLen; omega
  · have hd2 : d.2 = 0 := by
      have := h.2.2.1
      have : numBuckets n_max = 1 := by simp [numBuckets, hc]
      omega
    have h0_lt : 0 < globalMetaLen n_max := by unfold globalMetaLen; omega
    rw [clientResult_readGMProg _ h0_lt]
    have hbc := h.2.2.2
    unfold bCount at hbc
    simp only [hc, ↓reduceIte, hd2] at hbc
    exact hbc
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact ⟨h.1, h.2.1.multi_tail hb_pos, h.2.2.1,
      pos_gmRIdx_of_pos_bCount hb_pos h.2.1 h.2.2.1 h.2.2.2, hb_pos⟩
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmRIdx_lt hb_pos h.2.2.1))
  · refine fits_const_of_dictEnv h.1 ?_; omega
  · exact h.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact gmRIdx_lt hb_pos h.2.2.1
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact fits_of_le_globalMetaLen h.1 hb_pos hw hnU hU (le_of_lt (gmQIdx_lt hb_pos h.2.2.1))
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc
    exact gmQIdx_lt hb_pos h.2.2.1
  · rename_i hc0 hc1
    have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hc0
    rcases d with ⟨base, b⟩
    rcases h with ⟨hdict, hinv, hb, hbc⟩
    dsimp only at hdict hinv hb hbc hc1 hc ⊢
    have hr0_pos : 1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) :=
      pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have htail₀ := hinv.multi_tail hb_pos
    have hslab₀ := hinv.multi_slab hb_pos
    have htot₀ := hinv.multi_total_le hb_pos
    obtain ⟨_, _, _, _, _, hgm1_eq⟩ :=
      removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos hb s htail₀ hr0_pos
    let s₁ := (Memory.spec 0).clientState s
      (removeLastTailItemProg U V w₀ n_max h_space (base, b))
    have hr_idx_lt : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
    have hq_idx_lt : 4 + 3 * b < globalMetaLen n_max := gmQIdx_lt hb_pos hb
    rw [clientState_readGMProg] at hc
    rw [clientState_readGMProg, clientState_readGMProg]
    rw [clientResult_readGMProg s₁ hr_idx_lt] at hc1
    rw [clientResult_readGMProg s₁ hq_idx_lt] at hc
    have hpres1 := gmRemoveTail_preserves_nonTail hb hr0_pos htail₀
    have htail1 := tailBijection_gmRemoveTail hb hr0_pos htail₀
    have ⟨_, hslab1⟩ := slabBijection_gmRemoveTail hb hr0_pos htail₀ hslab₀
    refine ⟨hdict, ⟨hb, ?_, ?_, hc1, hc, fun b' hb' hne => ?_, ?_⟩, hb_pos⟩
    · rw [hgm1_eq]; exact htail1
    · rw [hgm1_eq]; exact hslab1
    · rw [hgm1_eq, hpres1.2.2.2.2.1 b' hb', hpres1.2.2.2.1 b' hb' hne]
      exact hinv.multi_r_bounds hb_pos b' hb'
    · rw [hgm1_eq, hpres1.1, hpres1.2.1]
      omega

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
