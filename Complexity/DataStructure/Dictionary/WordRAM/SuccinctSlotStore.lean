/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctAccessors

/-!
# Physical Slot Resolution and Slab/Tail Slot Store Operations

This module implements Word-RAM subroutines for bucket cardinality lookup (`readBucketCountCode`),
logical-to-physical slot resolution (`resolveIndexedSlotCode`), and physical slot allocation and
deallocation preserving `SlotStoreInv`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

theorem r_le_ntails_of_tailBijection {n_max : ℕ} {gm r_fn : ℕ → ℕ} {n_tails : ℕ}
    (htail : TailBijection n_max gm r_fn n_tails) {b : ℕ} (hb : b < numBuckets n_max) :
    r_fn b ≤ n_tails := by
  have hcard : (Finset.range (r_fn b)).card ≤ (Finset.range n_tails).card := by
    refine Finset.card_le_card_of_injOn (fun r => gm (gmTailPtrIdx n_max b r)) ?_ ?_
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_range] at hr ⊢
      exact htail.ptr_lt b hb r hr
    · intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_coe, Finset.mem_range] at hr₁ hr₂
      have hown := congrArg (gm ∘ gmTailOwnerIdx n_max) heq
      dsimp only [Function.comp_apply] at hown
      rw [htail.owner_ptr b hb r₁ hr₁, htail.owner_ptr b hb r₂ hr₂] at hown
      omega
  simpa using hcard

theorem q_le_nslabs_of_slabBijection {n_max : ℕ} {gm q_fn : ℕ → ℕ} {n_slabs : ℕ}
    (hslab : SlabBijection n_max gm q_fn n_slabs) {b : ℕ} (hb : b < numBuckets n_max) :
    q_fn b ≤ n_slabs := by
  have hcard : (Finset.range (q_fn b)).card ≤ (Finset.range n_slabs).card := by
    refine Finset.card_le_card_of_injOn (fun s => slabPtrOf n_max gm b s) ?_ ?_
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_range] at hs ⊢
      exact hslab.ptr_lt b hb s hs
    · intro s₁ hs₁ s₂ hs₂ heq
      simp only [Finset.mem_coe, Finset.mem_range] at hs₁ hs₂
      have hown := congrArg (gm ∘ gmSlabOwnerSIdx n_max) heq
      dsimp only [Function.comp_apply] at hown
      rw [hslab.ownerS_ptr b hb s₁ hs₁, hslab.ownerS_ptr b hb s₂ hs₂] at hown
      exact hown
  simpa using hcard

theorem bCount_le_n_max {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm) (b : ℕ) :
    bCount n_max gm b ≤ n_max := by
  unfold bCount
  split_ifs with hb0 hb_lt hb_lt
  · exact hinv.single_valid hb0
  · exact Nat.zero_le _
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have hq := q_le_nslabs_of_slabBijection (hinv.multi_slab hb_pos) hb_lt
    have hr := r_le_ntails_of_tailBijection (hinv.multi_tail hb_pos) hb_lt
    have htot := hinv.multi_total_le hb_pos
    have hqK : gm (gmQIdx b) * slabSize n_max ≤ gm 0 * slabSize n_max :=
      Nat.mul_le_mul_right _ hq
    omega
  · exact Nat.zero_le _

/-- Read `bCount n_max gm b` into working register `i_out` (`i_b` holds `b`).
When `bucketBits n_max = 0`, reads `gm 0`; when `0 < bucketBits n_max`, computes
`gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b)`. Uses `15, 16, 17, 18` as scratch
(`i_b, i_out < 15`). -/
def readBucketCountCode (r_hash U V w n_max h_space i_b i_out : ℕ)
    (hb : i_b < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  if bucketBits n_max = 0 then
    .seq (wConstCode r_hash 17 0)
      (readGMCode r_hash U V w n_max h_space 17 i_out (by omega) hout)
  else
    .seq (readGMLinCode r_hash U V w n_max h_space 4 3 i_b 15 hb)
      (.seq (wConstCode r_hash 16 (slabSize n_max))
        (.seq (wBinCode r_hash .mul 15 15 16)
          (.seq (readGMLinCode r_hash U V w n_max h_space 5 3 i_b i_out hb hout)
            (wBinCode r_hash .add i_out 15 i_out hout (by omega) hout))))

theorem readBucketCountCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_out : ℕ) (hb : i_b < 15) (hout : i_out < 15)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space x.mem))
    (hb_lt : wRegs x i_b < numBuckets n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readBucketCountCode r_hash U V w n_max h_space i_b i_out
        (by omega) (by omega)) x y 87 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y i_out = bCount n_max (gmAt base U V w n_max h_space x.mem) (wRegs x i_b) ∧
      (∀ k < 15, k ≠ i_out → wRegs y k = wRegs x k) := by
  unfold readBucketCountCode
  have hmax_fit : Fits w (max n_max 1) := max_n_one_lt_two_pow_w hw hnU hU
  split_ifs with hb0
  · obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
      wConstCode_execWithin 17 0 (by omega) x hctx (hmax_fit.of_le (by omega))
    have hx1_17 : wRegs x1 17 = 0 := by rw [hr1, Function.update_self]
    have h0_lt : wRegs x1 17 < globalMetaLen n_max := by
      rw [hx1_17]; unfold globalMetaLen; omega
    obtain ⟨y, hexy, hctxy, hmy, hry⟩ :=
      readGMCode_wRegs hw hnU hU hspace 17 i_out (by omega) (by omega) x1 hctx1 h0_lt
    refine ⟨y, (hex1.seq hexy).mono (by omega), hctxy, by rw [hmy, hm1], ?_, ?_⟩
    · rw [hry, Function.update_self, hx1_17, hm1]
      have hnb1 : numBuckets n_max = 1 := by unfold numBuckets; rw [hb0]; rfl
      have hb_eq0 : wRegs x i_b = 0 := by omega
      unfold bCount
      simp [hb0, hb_eq0]
    · intro k hk hne
      rw [hry, Function.update_of_ne hne, hr1, Function.update_of_ne (by omega)]
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have h9_fit : Fits w 9 := nine_lt_two_pow_w hw (one_le_n_max_of_bucketBits_pos hb_pos) hspace
    have hgm_fit : Fits w (globalMetaLen n_max) :=
      hmax_fit.of_le ((globalMetaLen_le_of_bucketBits_pos hb_pos).trans (le_max_left n_max 1))
    have hq_idx : 4 + 3 * wRegs x i_b < globalMetaLen n_max := gmQIdx_lt hb_pos hb_lt
    obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
      readGMLinCode_wRegs hw hnU hU hspace i_b 15 (by omega) (by omega) (by omega) (by omega)
        (h9_fit.of_le (by omega)) (h9_fit.of_le (by omega)) x hctx hq_idx
        (hgm_fit.of_le (le_of_lt hq_idx))
    have hK_le : slabSize n_max ≤ max n_max 1 := by
      have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
      have hK := (slabSize_eq_sq_of_pos hb_pos).1
      have hB := numBuckets_pos n_max
      have hS := two_le_slabScale n_max
      have : slabSize n_max ≤ numBuckets n_max * (slabScale n_max) ^ 3 := by
        rw [hK]
        calc (slabScale n_max) ^ 2 = 1 * ((slabScale n_max) ^ 2 * 1) := by ring
          _ ≤ numBuckets n_max * ((slabScale n_max) ^ 2 * slabScale n_max) :=
            Nat.mul_le_mul hB (Nat.mul_le_mul_left _ (by omega))
          _ = numBuckets n_max * (slabScale n_max) ^ 3 := by ring
      omega
    obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
      wConstCode_execWithin 16 (slabSize n_max) (by omega) x1 hctx1 (hmax_fit.of_le hK_le)
    have hx2_15 : wRegs x2 15 =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) := by
      rw [hr2, Function.update_of_ne (by decide), hr1]
      simp [uRegs, gmQIdx]
    have hx2_16 : wRegs x2 16 = slabSize n_max := by rw [hr2, Function.update_self]
    have hbc_le : bCount n_max (gmAt base U V w n_max h_space x.mem) (wRegs x i_b) ≤ n_max :=
      bCount_le_n_max hinv (wRegs x i_b)
    have hbc_eq : bCount n_max (gmAt base U V w n_max h_space x.mem) (wRegs x i_b) =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max +
          gmAt base U V w n_max h_space x.mem (gmRIdx (wRegs x i_b)) := by
      unfold bCount
      simp [hb0, hb_lt]
    have hmul_fit : Fits w (wRegs x2 15 * wRegs x2 16) := by
      rw [hx2_15, hx2_16]
      exact hmax_fit.of_le (by omega)
    obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
      wMul_execWithin 15 15 16 (by omega) (by omega) (by omega) x2 hctx2 hmul_fit
    have hx3_15 : wRegs x3 15 =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max := by
      rw [hr3, Function.update_self, hx2_15, hx2_16]
    have hx3_b : wRegs x3 i_b = wRegs x i_b := by
      rw [hr3, Function.update_of_ne (by omega), hr2, Function.update_of_ne (by omega), hr1]
      have hb15 : i_b ≠ 15 := by omega
      have hb17 : i_b ≠ 17 := by omega
      simp [uRegs, hb15, hb17]
    have hr_idx : 5 + 3 * wRegs x3 i_b < globalMetaLen n_max := by
      rw [hx3_b]
      have h := gmRIdx_lt hb_pos hb_lt
      unfold gmRIdx at h
      omega
    obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
      readGMLinCode_wRegs hw hnU hU hspace i_b i_out (by omega) (by omega) (by omega) (by omega)
        (h9_fit.of_le (by omega)) (h9_fit.of_le (by omega)) x3 hctx3 hr_idx
        (hgm_fit.of_le (le_of_lt hr_idx))
    have hm30 : x3.mem = x.mem := by rw [hm3, hm2, hm1]
    have hx4_15 : wRegs x4 15 =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max := by
      rw [hr4]
      have h15_out : (15 : ℕ) ≠ i_out := by omega
      have h15_17 : (15 : ℕ) ≠ 17 := by decide
      rw [uRegs_cons, uRegs_cons, uRegs_nil,
        Function.update_of_ne h15_out, Function.update_of_ne h15_17, hx3_15]
    have hx4_out : wRegs x4 i_out =
        gmAt base U V w n_max h_space x.mem (gmRIdx (wRegs x i_b)) := by
      rw [hr4, hm30, hx3_b]
      have heq : 5 + 3 * wRegs x i_b = gmRIdx (wRegs x i_b) := by unfold gmRIdx; omega
      simp [uRegs, heq]
    have hadd_fit : Fits w (wRegs x4 15 + wRegs x4 i_out) := by
      rw [hx4_15, hx4_out]
      exact hmax_fit.of_le (by omega)
    obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
      wAdd_execWithin i_out 15 i_out (by omega) (by omega) (by omega) x4 hctx4 hadd_fit
    refine ⟨x5,
      (hex1.seq (hex2.seq (hex3.seq (hex4.seq hex5)))).mono (by omega),
      hctx5, by rw [hm5, hm4, hm30], ?_, ?_⟩
    · rw [hr5, Function.update_self, hx4_15, hx4_out, hbc_eq]
    · intro k hk hne
      rw [hr5, Function.update_of_ne hne, hr4]
      have hk17 : k ≠ 17 := by omega
      have hk15 : k ≠ 15 := by omega
      have hk16 : k ≠ 16 := by omega
      simp only [uRegs, Function.update_of_ne hne, Function.update_of_ne hk17]
      rw [hr3, Function.update_of_ne hk15, hr2, Function.update_of_ne hk16, hr1]
      simp [uRegs, hk15, hk17]

/-- Resolve logical slot `(b, j)` (`b = wRegs x i_b`, `j = wRegs x i_j`) to physical slot
`slotOf n_max gm b j` in `i_out` whenever
`j < effBucketCap n_max ∨ gm (gmQIdx b) * slabSize n_max ≤ j`.
Uses `13, 14, 15, 16, 17, 18` as scratch (`i_b, i_j, i_out < 13`). -/
def resolveIndexedSlotCode (r_hash U V w n_max h_space i_b i_j i_out : ℕ)
    (hb : i_b < 19 := by omega) (hj : i_j < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  if bucketBits n_max = 0 then
    wCopyCode r_hash i_out i_j hout hj
  else
    .seq (readGMLinCode r_hash U V w n_max h_space 4 3 i_b 13 hb)
      (.seq (wConstCode r_hash 14 (slabSize n_max))
        (.seq (wBinCode r_hash .mul 15 13 14)
          (.branch (.lt (wReg r_hash i_j hj) (wReg r_hash 15))
            (.seq (wBinCode r_hash .div 15 i_j 14 (by omega) hj (by omega))
              (.seq (wBinCode r_hash .mod 16 i_j 14 (by omega) hj (by omega))
                (.seq (wConstCode r_hash 14 (slabSize n_max - 1))
                  (.seq (wBinCode r_hash .sub 16 14 16)
                    (.seq (readGMAffineCode r_hash U V w n_max h_space
                        (gmSlabDirBase n_max) (dirSlabsPerBucket n_max) i_b 15 15 hb)
                      (.seq (wConstCode r_hash 14 (slabSize n_max))
                        (.seq (wBinCode r_hash .mul 15 15 14)
                          (wBinCode r_hash .add i_out 15 16 hout (by omega) (by omega)))))))))
            (.seq (wBinCode r_hash .sub 15 i_j 15 (by omega) hj (by omega))
              (.seq (readGMAffineCode r_hash U V w n_max h_space
                  (gmTailPtrBase n_max) (tailCapPerBucket n_max) i_b 15 15 hb)
                (.seq (wConstCode r_hash 16 (n_max - 1))
                  (wBinCode r_hash .sub i_out 16 15 hout (by omega) (by omega))))))))

theorem resolveIndexedSlotCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_j i_out : ℕ) (hb : i_b < 13) (hj : i_j < 13) (hout : i_out < 13)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space x.mem))
    (hb_lt : wRegs x i_b < numBuckets n_max)
    (hj_lt : wRegs x i_j < bCount n_max (gmAt base U V w n_max h_space x.mem) (wRegs x i_b))
    (hj_reach : wRegs x i_j < effBucketCap n_max ∨
      gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max ≤ wRegs x i_j) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (resolveIndexedSlotCode r_hash U V w n_max h_space i_b i_j i_out
        (by omega) (by omega) (by omega)) x y 95 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y i_out = slotOf n_max (gmAt base U V w n_max h_space x.mem)
        (wRegs x i_b) (wRegs x i_j) ∧
      (∀ k < 13, k ≠ i_out → wRegs y k = wRegs x k) := by
  unfold resolveIndexedSlotCode
  have hmax_fit : Fits w (max n_max 1) := max_n_one_lt_two_pow_w hw hnU hU
  split_ifs with hb0
  · obtain ⟨y, hexy, hctxy, hmy, hry⟩ :=
      wCopyCode_execWithin i_out i_j (by omega) (by omega) x hctx
    refine ⟨y, hexy.mono (by omega), hctxy, hmy, ?_, ?_⟩
    · rw [hry, Function.update_self]
      unfold slotOf
      simp [hb0]
    · intro k hk hne
      rw [hry, Function.update_of_ne hne]
  · have hb_pos : 0 < bucketBits n_max := Nat.pos_of_ne_zero hb0
    have h9_fit : Fits w 9 := nine_lt_two_pow_w hw (one_le_n_max_of_bucketBits_pos hb_pos) hspace
    have hgm_fit : Fits w (globalMetaLen n_max) :=
      hmax_fit.of_le ((globalMetaLen_le_of_bucketBits_pos hb_pos).trans (le_max_left n_max 1))
    have hK_pos : 0 < slabSize n_max := slabSize_pos n_max
    have hK_le : slabSize n_max ≤ max n_max 1 := by
      have hcube := numBuckets_mul_slabScale_cubed_le hb_pos
      have hK := (slabSize_eq_sq_of_pos hb_pos).1
      have hB := numBuckets_pos n_max
      have hS := two_le_slabScale n_max
      have : slabSize n_max ≤ numBuckets n_max * (slabScale n_max) ^ 3 := by
        rw [hK]
        calc (slabScale n_max) ^ 2 = 1 * ((slabScale n_max) ^ 2 * 1) := by ring
          _ ≤ numBuckets n_max * ((slabScale n_max) ^ 2 * slabScale n_max) :=
            Nat.mul_le_mul hB (Nat.mul_le_mul_left _ (by omega))
          _ = numBuckets n_max * (slabScale n_max) ^ 3 := by ring
      omega
    have hq_idx : 4 + 3 * wRegs x i_b < globalMetaLen n_max := gmQIdx_lt hb_pos hb_lt
    obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
      readGMLinCode_wRegs hw hnU hU hspace i_b 13 (by omega) (by omega) (by omega) (by omega)
        (h9_fit.of_le (by omega)) (h9_fit.of_le (by omega)) x hctx hq_idx
        (hgm_fit.of_le (le_of_lt hq_idx))
    obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
      wConstCode_execWithin 14 (slabSize n_max) (by omega) x1 hctx1 (hmax_fit.of_le hK_le)
    have hx2_13 : wRegs x2 13 =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) := by
      rw [hr2, Function.update_of_ne (by decide), hr1]
      simp [uRegs, gmQIdx]
    have hx2_14 : wRegs x2 14 = slabSize n_max := by rw [hr2, Function.update_self]
    have hbc_le : bCount n_max (gmAt base U V w n_max h_space x.mem) (wRegs x i_b) ≤ n_max :=
      bCount_le_n_max hinv (wRegs x i_b)
    have hbc_eq : bCount n_max (gmAt base U V w n_max h_space x.mem) (wRegs x i_b) =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max +
          gmAt base U V w n_max h_space x.mem (gmRIdx (wRegs x i_b)) := by
      unfold bCount
      simp [hb0, hb_lt]
    have hmul_fit : Fits w (wRegs x2 13 * wRegs x2 14) := by
      rw [hx2_13, hx2_14]
      exact hmax_fit.of_le (by omega)
    obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
      wMul_execWithin 15 13 14 (by omega) (by omega) (by omega) x2 hctx2 hmul_fit
    have hx3_15 : wRegs x3 15 =
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max := by
      rw [hr3, Function.update_self, hx2_13, hx2_14]
    have hx3_14 : wRegs x3 14 = slabSize n_max := by
      rw [hr3, Function.update_of_ne (by decide), hx2_14]
    have hx3_k : ∀ k < 13, wRegs x3 k = wRegs x k := by
      intro k hk
      rw [hr3, Function.update_of_ne (by omega), hr2, Function.update_of_ne (by omega), hr1]
      have hk13 : k ≠ 13 := by omega
      have hk17 : k ≠ 17 := by omega
      simp [uRegs, hk13, hk17]
    have hm30 : x3.mem = x.mem := by rw [hm3, hm2, hm1]
    by_cases hj_slab : wRegs x i_j <
        gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max
    · have hcond : (Cond.lt (wReg r_hash i_j (by omega)) (wReg r_hash 15)).Holds x3 := by
        simp only [Cond.Holds, ← wRegs_apply]
        rw [hx3_k i_j hj, hx3_15]
        exact hj_slab
      have hj_cap : wRegs x i_j < effBucketCap n_max := by
        rcases hj_reach with h | h
        · exact h
        · omega
      have hdir_eq : effBucketCap n_max = dirSlabsPerBucket n_max * slabSize n_max := by
        rw [effBucketCap_eq_bucketCap_of_pos hb_pos, (slabSize_eq_sq_of_pos hb_pos).1]
        unfold bucketCap dirSlabsPerBucket
        rw [ite_eq_right hb0]
        ring
      have hs_dir : wRegs x i_j / slabSize n_max < dirSlabsPerBucket n_max :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hdir_eq]; exact hj_cap)
      have hs_q : wRegs x i_j / slabSize n_max <
          gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj_slab)
      have hslab := hinv.multi_slab hb_pos
      have h14_pos : 0 < wRegs x3 14 := by rw [hx3_14]; exact hK_pos
      obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
        wDiv_execWithin 15 i_j 14 (by omega) (by omega) (by omega) x3 hctx3 h14_pos
      have hx4_14 : 0 < wRegs x4 14 := by
        rw [hr4, Function.update_of_ne (by decide), hx3_14]; exact hK_pos
      obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
        wMod_execWithin 16 i_j 14 (by omega) (by omega) (by omega) x4 hctx4 hx4_14
      obtain ⟨x6, hex6, hctx6, hm6, hr6⟩ :=
        wConstCode_execWithin 14 (slabSize n_max - 1) (by omega) x5 hctx5
          (hmax_fit.of_le (by omega))
      have hx6_14 : wRegs x6 14 = slabSize n_max - 1 := by rw [hr6, Function.update_self]
      have hx6_16 : wRegs x6 16 = wRegs x i_j % slabSize n_max := by
        rw [hr6, Function.update_of_ne (by decide), hr5, Function.update_self,
          hr4, Function.update_of_ne (by omega), Function.update_of_ne (by decide),
          hx3_k i_j hj, hx3_14]
      have hmod_le : wRegs x6 16 ≤ wRegs x6 14 := by
        rw [hx6_16, hx6_14]
        have := Nat.mod_lt (wRegs x i_j) hK_pos
        omega
      obtain ⟨x7, hex7, hctx7, hm7, hr7⟩ :=
        wSub_execWithin 16 14 16 (by omega) (by omega) (by omega) x6 hctx6 hmod_le
      have hx7_16 : wRegs x7 16 = slabSize n_max - 1 - wRegs x i_j % slabSize n_max := by
        rw [hr7, Function.update_self, hx6_14, hx6_16]
      have hx7_15 : wRegs x7 15 = wRegs x i_j / slabSize n_max := by
        rw [hr7, Function.update_of_ne (by decide), hr6, Function.update_of_ne (by decide),
          hr5, Function.update_of_ne (by decide), hr4, Function.update_self,
          hx3_k i_j hj, hx3_14]
      have hx7_b : wRegs x7 i_b = wRegs x i_b := by
        rw [hr7, Function.update_of_ne (by omega), hr6, Function.update_of_ne (by omega),
          hr5, Function.update_of_ne (by omega), hr4, Function.update_of_ne (by omega),
          hx3_k i_b hb]
      have hdir_idx : gmSlabDirBase n_max + dirSlabsPerBucket n_max * wRegs x7 i_b +
          wRegs x7 15 < globalMetaLen n_max := by
        rw [hx7_b, hx7_15, Nat.mul_comm (dirSlabsPerBucket n_max)]
        exact gmSlabDirIdx_lt hb_pos hb_lt hs_dir
      have hstr_le : dirSlabsPerBucket n_max ≤ globalMetaLen n_max := by
        rw [← gmSlabMetaBase_add_eq_globalMetaLen hb_pos]
        unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase
        have := Nat.le_mul_of_pos_left (dirSlabsPerBucket n_max) (numBuckets_pos n_max)
        omega
      have hbo_le : gmSlabDirBase n_max ≤ globalMetaLen n_max := by
        rw [← gmSlabMetaBase_add_eq_globalMetaLen hb_pos]
        unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase
        omega
      obtain ⟨x8, hex8, hctx8, hm8, hr8⟩ :=
        readGMAffineCode_wRegs hw hnU hU hspace i_b 15 15
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by decide) (by decide) (by decide) (by decide)
          (hgm_fit.of_le hstr_le) (hgm_fit.of_le hbo_le) x7 hctx7 hdir_idx
          (hgm_fit.of_le (le_of_lt hdir_idx))
      have hm70 : x7.mem = x.mem := by rw [hm7, hm6, hm5, hm4, hm30]
      have hx8_15 : wRegs x8 15 =
          slabPtrOf n_max (gmAt base U V w n_max h_space x.mem)
            (wRegs x i_b) (wRegs x i_j / slabSize n_max) := by
        rw [hr8, hm70, hx7_b, hx7_15]
        have hidx_eq : gmSlabDirBase n_max + dirSlabsPerBucket n_max * wRegs x i_b +
            wRegs x i_j / slabSize n_max =
            gmSlabDirIdx n_max (wRegs x i_b) (wRegs x i_j / slabSize n_max) := by
          unfold gmSlabDirIdx; ring
        simp only [uRegs, Function.update_self, hidx_eq]
        exact hslab.dir_eq (wRegs x i_b) hb_lt _ hs_q hs_dir
      have hx8_16 : wRegs x8 16 = slabSize n_max - 1 - wRegs x i_j % slabSize n_max := by
        rw [hr8, uRegs_cons, uRegs_cons, uRegs_cons, uRegs_nil,
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), hx7_16]
      obtain ⟨x9, hex9, hctx9, hm9, hr9⟩ :=
        wConstCode_execWithin 14 (slabSize n_max) (by omega) x8 hctx8 (hmax_fit.of_le hK_le)
      have hx9_15 : wRegs x9 15 = wRegs x8 15 := by rw [hr9, Function.update_of_ne (by decide)]
      have hx9_14 : wRegs x9 14 = slabSize n_max := by rw [hr9, Function.update_self]
      have hp_lt : slabPtrOf n_max (gmAt base U V w n_max h_space x.mem)
          (wRegs x i_b) (wRegs x i_j / slabSize n_max) <
          gmAt base U V w n_max h_space x.mem 0 := by
        rw [hslab.nslabs_eq]
        exact hslab.ptr_lt (wRegs x i_b) hb_lt _ hs_q
      have htot := hinv.multi_total_le hb_pos
      have hpK_le : (slabPtrOf n_max (gmAt base U V w n_max h_space x.mem)
          (wRegs x i_b) (wRegs x i_j / slabSize n_max) + 1) * slabSize n_max ≤
          gmAt base U V w n_max h_space x.mem 0 * slabSize n_max :=
        Nat.mul_le_mul_right _ hp_lt
      rw [Nat.add_one_mul] at hpK_le
      have hmul9_fit : Fits w (wRegs x9 15 * wRegs x9 14) := by
        rw [hx9_15, hx8_15, hx9_14]
        exact hmax_fit.of_le (by omega)
      obtain ⟨x10, hex10, hctx10, hm10, hr10⟩ :=
        wMul_execWithin 15 15 14 (by omega) (by omega) (by omega) x9 hctx9 hmul9_fit
      have hx10_15 : wRegs x10 15 =
          slabPtrOf n_max (gmAt base U V w n_max h_space x.mem)
            (wRegs x i_b) (wRegs x i_j / slabSize n_max) * slabSize n_max := by
        rw [hr10, Function.update_self, hx9_15, hx8_15, hx9_14]
      have hx10_16 : wRegs x10 16 = slabSize n_max - 1 - wRegs x i_j % slabSize n_max := by
        rw [hr10, Function.update_of_ne (by decide), hr9, Function.update_of_ne (by decide), hx8_16]
      have hadd10_fit : Fits w (wRegs x10 15 + wRegs x10 16) := by
        rw [hx10_15, hx10_16]
        exact hmax_fit.of_le (by omega)
      obtain ⟨x11, hex11, hctx11, hm11, hr11⟩ :=
        wAdd_execWithin i_out 15 16 (by omega) (by omega) (by omega) x10 hctx10 hadd10_fit
      refine ⟨x11,
        (hex1.seq (hex2.seq (hex3.seq (execWithin_branch_pos hcond
          (hex4.seq (hex5.seq (hex6.seq (hex7.seq (hex8.seq
            (hex9.seq (hex10.seq hex11))))))))))).mono
          (by omega),
        hctx11, by rw [hm11, hm10, hm9, hm8, hm70], ?_, ?_⟩
      · rw [hr11, Function.update_self, hx10_15, hx10_16]
        unfold slotOf
        simp [hb0, hj_slab]
      · intro k hk hne
        rw [hr11, Function.update_of_ne hne, hr10, Function.update_of_ne (by omega),
          hr9, Function.update_of_ne (by omega), hr8]
        have hk15 : k ≠ 15 := by omega
        have hk17 : k ≠ 17 := by omega
        have hk18 : k ≠ 18 := by omega
        simp only [uRegs, Function.update_of_ne hk15, Function.update_of_ne hk17,
          Function.update_of_ne hk18]
        rw [hr7, Function.update_of_ne (by omega), hr6, Function.update_of_ne (by omega),
          hr5, Function.update_of_ne (by omega), hr4, Function.update_of_ne (by omega),
          hx3_k k hk]
    · have hcond : ¬(Cond.lt (wReg r_hash i_j (by omega)) (wReg r_hash 15)).Holds x3 := by
        simp only [Cond.Holds, ← wRegs_apply]
        rw [hx3_k i_j hj, hx3_15]
        exact hj_slab
      have hj_ge :
          gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max ≤
            wRegs x i_j := by omega
      have htail := hinv.multi_tail hb_pos
      have hr_lt : wRegs x i_j -
          gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max <
          gmAt base U V w n_max h_space x.mem (gmRIdx (wRegs x i_b)) := by omega
      have hr_cap : wRegs x i_j -
          gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max <
          tailCapPerBucket n_max :=
        lt_of_lt_of_le hr_lt (htail.r_le (wRegs x i_b) hb_lt)
      have hle3 : wRegs x3 15 ≤ wRegs x3 i_j := by
        rw [hx3_15, hx3_k i_j hj]; exact hj_ge
      obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
        wSub_execWithin 15 i_j 15 (by omega) (by omega) (by omega) x3 hctx3 hle3
      have hx4_15 : wRegs x4 15 = wRegs x i_j -
          gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max := by
        rw [hr4, Function.update_self, hx3_k i_j hj, hx3_15]
      have hx4_b : wRegs x4 i_b = wRegs x i_b := by
        rw [hr4, Function.update_of_ne (by omega), hx3_k i_b hb]
      have htail_idx : gmTailPtrBase n_max + tailCapPerBucket n_max * wRegs x4 i_b +
          wRegs x4 15 < globalMetaLen n_max := by
        rw [hx4_b, hx4_15, Nat.mul_comm (tailCapPerBucket n_max)]
        simpa only [gmTailPtrIdx, gmTailPtrFlatIdx, add_assoc] using
          gmTailPtrIdx_lt hb_pos hb_lt hr_cap
      have hstr_le : tailCapPerBucket n_max ≤ globalMetaLen n_max := by
        rw [← gmSlabMetaBase_add_eq_globalMetaLen hb_pos]
        unfold gmSlabMetaBase gmTailOwnerBase maxTailItems
        have := Nat.le_mul_of_pos_left (tailCapPerBucket n_max) (numBuckets_pos n_max)
        omega
      have hbo_le : gmTailPtrBase n_max ≤ globalMetaLen n_max := by
        rw [← gmSlabMetaBase_add_eq_globalMetaLen hb_pos]
        unfold gmSlabMetaBase gmTailOwnerBase
        omega
      obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
        readGMAffineCode_wRegs hw hnU hU hspace i_b 15 15
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by decide) (by decide) (by decide) (by decide)
          (hgm_fit.of_le hstr_le) (hgm_fit.of_le hbo_le) x4 hctx4 htail_idx
          (hgm_fit.of_le (le_of_lt htail_idx))
      have hm40 : x4.mem = x.mem := by rw [hm4, hm30]
      have hx5_15 : wRegs x5 15 =
          gmAt base U V w n_max h_space x.mem
            (gmTailPtrIdx n_max (wRegs x i_b)
              (wRegs x i_j -
                gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max)) := by
        rw [hr5, hm40, hx4_b, hx4_15]
        have hidx_eq : gmTailPtrBase n_max + tailCapPerBucket n_max * wRegs x i_b +
            (wRegs x i_j -
              gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max) =
            gmTailPtrIdx n_max (wRegs x i_b)
              (wRegs x i_j -
                gmAt base U V w n_max h_space x.mem (gmQIdx (wRegs x i_b)) * slabSize n_max) := by
          unfold gmTailPtrIdx gmTailPtrFlatIdx; ring
        simp [uRegs, hidx_eq]
      obtain ⟨x6, hex6, hctx6, hm6, hr6⟩ :=
        wConstCode_execWithin 16 (n_max - 1) (by omega) x5 hctx5 (hmax_fit.of_le (by omega))
      have hx6_16 : wRegs x6 16 = n_max - 1 := by rw [hr6, Function.update_self]
      have hx6_15 : wRegs x6 15 = wRegs x5 15 := by rw [hr6, Function.update_of_ne (by decide)]
      have ht_lt : wRegs x5 15 < gmAt base U V w n_max h_space x.mem 1 := by
        rw [hx5_15, htail.ntails_eq]
        exact htail.ptr_lt (wRegs x i_b) hb_lt _ hr_lt
      have htot := hinv.multi_total_le hb_pos
      have hsub6 : wRegs x6 15 ≤ wRegs x6 16 := by
        rw [hx6_15, hx6_16]
        omega
      obtain ⟨x7, hex7, hctx7, hm7, hr7⟩ :=
        wSub_execWithin i_out 16 15 (by omega) (by omega) (by omega) x6 hctx6 hsub6
      refine ⟨x7,
        (hex1.seq (hex2.seq (hex3.seq (execWithin_branch_neg hcond
          (hex4.seq (hex5.seq (hex6.seq hex7))))))).mono (by omega),
        hctx7, by rw [hm7, hm6, hm5, hm40], ?_, ?_⟩
      · rw [hr7, Function.update_self, hx6_16, hx6_15, hx5_15]
        unfold slotOf
        simp [hb0, hj_slab]
      · intro k hk hne
        rw [hr7, Function.update_of_ne hne, hr6, Function.update_of_ne (by omega), hr5]
        have hk15 : k ≠ 15 := by omega
        have hk17 : k ≠ 17 := by omega
        have hk18 : k ≠ 18 := by omega
        simp only [uRegs, Function.update_of_ne hk15, Function.update_of_ne hk17,
          Function.update_of_ne hk18]
        rw [hr4, Function.update_of_ne (by omega), hx3_k k hk]

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
