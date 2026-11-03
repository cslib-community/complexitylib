/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlotInv

/-!
# Composite `GlobalMeta` and `LocalMeta` Bit-Packed Accessors

This module provides Word-RAM subroutines and correctness theorems for affine-indexed reads and
writes in `GlobalMeta` (`readGMLinCode`, `writeGMLinCode`, `readGMAffineCode`, `writeGMAffineCode`)
and for micro-bucket heads and doubly-linked list pointers in `LocalMeta` (`readLMHeadCode`,
`writeLMHeadCode`, `readLMMod4Code`, `writeLMMod4Code`).
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

/-! ## Section 4: Composite `GlobalMeta` and `LocalMeta` accessors and `resolveIndexedSlotCode` -/

theorem max_n_one_lt_two_pow_w {w U n_max : ℕ} (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w) :
    Fits w (max n_max 1) :=
  max_lt (lt_of_le_of_lt hnU hU) (Nat.one_lt_pow (by omega) (by decide))

theorem one_le_n_max_of_bucketBits_pos {n_max : ℕ} (hb : 0 < bucketBits n_max) : 1 ≤ n_max := by
  by_contra h
  have h0 : n_max = 0 := by omega
  subst h0
  simp [bucketBits] at hb

theorem nine_lt_two_pow_w {w base U V n_max h_space : ℕ} (_hw : 0 < w) (_hn : 1 ≤ n_max)
    (hspace : Fits w (base + totalSpace U V w n_max h_space)) :
    Fits w 9 := by
  have hl : 2 ≤ lmSubWords n_max w := Nat.le_add_left 2 _
  exact hspace.of_le (by dsimp only [totalSpace, offGM]; omega)

/-- Shorthand for sequentially updating a working-register map `(i, v)` list. -/
@[expose]
def uRegs (R : ℕ → ℕ) : List (ℕ × ℕ) → (ℕ → ℕ)
  | [] => R
  | (i, v) :: rest => uRegs (Function.update R i v) rest

@[simp]
theorem uRegs_nil (R : ℕ → ℕ) : uRegs R [] = R := rfl

@[simp]
theorem uRegs_cons (R : ℕ → ℕ) (i v : ℕ) (rest : List (ℕ × ℕ)) :
    uRegs R ((i, v) :: rest) = uRegs (Function.update R i v) rest := rfl

/-- Read `gm (base_off + stride * wRegs x i_b)` into working register `i_out` using `17` as index
scratch (`i_b ≠ 17`). -/
def readGMLinCode (r_hash U V w n_max h_space base_off stride i_b i_out : ℕ)
    (hb : i_b < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 17 stride)
    (.seq (wBinCode r_hash .mul 17 17 i_b (by omega) (by omega) hb)
      (.seq (wConstCode r_hash i_out base_off hout)
        (.seq (wBinCode r_hash .add 17 17 i_out (by omega) (by omega) hout)
          (readGMCode r_hash U V w n_max h_space 17 i_out (by omega) hout))))

theorem readGMLinCode_wRegs {r_hash w base U V n_max h_space base_off stride : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_out : ℕ) (hb : i_b < 19) (hout : i_out < 19)
    (hb17 : i_b ≠ 17) (hout17 : i_out ≠ 17)
    (hstr_fit : Fits w stride) (hbo_fit : Fits w base_off)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : base_off + stride * wRegs x i_b < globalMetaLen n_max)
    (hidx_fit : Fits w (base_off + stride * wRegs x i_b)) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readGMLinCode r_hash U V w n_max h_space base_off stride i_b i_out hb hout)
        x y 42 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = uRegs (wRegs x)
        [(17, base_off + stride * wRegs x i_b),
         (i_out, gmAt base U V w n_max h_space x.mem (base_off + stride * wRegs x i_b))] := by
  unfold readGMLinCode
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 17 stride (by omega) x hctx hstr_fit
  have hmul_fit : Fits w (wRegs x1 17 * wRegs x1 i_b) := by
    rw [hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wMul_execWithin 17 17 i_b (by omega) (by omega) hb x1 hctx1 hmul_fit
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wConstCode_execWithin i_out base_off hout x2 hctx2 hbo_fit
  have hadd_fit : Fits w (wRegs x3 17 + wRegs x3 i_out) := by
    rw [hr3, Function.update_of_ne hout17.symm, Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    wAdd_execWithin 17 17 i_out (by omega) (by omega) hout x3 hctx3 hadd_fit
  have hx4_17 : wRegs x4 17 = base_off + stride * wRegs x i_b := by
    rw [hr4, Function.update_self, hr3, Function.update_of_ne hout17.symm, Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    omega
  have hidx4 : wRegs x4 17 < globalMetaLen n_max := by rw [hx4_17]; exact hidx_lt
  obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
    readGMCode_wRegs hw hnU hU hspace 17 i_out (by omega) hout x4 hctx4 hidx4
  refine ⟨x5,
    (hex1.seq (hex2.seq (hex3.seq (hex4.seq hex5)))).mono (by omega),
    hctx5, by rw [hm5, hm4, hm3, hm2, hm1], ?_⟩
  rw [hr5, hx4_17, hm4, hm3, hm2, hm1, hr4, hr3, hr2, hr1]
  funext j
  by_cases hj_out : j = i_out
  · subst hj_out; simp [uRegs]
  · by_cases hj17 : j = 17
    · subst hj17
      simp only [uRegs, Function.update_self, Function.update_of_ne hj_out,
        Function.update_of_ne hb17]
      omega
    · simp [uRegs, hj_out, hj17]

/-- Write `wRegs x i_val` into `gm (base_off + stride * wRegs x i_b)` using `17` and `18` as
scratch (`i_b, i_val ∉ {17, 18}`). -/
def writeGMLinCode (r_hash U V w n_max h_space base_off stride i_b i_val : ℕ)
    (hb : i_b < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 17 stride)
    (.seq (wBinCode r_hash .mul 17 17 i_b (by omega) (by omega) hb)
      (.seq (wConstCode r_hash 18 base_off)
        (.seq (wBinCode r_hash .add 17 17 18 (by omega) (by omega) (by omega))
          (writeGMCode r_hash U V w n_max h_space 17 i_val (by omega) hval))))

theorem writeGMLinCode_wRegs {r_hash w base U V n_max h_space base_off stride : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_val : ℕ) (hb : i_b < 19) (hval : i_val < 19)
    (hb17 : i_b ≠ 17) (_hb18 : i_b ≠ 18) (hv17 : i_val ≠ 17) (hv18 : i_val ≠ 18)
    (hstr_fit : Fits w stride) (hbo_fit : Fits w base_off)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : base_off + stride * wRegs x i_b < globalMetaLen n_max)
    (hidx_fit : Fits w (base_off + stride * wRegs x i_b))
    (hval_lt : wRegs x i_val < 2 ^ globalPtrBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeGMLinCode r_hash U V w n_max h_space base_off stride i_b i_val hb hval)
        x y 53 ∧
      MachCtx w base y ∧
      wRegs y = uRegs (wRegs x)
        [(18, base_off), (17, base_off + stride * wRegs x i_b)] ∧
      (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem =
        Function.update (gmAt base U V w n_max h_space x.mem)
          (base_off + stride * wRegs x i_b) (wRegs x i_val) := by
  unfold writeGMLinCode
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 17 stride (by omega) x hctx hstr_fit
  have hmul_fit : Fits w (wRegs x1 17 * wRegs x1 i_b) := by
    rw [hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wMul_execWithin 17 17 i_b (by omega) (by omega) hb x1 hctx1 hmul_fit
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wConstCode_execWithin 18 base_off (by omega) x2 hctx2 hbo_fit
  have hadd_fit : Fits w (wRegs x3 17 + wRegs x3 18) := by
    rw [hr3, Function.update_of_ne (by decide), Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    wAdd_execWithin 17 17 18 (by omega) (by omega) (by omega) x3 hctx3 hadd_fit
  have hx4_17 : wRegs x4 17 = base_off + stride * wRegs x i_b := by
    rw [hr4, Function.update_self, hr3, Function.update_of_ne (by decide), Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    omega
  have hx4_val : wRegs x4 i_val = wRegs x i_val := by
    rw [hr4, Function.update_of_ne hv17, hr3, Function.update_of_ne hv18,
      hr2, Function.update_of_ne hv17, hr1, Function.update_of_ne hv17]
  have hidx4 : wRegs x4 17 < globalMetaLen n_max := by rw [hx4_17]; exact hidx_lt
  have hval4 : wRegs x4 i_val < 2 ^ globalPtrBits n_max := by rw [hx4_val]; exact hval_lt
  obtain ⟨x5, hex5, hctx5, hr5, hout5, hq5, hv5, hlm5, hgm5⟩ :=
    writeGMCode_wRegs hw hnU hU hspace 17 i_val (by omega) hval x4 hctx4 hidx4 hval4
  have hm40 : x4.mem = x.mem := by rw [hm4, hm3, hm2, hm1]
  refine ⟨x5,
    (hex1.seq (hex2.seq (hex3.seq (hex4.seq hex5)))).mono (by omega),
    hctx5, ?_,
    fun a ha => by rw [hout5 a ha, hm40],
    by rw [hq5, hm40], by rw [hv5, hm40], by rw [hlm5, hm40],
    by rw [hgm5, hx4_17, hx4_val, hm40]⟩
  rw [hr5, hr4, hr3, hr2, hr1]
  funext j
  by_cases hj17 : j = 17
  · subst hj17
    simp only [uRegs, Function.update_self, Function.update_of_ne (by decide : (17 : ℕ) ≠ 18),
      Function.update_of_ne hb17]
    omega
  · by_cases hj18 : j = 18
    · subst hj18; simp [uRegs, hj17]
    · simp [uRegs, hj17, hj18]

/-- Read `gm (base_off + stride * wRegs x i_b + wRegs x i_s)` into `i_out` using `17` and `18` as
scratch (`i_b, i_s ∉ {17, 18}`). -/
def readGMAffineCode (r_hash U V w n_max h_space base_off stride i_b i_s i_out : ℕ)
    (hb : i_b < 19 := by omega) (hs : i_s < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 17 stride)
    (.seq (wBinCode r_hash .mul 17 17 i_b (by omega) (by omega) hb)
      (.seq (wConstCode r_hash 18 base_off)
        (.seq (wBinCode r_hash .add 17 17 18 (by omega) (by omega) (by omega))
          (.seq (wBinCode r_hash .add 17 17 i_s (by omega) (by omega) hs)
            (readGMCode r_hash U V w n_max h_space 17 i_out (by omega) hout)))))

theorem readGMAffineCode_wRegs {r_hash w base U V n_max h_space base_off stride : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_s i_out : ℕ) (hb : i_b < 19) (hs : i_s < 19) (hout : i_out < 19)
    (hb17 : i_b ≠ 17) (_hb18 : i_b ≠ 18) (hs17 : i_s ≠ 17) (hs18 : i_s ≠ 18)
    (hout17 : i_out ≠ 17) (hout18 : i_out ≠ 18)
    (hstr_fit : Fits w stride) (hbo_fit : Fits w base_off)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : base_off + stride * wRegs x i_b + wRegs x i_s < globalMetaLen n_max)
    (hidx_fit : Fits w (base_off + stride * wRegs x i_b + wRegs x i_s)) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w
        (readGMAffineCode r_hash U V w n_max h_space base_off stride i_b i_s i_out hb hs hout)
        x y 43 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = uRegs (wRegs x)
        [(18, base_off),
         (17, base_off + stride * wRegs x i_b + wRegs x i_s),
         (i_out, gmAt base U V w n_max h_space x.mem
           (base_off + stride * wRegs x i_b + wRegs x i_s))] := by
  unfold readGMAffineCode
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 17 stride (by omega) x hctx hstr_fit
  have hmul_fit : Fits w (wRegs x1 17 * wRegs x1 i_b) := by
    rw [hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wMul_execWithin 17 17 i_b (by omega) (by omega) hb x1 hctx1 hmul_fit
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wConstCode_execWithin 18 base_off (by omega) x2 hctx2 hbo_fit
  have hadd1_fit : Fits w (wRegs x3 17 + wRegs x3 18) := by
    rw [hr3, Function.update_of_ne (by decide), Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    wAdd_execWithin 17 17 18 (by omega) (by omega) (by omega) x3 hctx3 hadd1_fit
  have hx4_17 : wRegs x4 17 = base_off + stride * wRegs x i_b := by
    rw [hr4, Function.update_self, hr3, Function.update_of_ne (by decide), Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    omega
  have hx4_s : wRegs x4 i_s = wRegs x i_s := by
    rw [hr4, Function.update_of_ne hs17, hr3, Function.update_of_ne hs18,
      hr2, Function.update_of_ne hs17, hr1, Function.update_of_ne hs17]
  have hadd2_fit : Fits w (wRegs x4 17 + wRegs x4 i_s) := by
    rw [hx4_17, hx4_s]; exact hidx_fit
  obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
    wAdd_execWithin 17 17 i_s (by omega) (by omega) hs x4 hctx4 hadd2_fit
  have hx5_17 : wRegs x5 17 = base_off + stride * wRegs x i_b + wRegs x i_s := by
    rw [hr5, Function.update_self, hx4_17, hx4_s]
  have hidx5 : wRegs x5 17 < globalMetaLen n_max := by rw [hx5_17]; exact hidx_lt
  obtain ⟨x6, hex6, hctx6, hm6, hr6⟩ :=
    readGMCode_wRegs hw hnU hU hspace 17 i_out (by omega) hout x5 hctx5 hidx5
  refine ⟨x6,
    (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq hex6))))).mono (by omega),
    hctx6, by rw [hm6, hm5, hm4, hm3, hm2, hm1], ?_⟩
  rw [hr6, hx5_17, hm5, hm4, hm3, hm2, hm1, hr5, hr4, hr3, hr2, hr1]
  funext j
  by_cases hj_out : j = i_out
  · subst hj_out; simp [uRegs]
  · by_cases hj17 : j = 17
    · subst hj17
      simp only [uRegs, Function.update_self, Function.update_of_ne hj_out,
        Function.update_of_ne (by decide : (17 : ℕ) ≠ 18),
        Function.update_of_ne hs17, Function.update_of_ne hs18, Function.update_of_ne hb17]
      omega
    · by_cases hj18 : j = 18
      · subst hj18; simp [uRegs, hj_out, hj17]
      · simp [uRegs, hj_out, hj17, hj18]

/-- Write `wRegs x i_val` into `gm (base_off + stride * wRegs x i_b + wRegs x i_s)` using `17` and
`18` as scratch (`i_b, i_s, i_val ∉ {17, 18}`). -/
def writeGMAffineCode (r_hash U V w n_max h_space base_off stride i_b i_s i_val : ℕ)
    (hb : i_b < 19 := by omega) (hs : i_s < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 17 stride)
    (.seq (wBinCode r_hash .mul 17 17 i_b (by omega) (by omega) hb)
      (.seq (wConstCode r_hash 18 base_off)
        (.seq (wBinCode r_hash .add 17 17 18 (by omega) (by omega) (by omega))
          (.seq (wBinCode r_hash .add 17 17 i_s (by omega) (by omega) hs)
            (writeGMCode r_hash U V w n_max h_space 17 i_val (by omega) hval)))))

theorem writeGMAffineCode_wRegs {r_hash w base U V n_max h_space base_off stride : ℕ}
    [NeZero r_hash] (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_s i_val : ℕ) (hb : i_b < 19) (hs : i_s < 19) (hval : i_val < 19)
    (hb17 : i_b ≠ 17) (_hb18 : i_b ≠ 18) (hs17 : i_s ≠ 17) (hs18 : i_s ≠ 18)
    (hv17 : i_val ≠ 17) (hv18 : i_val ≠ 18)
    (hstr_fit : Fits w stride) (hbo_fit : Fits w base_off)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : base_off + stride * wRegs x i_b + wRegs x i_s < globalMetaLen n_max)
    (hidx_fit : Fits w (base_off + stride * wRegs x i_b + wRegs x i_s))
    (hval_lt : wRegs x i_val < 2 ^ globalPtrBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w
        (writeGMAffineCode r_hash U V w n_max h_space base_off stride i_b i_s i_val hb hs hval)
        x y 54 ∧
      MachCtx w base y ∧
      wRegs y = uRegs (wRegs x)
        [(18, base_off), (17, base_off + stride * wRegs x i_b + wRegs x i_s)] ∧
      (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem =
        Function.update (gmAt base U V w n_max h_space x.mem)
          (base_off + stride * wRegs x i_b + wRegs x i_s) (wRegs x i_val) := by
  unfold writeGMAffineCode
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 17 stride (by omega) x hctx hstr_fit
  have hmul_fit : Fits w (wRegs x1 17 * wRegs x1 i_b) := by
    rw [hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wMul_execWithin 17 17 i_b (by omega) (by omega) hb x1 hctx1 hmul_fit
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wConstCode_execWithin 18 base_off (by omega) x2 hctx2 hbo_fit
  have hadd1_fit : Fits w (wRegs x3 17 + wRegs x3 18) := by
    rw [hr3, Function.update_of_ne (by decide), Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    exact hidx_fit.of_le (by omega)
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    wAdd_execWithin 17 17 18 (by omega) (by omega) (by omega) x3 hctx3 hadd1_fit
  have hx4_17 : wRegs x4 17 = base_off + stride * wRegs x i_b := by
    rw [hr4, Function.update_self, hr3, Function.update_of_ne (by decide), Function.update_self,
      hr2, Function.update_self, hr1, Function.update_self, Function.update_of_ne hb17]
    omega
  have hx4_s : wRegs x4 i_s = wRegs x i_s := by
    rw [hr4, Function.update_of_ne hs17, hr3, Function.update_of_ne hs18,
      hr2, Function.update_of_ne hs17, hr1, Function.update_of_ne hs17]
  have hadd2_fit : Fits w (wRegs x4 17 + wRegs x4 i_s) := by
    rw [hx4_17, hx4_s]; exact hidx_fit
  obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
    wAdd_execWithin 17 17 i_s (by omega) (by omega) hs x4 hctx4 hadd2_fit
  have hx5_17 : wRegs x5 17 = base_off + stride * wRegs x i_b + wRegs x i_s := by
    rw [hr5, Function.update_self, hx4_17, hx4_s]
  have hx5_val : wRegs x5 i_val = wRegs x i_val := by
    rw [hr5, Function.update_of_ne hv17, hr4, Function.update_of_ne hv17,
      hr3, Function.update_of_ne hv18, hr2, Function.update_of_ne hv17,
      hr1, Function.update_of_ne hv17]
  have hidx5 : wRegs x5 17 < globalMetaLen n_max := by rw [hx5_17]; exact hidx_lt
  have hval5 : wRegs x5 i_val < 2 ^ globalPtrBits n_max := by rw [hx5_val]; exact hval_lt
  obtain ⟨x6, hex6, hctx6, hr6, hout6, hq6, hv6, hlm6, hgm6⟩ :=
    writeGMCode_wRegs hw hnU hU hspace 17 i_val (by omega) hval x5 hctx5 hidx5 hval5
  have hm50 : x5.mem = x.mem := by rw [hm5, hm4, hm3, hm2, hm1]
  refine ⟨x6,
    (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq hex6))))).mono (by omega),
    hctx6, ?_,
    fun a ha => by rw [hout6 a ha, hm50],
    by rw [hq6, hm50], by rw [hv6, hm50], by rw [hlm6, hm50],
    by rw [hgm6, hx5_17, hx5_val, hm50]⟩
  rw [hr6, hr5, hr4, hr3, hr2, hr1]
  funext j
  by_cases hj17 : j = 17
  · subst hj17
    simp only [uRegs, Function.update_self,
      Function.update_of_ne (by decide : (17 : ℕ) ≠ 18),
      Function.update_of_ne hs17, Function.update_of_ne hs18, Function.update_of_ne hb17]
    omega
  · by_cases hj18 : j = 18
    · subst hj18; simp [uRegs, hj17]
    · simp [uRegs, hj17, hj18]

/-! ### `LocalMeta` accessors (`head[b, m]`, `prev[b, j]`, `next[b, j]`) -/

/-- Read `head[b, m] = lmAt (0, b * numMicroPerBucket n_max + m)` into `i_out` using `17` as
scratch (`i_b, i_m, i_out ≠ 17`). -/
def readLMHeadCode (r_hash U V w n_max h_space i_b i_m i_out : ℕ)
    (hb : i_b < 19 := by omega) (hm : i_m < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 17 (numMicroPerBucket n_max))
    (.seq (wBinCode r_hash .mul 17 i_b 17 (by omega) hb (by omega))
      (.seq (wBinCode r_hash .add 17 17 i_m (by omega) (by omega) hm)
        (readLMCode r_hash U V w n_max h_space 0 17 i_out (by omega) hout)))

theorem readLMHeadCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_m i_out : ℕ) (hb : i_b < 19) (hm : i_m < 19) (hout : i_out < 19)
    (hb17 : i_b ≠ 17) (hm17 : i_m ≠ 17) (hout17 : i_out ≠ 17)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hb_lt : wRegs x i_b < numBuckets n_max)
    (hm_lt : wRegs x i_m < numMicroPerBucket n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readLMHeadCode r_hash U V w n_max h_space i_b i_m i_out hb hm hout)
        x y 41 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = uRegs (wRegs x)
        [(17, wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m),
         (i_out, lmAt base U V w n_max h_space x.mem
           (0, wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m))] := by
  unfold readLMHeadCode
  have htot_fit : Fits w (totalMicroBuckets n_max) :=
    lt_of_le_of_lt (totalMicroBuckets_le n_max) (max_n_one_lt_two_pow_w hw hnU hU)
  have htot_eq := totalMicroBuckets_eq_mul n_max
  have hidx_lt : wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m <
      totalMicroBuckets n_max := by
    have hmul : (wRegs x i_b + 1) * numMicroPerBucket n_max ≤
        numBuckets n_max * numMicroPerBucket n_max :=
      Nat.mul_le_mul_right _ hb_lt
    rw [Nat.add_one_mul] at hmul
    omega
  have hmb_fit : Fits w (numMicroPerBucket n_max) :=
    htot_fit.of_le (by
      have := numBuckets_pos n_max
      have hle := Nat.le_mul_of_pos_left (numMicroPerBucket n_max) this
      omega)
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 17 (numMicroPerBucket n_max) (by omega) x hctx hmb_fit
  have hmul_fit : Fits w (wRegs x1 i_b * wRegs x1 17) := by
    rw [hr1, Function.update_of_ne hb17, Function.update_self]
    exact htot_fit.of_le (by omega)
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wMul_execWithin 17 i_b 17 (by omega) hb (by omega) x1 hctx1 hmul_fit
  have hadd_fit : Fits w (wRegs x2 17 + wRegs x2 i_m) := by
    rw [hr2, Function.update_self, Function.update_of_ne hm17,
      hr1, Function.update_of_ne hb17, Function.update_self, Function.update_of_ne hm17]
    exact htot_fit.of_le (by omega)
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wAdd_execWithin 17 17 i_m (by omega) (by omega) hm x2 hctx2 hadd_fit
  have hx3_17 : wRegs x3 17 = wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m := by
    rw [hr3, Function.update_self, hr2, Function.update_self, Function.update_of_ne hm17,
      hr1, Function.update_of_ne hb17, Function.update_self, Function.update_of_ne hm17]
  have hidx3 : wRegs x3 17 < totalMicroBuckets n_max := by rw [hx3_17]; exact hidx_lt
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    readLMCode_wRegs hw hnU hU hspace (by decide : 0 < 9) 17 i_out (by omega) hout x3 hctx3 hidx3
  refine ⟨x4,
    (hex1.seq (hex2.seq (hex3.seq hex4))).mono (by omega),
    hctx4, by rw [hm4, hm3, hm2, hm1], ?_⟩
  rw [hr4, hx3_17, hm3, hm2, hm1, hr3, hr2, hr1]
  funext j
  by_cases hj_out : j = i_out
  · subst hj_out; simp [uRegs]
  · by_cases hj17 : j = 17
    · subst hj17; simp [uRegs, hj_out, hm17, hb17]
    · simp [uRegs, hj_out, hj17]

/-- Write `wRegs x i_val` into `head[b, m] = lmAt (0, b * numMicroPerBucket n_max + m)` using
`17` as scratch (`i_b, i_m, i_val ≠ 17`). -/
def writeLMHeadCode (r_hash U V w n_max h_space i_b i_m i_val : ℕ)
    (hb : i_b < 19 := by omega) (hm : i_m < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 17 (numMicroPerBucket n_max))
    (.seq (wBinCode r_hash .mul 17 i_b 17 (by omega) hb (by omega))
      (.seq (wBinCode r_hash .add 17 17 i_m (by omega) (by omega) hm)
        (writeLMCode r_hash U V w n_max h_space 0 17 i_val (by omega) hval)))

theorem writeLMHeadCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_b i_m i_val : ℕ) (hb : i_b < 19) (hm : i_m < 19) (hval : i_val < 19)
    (hb17 : i_b ≠ 17) (hm17 : i_m ≠ 17) (hv17 : i_val ≠ 17)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hb_lt : wRegs x i_b < numBuckets n_max)
    (hm_lt : wRegs x i_m < numMicroPerBucket n_max)
    (hval_lt : wRegs x i_val < 2 ^ effBucketPosBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeLMHeadCode r_hash U V w n_max h_space i_b i_m i_val hb hm hval)
        x y 52 ∧
      MachCtx w base y ∧
      wRegs y = uRegs (wRegs x)
        [(17, wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m)] ∧
      (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem =
        Function.update (lmAt base U V w n_max h_space x.mem)
          (0, wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m) (wRegs x i_val) ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  unfold writeLMHeadCode
  have htot_fit : Fits w (totalMicroBuckets n_max) :=
    lt_of_le_of_lt (totalMicroBuckets_le n_max) (max_n_one_lt_two_pow_w hw hnU hU)
  have htot_eq := totalMicroBuckets_eq_mul n_max
  have hidx_lt : wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m <
      totalMicroBuckets n_max := by
    have hmul : (wRegs x i_b + 1) * numMicroPerBucket n_max ≤
        numBuckets n_max * numMicroPerBucket n_max :=
      Nat.mul_le_mul_right _ hb_lt
    rw [Nat.add_one_mul] at hmul
    omega
  have hmb_fit : Fits w (numMicroPerBucket n_max) :=
    htot_fit.of_le (by
      have := numBuckets_pos n_max
      have hle := Nat.le_mul_of_pos_left (numMicroPerBucket n_max) this
      omega)
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 17 (numMicroPerBucket n_max) (by omega) x hctx hmb_fit
  have hmul_fit : Fits w (wRegs x1 i_b * wRegs x1 17) := by
    rw [hr1, Function.update_of_ne hb17, Function.update_self]
    exact htot_fit.of_le (by omega)
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wMul_execWithin 17 i_b 17 (by omega) hb (by omega) x1 hctx1 hmul_fit
  have hadd_fit : Fits w (wRegs x2 17 + wRegs x2 i_m) := by
    rw [hr2, Function.update_self, Function.update_of_ne hm17,
      hr1, Function.update_of_ne hb17, Function.update_self, Function.update_of_ne hm17]
    exact htot_fit.of_le (by omega)
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wAdd_execWithin 17 17 i_m (by omega) (by omega) hm x2 hctx2 hadd_fit
  have hx3_17 : wRegs x3 17 = wRegs x i_b * numMicroPerBucket n_max + wRegs x i_m := by
    rw [hr3, Function.update_self, hr2, Function.update_self, Function.update_of_ne hm17,
      hr1, Function.update_of_ne hb17, Function.update_self, Function.update_of_ne hm17]
  have hx3_val : wRegs x3 i_val = wRegs x i_val := by
    rw [hr3, Function.update_of_ne hv17, hr2, Function.update_of_ne hv17,
      hr1, Function.update_of_ne hv17]
  have hidx3 : wRegs x3 17 < totalMicroBuckets n_max := by rw [hx3_17]; exact hidx_lt
  have hval3 : wRegs x3 i_val < 2 ^ effBucketPosBits n_max := by rw [hx3_val]; exact hval_lt
  obtain ⟨x4, hex4, hctx4, hr4, hout4, hq4, hv4, hlm4, hgm4⟩ :=
    writeLMCode_wRegs hw hnU hU hspace (by decide : 0 < 9) 17 i_val (by omega) hval x3 hctx3
      hidx3 hval3
  have hm30 : x3.mem = x.mem := by rw [hm3, hm2, hm1]
  refine ⟨x4,
    (hex1.seq (hex2.seq (hex3.seq hex4))).mono (by omega),
    hctx4, ?_,
    fun a ha => by rw [hout4 a ha, hm30],
    by rw [hq4, hm30], by rw [hv4, hm30], by rw [hlm4, hx3_17, hx3_val, hm30],
    by rw [hgm4, hm30]⟩
  rw [hr4, hr3, hr2, hr1]
  funext j
  by_cases hj17 : j = 17
  · subst hj17; simp [uRegs, hm17, hb17]
  · simp [uRegs, hj17]

theorem execWithin_branch_pos {B : Basis} {r w t : ℕ} {c : Cond r} {pos neg : Code B r}
    {x y : Data r} (hc : c.Holds x) (hpos : ExecWithin w pos x y t) :
    ExecWithin w (.branch c pos neg) x y (t + 1) := by
  rcases hpos with ⟨n, hn, hex⟩
  exact ⟨n + 1, by omega, Exec.branch_pos hc hex⟩

theorem execWithin_branch_neg {B : Basis} {r w t : ℕ} {c : Cond r} {pos neg : Code B r}
    {x y : Data r} (hc : ¬c.Holds x) (hneg : ExecWithin w neg x y t) :
    ExecWithin w (.branch c pos neg) x y (t + 2) := by
  rcases hneg with ⟨n, hn, hex⟩
  exact ⟨n + 2, by omega, Exec.branch_neg hc hex⟩

/-- Read `prev[b, j]` (`c_base = 1`) or `next[b, j]` (`c_base = 5`) for `j < effBucketCap n_max`:
computes `q = j / 4 < numMicroPerBucket n_max` and `r = j % 4 < 4`, then dispatches on `r` to
`readLMCode (c_base + r) (b * numMicroPerBucket n_max + q) i_out`. Uses `16, 17, 18` as
scratch (`i_b, i_j, i_out ∉ {16, 17, 18}`). -/
def readLMMod4Code (r_hash U V w n_max h_space c_base i_b i_j i_out : ℕ)
    (hb : i_b < 19 := by omega) (hj : i_j < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 16 4)
    (.seq (wBinCode r_hash .div 17 i_j 16 (by omega) hj (by omega))
      (.seq (wBinCode r_hash .mod 18 i_j 16 (by omega) hj (by omega))
        (.seq (wConstCode r_hash 16 (numMicroPerBucket n_max))
          (.seq (wBinCode r_hash .mul 16 i_b 16 (by omega) hb (by omega))
            (.seq (wBinCode r_hash .add 17 16 17 (by omega) (by omega) (by omega))
              (.seq (wConstCode r_hash 16 0)
                (.branch (.eq (wReg r_hash 18) (wReg r_hash 16))
                  (readLMCode r_hash U V w n_max h_space c_base 17 i_out (by omega) hout)
                  (.seq (wConstCode r_hash 16 1)
                    (.branch (.eq (wReg r_hash 18) (wReg r_hash 16))
                      (readLMCode r_hash U V w n_max h_space (c_base + 1) 17 i_out (by omega) hout)
                      (.seq (wConstCode r_hash 16 2)
                        (.branch (.eq (wReg r_hash 18) (wReg r_hash 16))
                          (readLMCode r_hash U V w n_max h_space (c_base + 2) 17 i_out
                            (by omega) hout)
                          (readLMCode r_hash U V w n_max h_space (c_base + 3) 17 i_out
                            (by omega) hout))))))))))))

theorem readLMMod4Code_wRegs {r_hash w base U V n_max h_space c_base : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hn : 1 ≤ n_max) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (hc : c_base + 3 < 9)
    (i_b i_j i_out : ℕ) (hb : i_b < 19) (hj : i_j < 19) (hout : i_out < 19)
    (hb16 : i_b ≠ 16) (hb17 : i_b ≠ 17) (hb18 : i_b ≠ 18)
    (hj16 : i_j ≠ 16) (hj17 : i_j ≠ 17) (_hj18 : i_j ≠ 18)
    (_hout16 : i_out ≠ 16) (_hout17 : i_out ≠ 17) (_hout18 : i_out ≠ 18)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hb_lt : wRegs x i_b < numBuckets n_max)
    (hj_lt : wRegs x i_j < effBucketCap n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readLMMod4Code r_hash U V w n_max h_space c_base i_b i_j i_out hb hj hout)
        x y 53 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y i_out = lmAt base U V w n_max h_space x.mem
        (c_base + wRegs x i_j % 4,
         wRegs x i_b * numMicroPerBucket n_max + wRegs x i_j / 4) ∧
      (∀ k < 16, k ≠ i_out → wRegs y k = wRegs x k) := by
  unfold readLMMod4Code
  have h9_fit : Fits w 9 := nine_lt_two_pow_w hw hn hspace
  have h4_fit : Fits w 4 := h9_fit.of_le (by omega)
  have htot_fit : Fits w (totalMicroBuckets n_max) :=
    lt_of_le_of_lt (totalMicroBuckets_le n_max) (max_n_one_lt_two_pow_w hw hnU hU)
  have htot_eq := totalMicroBuckets_eq_mul n_max
  have hq_lt : wRegs x i_j / 4 < numMicroPerBucket n_max := by
    unfold effBucketCap at hj_lt
    omega
  have hidx_lt : wRegs x i_b * numMicroPerBucket n_max + wRegs x i_j / 4 <
      totalMicroBuckets n_max := by
    have hmul : (wRegs x i_b + 1) * numMicroPerBucket n_max ≤
        numBuckets n_max * numMicroPerBucket n_max :=
      Nat.mul_le_mul_right _ hb_lt
    rw [Nat.add_one_mul] at hmul
    omega
  have hmb_fit : Fits w (numMicroPerBucket n_max) :=
    htot_fit.of_le (by
      have := numBuckets_pos n_max
      have hle := Nat.le_mul_of_pos_left (numMicroPerBucket n_max) this
      omega)
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 16 4 (by omega) x hctx h4_fit
  have hx1_16 : 0 < wRegs x1 16 := by rw [hr1, Function.update_self]; omega
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wDiv_execWithin 17 i_j 16 (by omega) hj (by omega) x1 hctx1 hx1_16
  have hx2_16 : 0 < wRegs x2 16 := by
    rw [hr2, Function.update_of_ne (by decide), hr1, Function.update_self]; omega
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wMod_execWithin 18 i_j 16 (by omega) hj (by omega) x2 hctx2 hx2_16
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    wConstCode_execWithin 16 (numMicroPerBucket n_max) (by omega) x3 hctx3 hmb_fit
  have hx4_b : wRegs x4 i_b = wRegs x i_b := by
    rw [hr4, Function.update_of_ne hb16, hr3, Function.update_of_ne hb18,
      hr2, Function.update_of_ne hb17, hr1, Function.update_of_ne hb16]
  have hmul_fit : Fits w (wRegs x4 i_b * wRegs x4 16) := by
    rw [hx4_b, hr4, Function.update_self]
    exact htot_fit.of_le (by omega)
  obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
    wMul_execWithin 16 i_b 16 (by omega) hb (by omega) x4 hctx4 hmul_fit
  have hx5_16 : wRegs x5 16 = wRegs x i_b * numMicroPerBucket n_max := by
    rw [hr5, Function.update_self, hx4_b, hr4, Function.update_self]
  have hx5_17 : wRegs x5 17 = wRegs x i_j / 4 := by
    rw [hr5, Function.update_of_ne (by decide), hr4, Function.update_of_ne (by decide),
      hr3, Function.update_of_ne (by decide), hr2, Function.update_self,
      hr1, Function.update_of_ne hj16, Function.update_self]
  have hadd_fit : Fits w (wRegs x5 16 + wRegs x5 17) := by
    rw [hx5_16, hx5_17]; exact htot_fit.of_le (by omega)
  obtain ⟨x6, hex6, hctx6, hm6, hr6⟩ :=
    wAdd_execWithin 17 16 17 (by omega) (by omega) (by omega) x5 hctx5 hadd_fit
  have hx6_17 : wRegs x6 17 = wRegs x i_b * numMicroPerBucket n_max + wRegs x i_j / 4 := by
    rw [hr6, Function.update_self, hx5_16, hx5_17]
  have hx6_18 : wRegs x6 18 = wRegs x i_j % 4 := by
    rw [hr6, Function.update_of_ne (by decide), hr5, Function.update_of_ne (by decide),
      hr4, Function.update_of_ne (by decide), hr3, Function.update_self,
      hr2, Function.update_of_ne hj17, Function.update_of_ne (by decide),
      hr1, Function.update_of_ne hj16, Function.update_self]
  have hx6_k : ∀ k < 16, wRegs x6 k = wRegs x k := by
    intro k hk
    rw [hr6, Function.update_of_ne (by omega), hr5, Function.update_of_ne (by omega),
      hr4, Function.update_of_ne (by omega), hr3, Function.update_of_ne (by omega),
      hr2, Function.update_of_ne (by omega), hr1, Function.update_of_ne (by omega)]
  have hm60 : x6.mem = x.mem := by rw [hm6, hm5, hm4, hm3, hm2, hm1]
  obtain ⟨x7, hex7, hctx7, hm7, hr7⟩ :=
    wConstCode_execWithin 16 0 (by omega) x6 hctx6 (h4_fit.of_le (by omega))
  have hx7_17 : wRegs x7 17 = wRegs x6 17 := by rw [hr7, Function.update_of_ne (by decide)]
  have hx7_18 : wRegs x7 18 = wRegs x6 18 := by rw [hr7, Function.update_of_ne (by decide)]
  have hx7_16 : wRegs x7 16 = 0 := by rw [hr7, Function.update_self]
  by_cases hr0 : wRegs x i_j % 4 = 0
  · have hcond0 : (Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x7 := by
      simp only [Cond.Holds, ← wRegs_apply]
      rw [hx7_18, hx6_18, hx7_16, hr0]
    have hidx7 : wRegs x7 17 < totalMicroBuckets n_max := by rw [hx7_17, hx6_17]; exact hidx_lt
    obtain ⟨y, hexy, hctxy, hmy, hry⟩ :=
      readLMCode_wRegs hw hnU hU hspace (by omega : c_base < 9) 17 i_out (by omega) hout
        x7 hctx7 hidx7
    refine ⟨y,
      (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
        (execWithin_branch_pos hcond0 hexy)))))))).mono (by omega),
      hctxy, by rw [hmy, hm7, hm60], ?_, ?_⟩
    · rw [hry, Function.update_self, hx7_17, hx6_17, hm7, hm60, hr0, Nat.add_zero]
    · intro k hk hne
      rw [hry, Function.update_of_ne hne, hr7, Function.update_of_ne (by omega), hx6_k k hk]
  · have hcond0 : ¬(Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x7 := by
      simp only [Cond.Holds, ← wRegs_apply]
      rw [hx7_18, hx6_18, hx7_16]; exact hr0
    obtain ⟨x8, hex8, hctx8, hm8, hr8⟩ :=
      wConstCode_execWithin 16 1 (by omega) x7 hctx7 (h4_fit.of_le (by omega))
    have hx8_17 : wRegs x8 17 = wRegs x6 17 := by
      rw [hr8, Function.update_of_ne (by decide), hx7_17]
    have hx8_18 : wRegs x8 18 = wRegs x6 18 := by
      rw [hr8, Function.update_of_ne (by decide), hx7_18]
    have hx8_16 : wRegs x8 16 = 1 := by rw [hr8, Function.update_self]
    by_cases hr1_eq : wRegs x i_j % 4 = 1
    · have hcond1 : (Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x8 := by
        simp only [Cond.Holds, ← wRegs_apply]
        rw [hx8_18, hx6_18, hx8_16, hr1_eq]
      have hidx8 : wRegs x8 17 < totalMicroBuckets n_max := by rw [hx8_17, hx6_17]; exact hidx_lt
      obtain ⟨y, hexy, hctxy, hmy, hry⟩ :=
        readLMCode_wRegs hw hnU hU hspace (by omega : c_base + 1 < 9) 17 i_out (by omega) hout
          x8 hctx8 hidx8
      refine ⟨y,
        (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
          (execWithin_branch_neg hcond0 (hex8.seq (execWithin_branch_pos hcond1 hexy)))))))))).mono
          (by omega),
        hctxy, by rw [hmy, hm8, hm7, hm60], ?_, ?_⟩
      · rw [hry, Function.update_self, hx8_17, hx6_17, hm8, hm7, hm60, hr1_eq]
      · intro k hk hne
        rw [hry, Function.update_of_ne hne, hr8, Function.update_of_ne (by omega),
          hr7, Function.update_of_ne (by omega), hx6_k k hk]
    · have hcond1 : ¬(Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x8 := by
        simp only [Cond.Holds, ← wRegs_apply]
        rw [hx8_18, hx6_18, hx8_16]; exact hr1_eq
      obtain ⟨x9, hex9, hctx9, hm9, hr9⟩ :=
        wConstCode_execWithin 16 2 (by omega) x8 hctx8 (h4_fit.of_le (by omega))
      have hx9_17 : wRegs x9 17 = wRegs x6 17 := by
        rw [hr9, Function.update_of_ne (by decide), hx8_17]
      have hx9_18 : wRegs x9 18 = wRegs x6 18 := by
        rw [hr9, Function.update_of_ne (by decide), hx8_18]
      have hx9_16 : wRegs x9 16 = 2 := by rw [hr9, Function.update_self]
      by_cases hr2_eq : wRegs x i_j % 4 = 2
      · have hcond2 : (Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x9 := by
          simp only [Cond.Holds, ← wRegs_apply]
          rw [hx9_18, hx6_18, hx9_16, hr2_eq]
        have hidx9 : wRegs x9 17 < totalMicroBuckets n_max := by rw [hx9_17, hx6_17]; exact hidx_lt
        obtain ⟨y, hexy, hctxy, hmy, hry⟩ :=
          readLMCode_wRegs hw hnU hU hspace (by omega : c_base + 2 < 9) 17 i_out (by omega) hout
            x9 hctx9 hidx9
        refine ⟨y,
          (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
            (execWithin_branch_neg hcond0 (hex8.seq (execWithin_branch_neg hcond1
              (hex9.seq (execWithin_branch_pos hcond2 hexy)))))))))))).mono (by omega),
          hctxy, by rw [hmy, hm9, hm8, hm7, hm60], ?_, ?_⟩
        · rw [hry, Function.update_self, hx9_17, hx6_17, hm9, hm8, hm7, hm60, hr2_eq]
        · intro k hk hne
          rw [hry, Function.update_of_ne hne, hr9, Function.update_of_ne (by omega),
            hr8, Function.update_of_ne (by omega), hr7, Function.update_of_ne (by omega),
            hx6_k k hk]
      · have hr3_eq : wRegs x i_j % 4 = 3 := by omega
        have hcond2 : ¬(Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x9 := by
          simp only [Cond.Holds, ← wRegs_apply]
          rw [hx9_18, hx6_18, hx9_16]; exact hr2_eq
        have hidx9 : wRegs x9 17 < totalMicroBuckets n_max := by rw [hx9_17, hx6_17]; exact hidx_lt
        obtain ⟨y, hexy, hctxy, hmy, hry⟩ :=
          readLMCode_wRegs hw hnU hU hspace (by omega : c_base + 3 < 9) 17 i_out (by omega) hout
            x9 hctx9 hidx9
        refine ⟨y,
          (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
            (execWithin_branch_neg hcond0 (hex8.seq (execWithin_branch_neg hcond1
              (hex9.seq (execWithin_branch_neg hcond2 hexy)))))))))))).mono (by omega),
          hctxy, by rw [hmy, hm9, hm8, hm7, hm60], ?_, ?_⟩
        · rw [hry, Function.update_self, hx9_17, hx6_17, hm9, hm8, hm7, hm60, hr3_eq]
        · intro k hk hne
          rw [hry, Function.update_of_ne hne, hr9, Function.update_of_ne (by omega),
            hr8, Function.update_of_ne (by omega), hr7, Function.update_of_ne (by omega),
            hx6_k k hk]

/-- Write `wRegs x i_val` into `prev[b, j]` (`c_base = 1`) or `next[b, j]` (`c_base = 5`) for
`j < effBucketCap n_max`. Uses `16, 17, 18` as scratch (`i_b, i_j, i_val ∉ {16, 17, 18}`). -/
def writeLMMod4Code (r_hash U V w n_max h_space c_base i_b i_j i_val : ℕ)
    (hb : i_b < 19 := by omega) (hj : i_j < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq (wConstCode r_hash 16 4)
    (.seq (wBinCode r_hash .div 17 i_j 16 (by omega) hj (by omega))
      (.seq (wBinCode r_hash .mod 18 i_j 16 (by omega) hj (by omega))
        (.seq (wConstCode r_hash 16 (numMicroPerBucket n_max))
          (.seq (wBinCode r_hash .mul 16 i_b 16 (by omega) hb (by omega))
            (.seq (wBinCode r_hash .add 17 16 17 (by omega) (by omega) (by omega))
              (.seq (wConstCode r_hash 16 0)
                (.branch (.eq (wReg r_hash 18) (wReg r_hash 16))
                  (writeLMCode r_hash U V w n_max h_space c_base 17 i_val (by omega) hval)
                  (.seq (wConstCode r_hash 16 1)
                    (.branch (.eq (wReg r_hash 18) (wReg r_hash 16))
                      (writeLMCode r_hash U V w n_max h_space (c_base + 1) 17 i_val
                        (by omega) hval)
                      (.seq (wConstCode r_hash 16 2)
                        (.branch (.eq (wReg r_hash 18) (wReg r_hash 16))
                          (writeLMCode r_hash U V w n_max h_space (c_base + 2) 17 i_val
                            (by omega) hval)
                          (writeLMCode r_hash U V w n_max h_space (c_base + 3) 17 i_val
                            (by omega) hval))))))))))))

theorem writeLMMod4Code_wRegs {r_hash w base U V n_max h_space c_base : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hn : 1 ≤ n_max) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (hc : c_base + 3 < 9)
    (i_b i_j i_val : ℕ) (hb : i_b < 19) (hj : i_j < 19) (hval : i_val < 19)
    (hb16 : i_b ≠ 16) (hb17 : i_b ≠ 17) (hb18 : i_b ≠ 18)
    (hj16 : i_j ≠ 16) (hj17 : i_j ≠ 17) (_hj18 : i_j ≠ 18)
    (hv16 : i_val ≠ 16) (hv17 : i_val ≠ 17) (hv18 : i_val ≠ 18)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hb_lt : wRegs x i_b < numBuckets n_max)
    (hj_lt : wRegs x i_j < effBucketCap n_max)
    (hval_lt : wRegs x i_val < 2 ^ effBucketPosBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeLMMod4Code r_hash U V w n_max h_space c_base i_b i_j i_val hb hj hval)
        x y 64 ∧
      MachCtx w base y ∧
      (∀ k < 16, wRegs y k = wRegs x k) ∧
      (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem =
        Function.update (lmAt base U V w n_max h_space x.mem)
          (c_base + wRegs x i_j % 4,
           wRegs x i_b * numMicroPerBucket n_max + wRegs x i_j / 4)
          (wRegs x i_val) ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  unfold writeLMMod4Code
  have h9_fit : Fits w 9 := nine_lt_two_pow_w hw hn hspace
  have h4_fit : Fits w 4 := h9_fit.of_le (by omega)
  have htot_fit : Fits w (totalMicroBuckets n_max) :=
    lt_of_le_of_lt (totalMicroBuckets_le n_max) (max_n_one_lt_two_pow_w hw hnU hU)
  have htot_eq := totalMicroBuckets_eq_mul n_max
  have hq_lt : wRegs x i_j / 4 < numMicroPerBucket n_max := by
    unfold effBucketCap at hj_lt
    omega
  have hidx_lt : wRegs x i_b * numMicroPerBucket n_max + wRegs x i_j / 4 <
      totalMicroBuckets n_max := by
    have hmul : (wRegs x i_b + 1) * numMicroPerBucket n_max ≤
        numBuckets n_max * numMicroPerBucket n_max :=
      Nat.mul_le_mul_right _ hb_lt
    rw [Nat.add_one_mul] at hmul
    omega
  have hmb_fit : Fits w (numMicroPerBucket n_max) :=
    htot_fit.of_le (by
      have := numBuckets_pos n_max
      have hle := Nat.le_mul_of_pos_left (numMicroPerBucket n_max) this
      omega)
  obtain ⟨x1, hex1, hctx1, hm1, hr1⟩ :=
    wConstCode_execWithin 16 4 (by omega) x hctx h4_fit
  have hx1_16 : 0 < wRegs x1 16 := by rw [hr1, Function.update_self]; omega
  obtain ⟨x2, hex2, hctx2, hm2, hr2⟩ :=
    wDiv_execWithin 17 i_j 16 (by omega) hj (by omega) x1 hctx1 hx1_16
  have hx2_16 : 0 < wRegs x2 16 := by
    rw [hr2, Function.update_of_ne (by decide), hr1, Function.update_self]; omega
  obtain ⟨x3, hex3, hctx3, hm3, hr3⟩ :=
    wMod_execWithin 18 i_j 16 (by omega) hj (by omega) x2 hctx2 hx2_16
  obtain ⟨x4, hex4, hctx4, hm4, hr4⟩ :=
    wConstCode_execWithin 16 (numMicroPerBucket n_max) (by omega) x3 hctx3 hmb_fit
  have hx4_b : wRegs x4 i_b = wRegs x i_b := by
    rw [hr4, Function.update_of_ne hb16, hr3, Function.update_of_ne hb18,
      hr2, Function.update_of_ne hb17, hr1, Function.update_of_ne hb16]
  have hmul_fit : Fits w (wRegs x4 i_b * wRegs x4 16) := by
    rw [hx4_b, hr4, Function.update_self]
    exact htot_fit.of_le (by omega)
  obtain ⟨x5, hex5, hctx5, hm5, hr5⟩ :=
    wMul_execWithin 16 i_b 16 (by omega) hb (by omega) x4 hctx4 hmul_fit
  have hx5_16 : wRegs x5 16 = wRegs x i_b * numMicroPerBucket n_max := by
    rw [hr5, Function.update_self, hx4_b, hr4, Function.update_self]
  have hx5_17 : wRegs x5 17 = wRegs x i_j / 4 := by
    rw [hr5, Function.update_of_ne (by decide), hr4, Function.update_of_ne (by decide),
      hr3, Function.update_of_ne (by decide), hr2, Function.update_self,
      hr1, Function.update_of_ne hj16, Function.update_self]
  have hadd_fit : Fits w (wRegs x5 16 + wRegs x5 17) := by
    rw [hx5_16, hx5_17]; exact htot_fit.of_le (by omega)
  obtain ⟨x6, hex6, hctx6, hm6, hr6⟩ :=
    wAdd_execWithin 17 16 17 (by omega) (by omega) (by omega) x5 hctx5 hadd_fit
  have hx6_17 : wRegs x6 17 = wRegs x i_b * numMicroPerBucket n_max + wRegs x i_j / 4 := by
    rw [hr6, Function.update_self, hx5_16, hx5_17]
  have hx6_18 : wRegs x6 18 = wRegs x i_j % 4 := by
    rw [hr6, Function.update_of_ne (by decide), hr5, Function.update_of_ne (by decide),
      hr4, Function.update_of_ne (by decide), hr3, Function.update_self,
      hr2, Function.update_of_ne hj17, Function.update_of_ne (by decide),
      hr1, Function.update_of_ne hj16, Function.update_self]
  have hx6_val : wRegs x6 i_val = wRegs x i_val := by
    rw [hr6, Function.update_of_ne hv17, hr5, Function.update_of_ne hv16,
      hr4, Function.update_of_ne hv16, hr3, Function.update_of_ne hv18,
      hr2, Function.update_of_ne hv17, hr1, Function.update_of_ne hv16]
  have hx6_k : ∀ k < 16, wRegs x6 k = wRegs x k := by
    intro k hk
    rw [hr6, Function.update_of_ne (by omega), hr5, Function.update_of_ne (by omega),
      hr4, Function.update_of_ne (by omega), hr3, Function.update_of_ne (by omega),
      hr2, Function.update_of_ne (by omega), hr1, Function.update_of_ne (by omega)]
  have hm60 : x6.mem = x.mem := by rw [hm6, hm5, hm4, hm3, hm2, hm1]
  obtain ⟨x7, hex7, hctx7, hm7, hr7⟩ :=
    wConstCode_execWithin 16 0 (by omega) x6 hctx6 (h4_fit.of_le (by omega))
  have hx7_17 : wRegs x7 17 = wRegs x6 17 := by rw [hr7, Function.update_of_ne (by decide)]
  have hx7_18 : wRegs x7 18 = wRegs x6 18 := by rw [hr7, Function.update_of_ne (by decide)]
  have hx7_16 : wRegs x7 16 = 0 := by rw [hr7, Function.update_self]
  have hx7_val : wRegs x7 i_val = wRegs x i_val := by rw [hr7, Function.update_of_ne hv16, hx6_val]
  by_cases hr0 : wRegs x i_j % 4 = 0
  · have hcond0 : (Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x7 := by
      simp only [Cond.Holds, ← wRegs_apply]
      rw [hx7_18, hx6_18, hx7_16, hr0]
    have hidx7 : wRegs x7 17 < totalMicroBuckets n_max := by rw [hx7_17, hx6_17]; exact hidx_lt
    have hval7 : wRegs x7 i_val < 2 ^ effBucketPosBits n_max := by rw [hx7_val]; exact hval_lt
    obtain ⟨y, hexy, hctxy, hry, houty, hqy, hvy, hlmy, hgmy⟩ :=
      writeLMCode_wRegs hw hnU hU hspace (by omega : c_base < 9) 17 i_val (by omega) hval
        x7 hctx7 hidx7 hval7
    have hm70 : x7.mem = x.mem := by rw [hm7, hm60]
    refine ⟨y,
      (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
        (execWithin_branch_pos hcond0 hexy)))))))).mono (by omega),
      hctxy, ?_, fun a ha => by rw [houty a ha, hm70],
      by rw [hqy, hm70], by rw [hvy, hm70],
      by rw [hlmy, hx7_17, hx6_17, hx7_val, hm70, hr0, Nat.add_zero],
      by rw [hgmy, hm70]⟩
    intro k hk
    rw [hry, hr7, Function.update_of_ne (by omega), hx6_k k hk]
  · have hcond0 : ¬(Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x7 := by
      simp only [Cond.Holds, ← wRegs_apply]
      rw [hx7_18, hx6_18, hx7_16]; exact hr0
    obtain ⟨x8, hex8, hctx8, hm8, hr8⟩ :=
      wConstCode_execWithin 16 1 (by omega) x7 hctx7 (h4_fit.of_le (by omega))
    have hx8_17 : wRegs x8 17 = wRegs x6 17 := by
      rw [hr8, Function.update_of_ne (by decide), hx7_17]
    have hx8_18 : wRegs x8 18 = wRegs x6 18 := by
      rw [hr8, Function.update_of_ne (by decide), hx7_18]
    have hx8_16 : wRegs x8 16 = 1 := by rw [hr8, Function.update_self]
    have hx8_val : wRegs x8 i_val = wRegs x i_val := by
      rw [hr8, Function.update_of_ne hv16, hx7_val]
    by_cases hr1_eq : wRegs x i_j % 4 = 1
    · have hcond1 : (Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x8 := by
        simp only [Cond.Holds, ← wRegs_apply]
        rw [hx8_18, hx6_18, hx8_16, hr1_eq]
      have hidx8 : wRegs x8 17 < totalMicroBuckets n_max := by rw [hx8_17, hx6_17]; exact hidx_lt
      have hval8 : wRegs x8 i_val < 2 ^ effBucketPosBits n_max := by rw [hx8_val]; exact hval_lt
      obtain ⟨y, hexy, hctxy, hry, houty, hqy, hvy, hlmy, hgmy⟩ :=
        writeLMCode_wRegs hw hnU hU hspace (by omega : c_base + 1 < 9) 17 i_val (by omega) hval
          x8 hctx8 hidx8 hval8
      have hm80 : x8.mem = x.mem := by rw [hm8, hm7, hm60]
      refine ⟨y,
        (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
          (execWithin_branch_neg hcond0 (hex8.seq (execWithin_branch_pos hcond1 hexy)))))))))).mono
          (by omega),
        hctxy, ?_, fun a ha => by rw [houty a ha, hm80],
        by rw [hqy, hm80], by rw [hvy, hm80],
        by rw [hlmy, hx8_17, hx6_17, hx8_val, hm80, hr1_eq],
        by rw [hgmy, hm80]⟩
      intro k hk
      rw [hry, hr8, Function.update_of_ne (by omega), hr7, Function.update_of_ne (by omega),
        hx6_k k hk]
    · have hcond1 : ¬(Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x8 := by
        simp only [Cond.Holds, ← wRegs_apply]
        rw [hx8_18, hx6_18, hx8_16]; exact hr1_eq
      obtain ⟨x9, hex9, hctx9, hm9, hr9⟩ :=
        wConstCode_execWithin 16 2 (by omega) x8 hctx8 (h4_fit.of_le (by omega))
      have hx9_17 : wRegs x9 17 = wRegs x6 17 := by
        rw [hr9, Function.update_of_ne (by decide), hx8_17]
      have hx9_18 : wRegs x9 18 = wRegs x6 18 := by
        rw [hr9, Function.update_of_ne (by decide), hx8_18]
      have hx9_16 : wRegs x9 16 = 2 := by rw [hr9, Function.update_self]
      have hx9_val : wRegs x9 i_val = wRegs x i_val := by
        rw [hr9, Function.update_of_ne hv16, hx8_val]
      by_cases hr2_eq : wRegs x i_j % 4 = 2
      · have hcond2 : (Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x9 := by
          simp only [Cond.Holds, ← wRegs_apply]
          rw [hx9_18, hx6_18, hx9_16, hr2_eq]
        have hidx9 : wRegs x9 17 < totalMicroBuckets n_max := by rw [hx9_17, hx6_17]; exact hidx_lt
        have hval9 : wRegs x9 i_val < 2 ^ effBucketPosBits n_max := by rw [hx9_val]; exact hval_lt
        obtain ⟨y, hexy, hctxy, hry, houty, hqy, hvy, hlmy, hgmy⟩ :=
          writeLMCode_wRegs hw hnU hU hspace (by omega : c_base + 2 < 9) 17 i_val (by omega) hval
            x9 hctx9 hidx9 hval9
        have hm90 : x9.mem = x.mem := by rw [hm9, hm8, hm7, hm60]
        refine ⟨y,
          (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
            (execWithin_branch_neg hcond0 (hex8.seq (execWithin_branch_neg hcond1
              (hex9.seq (execWithin_branch_pos hcond2 hexy)))))))))))).mono (by omega),
          hctxy, ?_, fun a ha => by rw [houty a ha, hm90],
          by rw [hqy, hm90], by rw [hvy, hm90],
          by rw [hlmy, hx9_17, hx6_17, hx9_val, hm90, hr2_eq],
          by rw [hgmy, hm90]⟩
        intro k hk
        rw [hry, hr9, Function.update_of_ne (by omega), hr8, Function.update_of_ne (by omega),
          hr7, Function.update_of_ne (by omega), hx6_k k hk]
      · have hr3_eq : wRegs x i_j % 4 = 3 := by omega
        have hcond2 : ¬(Cond.eq (wReg r_hash 18) (wReg r_hash 16)).Holds x9 := by
          simp only [Cond.Holds, ← wRegs_apply]
          rw [hx9_18, hx6_18, hx9_16]; exact hr2_eq
        have hidx9 : wRegs x9 17 < totalMicroBuckets n_max := by rw [hx9_17, hx6_17]; exact hidx_lt
        have hval9 : wRegs x9 i_val < 2 ^ effBucketPosBits n_max := by rw [hx9_val]; exact hval_lt
        obtain ⟨y, hexy, hctxy, hry, houty, hqy, hvy, hlmy, hgmy⟩ :=
          writeLMCode_wRegs hw hnU hU hspace (by omega : c_base + 3 < 9) 17 i_val (by omega) hval
            x9 hctx9 hidx9 hval9
        have hm90 : x9.mem = x.mem := by rw [hm9, hm8, hm7, hm60]
        refine ⟨y,
          (hex1.seq (hex2.seq (hex3.seq (hex4.seq (hex5.seq (hex6.seq (hex7.seq
            (execWithin_branch_neg hcond0 (hex8.seq (execWithin_branch_neg hcond1
              (hex9.seq (execWithin_branch_neg hcond2 hexy)))))))))))).mono (by omega),
          hctxy, ?_, fun a ha => by rw [houty a ha, hm90],
          by rw [hqy, hm90], by rw [hvy, hm90],
          by rw [hlmy, hx9_17, hx6_17, hx9_val, hm90, hr3_eq],
          by rw [hgmy, hm90]⟩
        intro k hk
        rw [hry, hr9, Function.update_of_ne (by omega), hr8, Function.update_of_ne (by omega),
          hr7, Function.update_of_ne (by omega), hx6_k k hk]


end Cslib.DataStructure.Dictionary.WordRAM.Succinct
