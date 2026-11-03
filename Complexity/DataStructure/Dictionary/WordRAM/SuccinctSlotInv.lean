/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctLayout

/-!
# Working-Register Combinators and Slab/Tail Slot-Store Invariant

This module defines the functional working-register view (`wRegs`), primitive arithmetic and
bit-packed array combinators on working registers, the `GlobalMeta` index map, and the bijection
invariants (`TailBijection`, `SlabBijection`, `SlotStoreInv`) governing physical slot allocation
in the fixed-capacity succinct dictionary.
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

/-! ### Working-register functional view (`wRegs`) and instruction combinators -/

/-- Functional view `ℕ → ℕ` of the 19 working registers `wReg r_hash 0 .. wReg r_hash 18`. -/
@[expose]
def wRegs {r_hash : ℕ} (x : Data (numRegs r_hash)) (i : ℕ) : ℕ :=
  if hi : i < 19 then x.regs (wReg r_hash i hi) else 0

@[simp]
theorem wRegs_apply {r_hash : ℕ} (x : Data (numRegs r_hash)) (i : ℕ) (hi : i < 19) :
    wRegs x i = x.regs (wReg r_hash i hi) := by
  unfold wRegs
  simp only [hi, ↓reduceDIte]

theorem wRegs_lt_of_bounded {r_hash w : ℕ} {x : Data (numRegs r_hash)}
    (hbdd : x.Bounded w) (i : ℕ) :
    wRegs x i < 2 ^ w := by
  unfold wRegs
  split_ifs with hi
  · exact hbdd.1 (wReg r_hash i hi)
  · positivity

theorem wRegs_set {r_hash : ℕ} (x : Data (numRegs r_hash)) (i : ℕ) (hi : i < 19) (v : ℕ) :
    wRegs (x.set (wReg r_hash i hi) v) = Function.update (wRegs x) i v := by
  funext j
  unfold wRegs
  by_cases hj : j = i
  · subst hj
    simp only [hi, ↓reduceDIte, Function.update_self]
    dsimp only [Data.set]
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with hj_lt
    · dsimp only [Data.set]
      rw [Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [wReg] at this; omega)]
    · rfl

/-- Machine execution invariant: word bounds hold and register `0` (`rBase`) holds `base`. -/
structure MachCtx {r_hash : ℕ} (w base : ℕ) (x : Data (numRegs r_hash)) : Prop where
  bdd : x.Bounded w
  base_reg : x.regs (rBase r_hash) = base

/-- Load constant `v` into working register `i_dst`. -/
def wConstCode (r_hash i_dst v : ℕ) (hdst : i_dst < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .op (.const (wReg r_hash i_dst hdst) v)

theorem wConstCode_execWithin {r_hash w base : ℕ} (i_dst v : ℕ) (hdst : i_dst < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x) (hfit : Fits w v) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wConstCode r_hash i_dst v hdst) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst v := by
  let y := x.set (wReg r_hash i_dst hdst) v
  have hex : ExecWithin (B := .exact) w (wConstCode r_hash i_dst v hdst) x y 1 :=
    ExecWithin.const hfit
  refine ⟨y, hex, ⟨hex.bounded hctx.bdd, ?_⟩, rfl, wRegs_set x i_dst hdst v⟩
  dsimp only [y, Data.set]
  rw [Function.update_of_ne
    (by intro h; have := congrArg Fin.val h; dsimp [rBase, wReg] at this; omega)]
  exact hctx.base_reg

/-- Copy working register `i_src` into `i_dst`. -/
def wCopyCode (r_hash i_dst i_src : ℕ)
    (hdst : i_dst < 19 := by omega) (hsrc : i_src < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .op (.copy (wReg r_hash i_dst hdst) (wReg r_hash i_src hsrc))

theorem wCopyCode_execWithin {r_hash w base : ℕ} (i_dst i_src : ℕ)
    (hdst : i_dst < 19) (hsrc : i_src < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wCopyCode r_hash i_dst i_src hdst hsrc) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst (wRegs x i_src) := by
  let y := x.set (wReg r_hash i_dst hdst) (x.regs (wReg r_hash i_src hsrc))
  have hex : ExecWithin (B := .exact) w (wCopyCode r_hash i_dst i_src hdst hsrc) x y 1 :=
    ExecWithin.copy
  refine ⟨y, hex, ⟨hex.bounded hctx.bdd, ?_⟩, rfl, ?_⟩
  · dsimp only [y, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rBase, wReg] at this; omega)]
    exact hctx.base_reg
  · change wRegs (x.set (wReg r_hash i_dst hdst) (x.regs (wReg r_hash i_src hsrc))) = _
    rw [← wRegs_apply x i_src hsrc]
    exact wRegs_set x i_dst hdst (wRegs x i_src)

/-- Exact binary operation `f` on working registers `i_a` and `i_b`, storing into `i_dst`. -/
def wBinCode (r_hash : ℕ) (f : BinOp) (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19 := by omega) (ha : i_a < 19 := by omega) (hb : i_b < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .op (.exactBin f (wReg r_hash i_dst hdst) (wReg r_hash i_a ha) (wReg r_hash i_b hb))

theorem wBinCode_execWithin {r_hash w base : ℕ} (f : BinOp) (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19) (ha : i_a < 19) (hb : i_b < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x) {v : ℕ}
    (hev : f.evalExact (wRegs x i_a) (wRegs x i_b) = some v) (hfit : Fits w v) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wBinCode r_hash f i_dst i_a i_b hdst ha hb) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst v := by
  rw [wRegs_apply x i_a ha, wRegs_apply x i_b hb] at hev
  let y := x.set (wReg r_hash i_dst hdst) v
  have hex : ExecWithin w (wBinCode r_hash f i_dst i_a i_b hdst ha hb) x y 1 :=
    (ExactLog.exec_exactBin hev hfit).within
  refine ⟨y, hex, ⟨hex.bounded hctx.bdd, ?_⟩, rfl, wRegs_set x i_dst hdst v⟩
  dsimp only [y, Data.set]
  rw [Function.update_of_ne
    (by intro h; have := congrArg Fin.val h; dsimp [rBase, wReg] at this; omega)]
  exact hctx.base_reg

theorem wAdd_execWithin {r_hash w base : ℕ} (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19) (ha : i_a < 19) (hb : i_b < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hfit : Fits w (wRegs x i_a + wRegs x i_b)) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wBinCode r_hash .add i_dst i_a i_b hdst ha hb) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst (wRegs x i_a + wRegs x i_b) :=
  wBinCode_execWithin .add i_dst i_a i_b hdst ha hb x hctx rfl hfit

theorem wSub_execWithin {r_hash w base : ℕ} (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19) (ha : i_a < 19) (hb : i_b < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hle : wRegs x i_b ≤ wRegs x i_a) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wBinCode r_hash .sub i_dst i_a i_b hdst ha hb) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst (wRegs x i_a - wRegs x i_b) := by
  have hev : BinOp.sub.evalExact (wRegs x i_a) (wRegs x i_b) =
      some (wRegs x i_a - wRegs x i_b) := by
    simp [BinOp.evalExact, hle]
  have hfit : Fits w (wRegs x i_a - wRegs x i_b) := by
    have hlt : Fits w (wRegs x i_a) := by
      rw [wRegs_apply x i_a ha]
      exact hctx.bdd.1 _
    exact hlt.of_le (Nat.sub_le _ _)
  exact wBinCode_execWithin .sub i_dst i_a i_b hdst ha hb x hctx hev hfit

theorem wMul_execWithin {r_hash w base : ℕ} (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19) (ha : i_a < 19) (hb : i_b < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hfit : Fits w (wRegs x i_a * wRegs x i_b)) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wBinCode r_hash .mul i_dst i_a i_b hdst ha hb) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst (wRegs x i_a * wRegs x i_b) :=
  wBinCode_execWithin .mul i_dst i_a i_b hdst ha hb x hctx rfl hfit

theorem wDiv_execWithin {r_hash w base : ℕ} (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19) (ha : i_a < 19) (hb : i_b < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hpos : 0 < wRegs x i_b) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wBinCode r_hash .div i_dst i_a i_b hdst ha hb) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst (wRegs x i_a / wRegs x i_b) := by
  have hne : wRegs x i_b ≠ 0 := by omega
  have hev : BinOp.div.evalExact (wRegs x i_a) (wRegs x i_b) =
      some (wRegs x i_a / wRegs x i_b) := by
    simp [BinOp.evalExact, hne]
  have hfit : Fits w (wRegs x i_a / wRegs x i_b) := by
    have hlt : Fits w (wRegs x i_a) := by
      rw [wRegs_apply x i_a ha]
      exact hctx.bdd.1 _
    exact hlt.of_le (Nat.div_le_self _ _)
  exact wBinCode_execWithin .div i_dst i_a i_b hdst ha hb x hctx hev hfit

theorem wMod_execWithin {r_hash w base : ℕ} (i_dst i_a i_b : ℕ)
    (hdst : i_dst < 19) (ha : i_a < 19) (hb : i_b < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hpos : 0 < wRegs x i_b) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (wBinCode r_hash .mod i_dst i_a i_b hdst ha hb) x y 1 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_dst (wRegs x i_a % wRegs x i_b) := by
  have hne : wRegs x i_b ≠ 0 := by omega
  have hev : BinOp.mod.evalExact (wRegs x i_a) (wRegs x i_b) =
      some (wRegs x i_a % wRegs x i_b) := by
    simp [BinOp.evalExact, hne]
  have hfit : Fits w (wRegs x i_a % wRegs x i_b) := by
    have hlt : Fits w (wRegs x i_a) := by
      rw [wRegs_apply x i_a ha]
      exact hctx.bdd.1 _
    exact hlt.of_le (Nat.mod_le _ _)
  exact wBinCode_execWithin .mod i_dst i_a i_b hdst ha hb x hctx hev hfit

theorem readGMCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < globalMetaLen n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readGMCode r_hash U V w n_max h_space i_idx i_out hidx hout) x y 38 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_out
        (gmAt base U V w n_max h_space x.mem (wRegs x i_idx)) := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  obtain ⟨y, hex, hbdd, hmem, hbase, hout', hregs'⟩ :=
    readGMCode_execWithin hw hnU hU hspace i_idx i_out hidx hout x hctx.bdd hctx.base_reg hidx_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, hmem, ?_⟩
  funext j
  by_cases hj : j = i_out
  · subst hj
    rw [wRegs_apply y j hout, Function.update_self, hout']
  · rw [Function.update_of_ne hj]
    unfold wRegs
    split_ifs with hj_lt
    · exact hregs' j hj_lt hj
    · rfl

theorem writeGMCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < globalMetaLen n_max)
    (hval_lt : wRegs x i_val < 2 ^ globalPtrBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeGMCode r_hash U V w n_max h_space i_idx i_val hidx hval) x y 49 ∧
      MachCtx w base y ∧
      wRegs y = wRegs x ∧
      (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem =
        Function.update (gmAt base U V w n_max h_space x.mem)
          (wRegs x i_idx) (wRegs x i_val) := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  rw [wRegs_apply x i_val hval] at hval_lt ⊢
  obtain ⟨y, hex, hbdd, hbase, hregs', hout, hq, hv, hlm, hgm⟩ :=
    writeGMCode_execWithin hw hnU hU hspace i_idx i_val hidx hval x
      hctx.bdd hctx.base_reg hidx_lt hval_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, ?_, hout, hq, hv, hlm, hgm⟩
  funext j
  unfold wRegs
  split_ifs with hj_lt
  · exact hregs' j hj_lt
  · rfl

theorem readQuotCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readQuotCode r_hash U w n_max h_space i_idx i_out hidx hout) x y 38 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_out
        (quotAt base U w n_max h_space x.mem (wRegs x i_idx)) := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  obtain ⟨y, hex, hbdd, hmem, hbase, hout', hregs'⟩ :=
    readQuotCode_execWithin hw hU hspace i_idx i_out hidx hout x hctx.bdd hctx.base_reg hidx_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, hmem, ?_⟩
  funext j
  by_cases hj : j = i_out
  · subst hj
    rw [wRegs_apply y j hout, Function.update_self, hout']
  · rw [Function.update_of_ne hj]
    unfold wRegs
    split_ifs with hj_lt
    · exact hregs' j hj_lt hj
    · rfl

theorem writeQuotCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < n_max)
    (hval_lt : wRegs x i_val < 2 ^ quotientBits U n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeQuotCode r_hash U w n_max h_space i_idx i_val hidx hval) x y 49 ∧
      MachCtx w base y ∧
      wRegs y = wRegs x ∧
      (∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + offVal U w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem =
        Function.update (quotAt base U w n_max h_space x.mem)
          (wRegs x i_idx) (wRegs x i_val) ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  rw [wRegs_apply x i_val hval] at hval_lt ⊢
  obtain ⟨y, hex, hbdd, hbase, hregs', hout, hq, hv, hlm, hgm⟩ :=
    writeQuotCode_execWithin hw hU hspace i_idx i_val hidx hval x
      hctx.bdd hctx.base_reg hidx_lt hval_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, ?_, hout, hq, hv, hlm, hgm⟩
  funext j
  unfold wRegs
  split_ifs with hj_lt
  · exact hregs' j hj_lt
  · rfl

theorem readValCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readValCode r_hash U V w n_max h_space i_idx i_out hidx hout) x y 38 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_out
        (valAt base U V w n_max h_space x.mem (wRegs x i_idx)) := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  obtain ⟨y, hex, hbdd, hmem, hbase, hout', hregs'⟩ :=
    readValCode_execWithin hw hV hspace i_idx i_out hidx hout x hctx.bdd hctx.base_reg hidx_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, hmem, ?_⟩
  funext j
  by_cases hj : j = i_out
  · subst hj
    rw [wRegs_apply y j hout, Function.update_self, hout']
  · rw [Function.update_of_ne hj]
    unfold wRegs
    split_ifs with hj_lt
    · exact hregs' j hj_lt hj
    · rfl

theorem writeValCode_wRegs {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < n_max)
    (hval_lt : wRegs x i_val < 2 ^ valBits V) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeValCode r_hash U V w n_max h_space i_idx i_val hidx hval) x y 49 ∧
      MachCtx w base y ∧
      wRegs y = wRegs x ∧
      (∀ a, ¬(base + offVal U w n_max h_space ≤ a ∧ a < base + offLM U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem =
        Function.update (valAt base U V w n_max h_space x.mem)
          (wRegs x i_idx) (wRegs x i_val) ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  rw [wRegs_apply x i_val hval] at hval_lt ⊢
  obtain ⟨y, hex, hbdd, hbase, hregs', hout, hq, hv, hlm, hgm⟩ :=
    writeValCode_execWithin hw hV hspace i_idx i_val hidx hval x
      hctx.bdd hctx.base_reg hidx_lt hval_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, ?_, hout, hq, hv, hlm, hgm⟩
  funext j
  unfold wRegs
  split_ifs with hj_lt
  · exact hregs' j hj_lt
  · rfl

theorem readLMCode_wRegs {r_hash w base U V n_max h_space c : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (hc : c < 9)
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < totalMicroBuckets n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readLMCode r_hash U V w n_max h_space c i_idx i_out hidx hout) x y 38 ∧
      MachCtx w base y ∧
      y.mem = x.mem ∧
      wRegs y = Function.update (wRegs x) i_out
        (lmAt base U V w n_max h_space x.mem (c, wRegs x i_idx)) := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  obtain ⟨y, hex, hbdd, hmem, hbase, hout', hregs'⟩ :=
    readLMCode_execWithin hw hnU hU hspace hc i_idx i_out hidx hout x hctx.bdd hctx.base_reg hidx_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, hmem, ?_⟩
  funext j
  by_cases hj : j = i_out
  · subst hj
    rw [wRegs_apply y j hout, Function.update_self, hout']
  · rw [Function.update_of_ne hj]
    unfold wRegs
    split_ifs with hj_lt
    · exact hregs' j hj_lt hj
    · rfl

theorem writeLMCode_wRegs {r_hash w base U V n_max h_space c : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (hc : c < 9)
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash)) (hctx : MachCtx w base x)
    (hidx_lt : wRegs x i_idx < totalMicroBuckets n_max)
    (hval_lt : wRegs x i_val < 2 ^ effBucketPosBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeLMCode r_hash U V w n_max h_space c i_idx i_val hidx hval) x y 49 ∧
      MachCtx w base y ∧
      wRegs y = wRegs x ∧
      (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem =
        Function.update (lmAt base U V w n_max h_space x.mem)
          (c, wRegs x i_idx) (wRegs x i_val) ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  rw [wRegs_apply x i_idx hidx] at hidx_lt ⊢
  rw [wRegs_apply x i_val hval] at hval_lt ⊢
  obtain ⟨y, hex, hbdd, hbase, hregs', hout, hq, hv, hlm, hgm⟩ :=
    writeLMCode_execWithin hw hnU hU hspace hc i_idx i_val hidx hval x
      hctx.bdd hctx.base_reg hidx_lt hval_lt
  refine ⟨y, hex, ⟨hbdd, hbase⟩, ?_, hout, hq, hv, hlm, hgm⟩
  funext j
  unfold wRegs
  split_ifs with hj_lt
  · exact hregs' j hj_lt
  · rfl

/-! ## Section 3: `GlobalMeta` layout, `SlotStoreInv`, and slab/tail slot operations -/

/-- `GlobalMeta` index `4 + 3 * b` holding `q_b` (number of full slabs in bucket `b`). -/
@[expose]
def gmQIdx (b : ℕ) : ℕ :=
  4 + 3 * b

/-- `GlobalMeta` index `4 + 3 * b + 1` holding `r_b` (number of tail items in bucket `b`). -/
@[expose]
def gmRIdx (b : ℕ) : ℕ :=
  4 + 3 * b + 1

/-- `GlobalMeta` index `4 + 3 * b + 2` holding `slabTop_b` (physical slab index of the top slab
`s = q_b - 1` of bucket `b`). -/
@[expose]
def gmSlabTopIdx (b : ℕ) : ℕ :=
  4 + 3 * b + 2

/-- Base index `4 + 3 * numBuckets n_max` of the `slabDir` table in `GlobalMeta`. -/
@[expose]
def gmSlabDirBase (n_max : ℕ) : ℕ :=
  4 + 3 * numBuckets n_max

/-- `GlobalMeta` index of `slabDir(b, s)` (`s < dirSlabsPerBucket n_max`). -/
@[expose]
def gmSlabDirIdx (n_max b s : ℕ) : ℕ :=
  gmSlabDirBase n_max + b * dirSlabsPerBucket n_max + s

/-- Base index of the `tailPtr` table in `GlobalMeta`. -/
@[expose]
def gmTailPtrBase (n_max : ℕ) : ℕ :=
  gmSlabDirBase n_max + numBuckets n_max * dirSlabsPerBucket n_max

/-- `GlobalMeta` index of flat tail descriptor `d < maxTailItems n_max`. -/
@[expose]
def gmTailPtrFlatIdx (n_max d : ℕ) : ℕ :=
  gmTailPtrBase n_max + d

/-- `GlobalMeta` index of `tailPtr(b, r)` (`r < tailCapPerBucket n_max`). -/
@[expose]
def gmTailPtrIdx (n_max b r : ℕ) : ℕ :=
  gmTailPtrFlatIdx n_max (b * tailCapPerBucket n_max + r)

/-- Base index of the `tailOwner` table in `GlobalMeta`. -/
@[expose]
def gmTailOwnerBase (n_max : ℕ) : ℕ :=
  gmTailPtrBase n_max + maxTailItems n_max

/-- `GlobalMeta` index of `tailOwner(t)` (`t < maxTailItems n_max`). -/
@[expose]
def gmTailOwnerIdx (n_max t : ℕ) : ℕ :=
  gmTailOwnerBase n_max + t

/-- Base index of the per-physical-slab metadata table in `GlobalMeta`. -/
@[expose]
def gmSlabMetaBase (n_max : ℕ) : ℕ :=
  gmTailOwnerBase n_max + maxTailItems n_max

/-- `GlobalMeta` index of `slabOwnerB(p)` (`p < maxFullSlabs n_max`). -/
@[expose]
def gmSlabOwnerBIdx (n_max p : ℕ) : ℕ :=
  gmSlabMetaBase n_max + 4 * p

/-- `GlobalMeta` index of `slabOwnerS(p)` (`p < maxFullSlabs n_max`). -/
@[expose]
def gmSlabOwnerSIdx (n_max p : ℕ) : ℕ :=
  gmSlabMetaBase n_max + 4 * p + 1

/-- `GlobalMeta` index of `slabBelow(p)` (`p < maxFullSlabs n_max`). -/
@[expose]
def gmSlabBelowIdx (n_max p : ℕ) : ℕ :=
  gmSlabMetaBase n_max + 4 * p + 2

/-- `GlobalMeta` index of `slabAbove(p)` (`p < maxFullSlabs n_max`). -/
@[expose]
def gmSlabAboveIdx (n_max p : ℕ) : ℕ :=
  gmSlabMetaBase n_max + 4 * p + 3

theorem gmSlabMetaBase_add_eq_globalMetaLen {n_max : ℕ} (hb : 0 < bucketBits n_max) :
    gmSlabMetaBase n_max + 4 * maxFullSlabs n_max = globalMetaLen n_max := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  unfold globalMetaLen globalMetaVarLen gmSlabMetaBase gmTailOwnerBase gmTailPtrBase
    gmSlabDirBase maxTailItems
  rw [ite_eq_right hb0]
  ring

theorem gmQIdx_lt {n_max b : ℕ} (hb : 0 < bucketBits n_max) (hb_lt : b < numBuckets n_max) :
    gmQIdx b < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmQIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  omega

theorem gmRIdx_lt {n_max b : ℕ} (hb : 0 < bucketBits n_max) (hb_lt : b < numBuckets n_max) :
    gmRIdx b < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmRIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  omega

theorem gmSlabTopIdx_lt {n_max b : ℕ} (hb : 0 < bucketBits n_max) (hb_lt : b < numBuckets n_max) :
    gmSlabTopIdx b < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabTopIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  omega

theorem gmSlabDirIdx_lt {n_max b s : ℕ} (hb : 0 < bucketBits n_max)
    (hb_lt : b < numBuckets n_max) (hs_lt : s < dirSlabsPerBucket n_max) :
    gmSlabDirIdx n_max b s < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  have hmul : b * dirSlabsPerBucket n_max + s < numBuckets n_max * dirSlabsPerBucket n_max := by
    have h1 : (b + 1) * dirSlabsPerBucket n_max ≤ numBuckets n_max * dirSlabsPerBucket n_max :=
      Nat.mul_le_mul_right _ hb_lt
    nlinarith
  unfold gmSlabDirIdx gmSlabMetaBase gmTailOwnerBase gmTailPtrBase
  omega

theorem gmTailPtrFlatIdx_lt {n_max d : ℕ} (hb : 0 < bucketBits n_max)
    (hd_lt : d < maxTailItems n_max) :
    gmTailPtrFlatIdx n_max d < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmTailPtrFlatIdx gmSlabMetaBase gmTailOwnerBase
  omega

theorem gmTailPtrIdx_lt {n_max b r : ℕ} (hb : 0 < bucketBits n_max)
    (hb_lt : b < numBuckets n_max) (hr_lt : r < tailCapPerBucket n_max) :
    gmTailPtrIdx n_max b r < globalMetaLen n_max := by
  apply gmTailPtrFlatIdx_lt hb
  unfold maxTailItems
  have h1 : (b + 1) * tailCapPerBucket n_max ≤ numBuckets n_max * tailCapPerBucket n_max :=
    Nat.mul_le_mul_right _ hb_lt
  nlinarith

theorem gmTailOwnerIdx_lt {n_max t : ℕ} (hb : 0 < bucketBits n_max)
    (ht_lt : t < maxTailItems n_max) :
    gmTailOwnerIdx n_max t < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmTailOwnerIdx gmSlabMetaBase
  omega

theorem gmSlabOwnerBIdx_lt {n_max p : ℕ} (hb : 0 < bucketBits n_max)
    (hp_lt : p < maxFullSlabs n_max) :
    gmSlabOwnerBIdx n_max p < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabOwnerBIdx
  omega

theorem gmSlabOwnerSIdx_lt {n_max p : ℕ} (hb : 0 < bucketBits n_max)
    (hp_lt : p < maxFullSlabs n_max) :
    gmSlabOwnerSIdx n_max p < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabOwnerSIdx
  omega

theorem gmSlabBelowIdx_lt {n_max p : ℕ} (hb : 0 < bucketBits n_max)
    (hp_lt : p < maxFullSlabs n_max) :
    gmSlabBelowIdx n_max p < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabBelowIdx
  omega

theorem gmSlabAboveIdx_lt {n_max p : ℕ} (hb : 0 < bucketBits n_max)
    (hp_lt : p < maxFullSlabs n_max) :
    gmSlabAboveIdx n_max p < globalMetaLen n_max := by
  rw [← gmSlabMetaBase_add_eq_globalMetaLen hb]
  unfold gmSlabAboveIdx
  omega

/-- Number of items currently stored in bucket `b` according to `gm : ℕ → ℕ`. -/
@[expose]
def bCount (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ :=
  if bucketBits n_max = 0 then
    if b = 0 then gm 0 else 0
  else
    if b < numBuckets n_max then gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b) else 0

/-- Physical slab `p < gm 0` owned by `(b, s)` in `gm`. -/
@[expose]
def slabPtrOf (n_max : ℕ) (gm : ℕ → ℕ) (b s : ℕ) : ℕ :=
  ((List.range (gm 0)).find? (fun p =>
    decide (gm (gmSlabOwnerBIdx n_max p) = b ∧ gm (gmSlabOwnerSIdx n_max p) = s))).getD 0

theorem slabPtrOf_congr {n_max : ℕ} {gm₁ gm₂ : ℕ → ℕ}
    (h0 : gm₁ 0 = gm₂ 0)
    (hB : ∀ p < gm₁ 0, gm₁ (gmSlabOwnerBIdx n_max p) = gm₂ (gmSlabOwnerBIdx n_max p))
    (hS : ∀ p < gm₁ 0, gm₁ (gmSlabOwnerSIdx n_max p) = gm₂ (gmSlabOwnerSIdx n_max p))
    (b s : ℕ) :
    slabPtrOf n_max gm₁ b s = slabPtrOf n_max gm₂ b s := by
  unfold slabPtrOf
  rw [← h0]
  congr 1
  apply List.find?_congr
  intro p hp
  rw [List.mem_range] at hp
  rw [hB p hp, hS p hp]

theorem slabPtrOf_eq_of_owner {n_max : ℕ} {gm : ℕ → ℕ} {b s p : ℕ}
    (hp : p < gm 0)
    (hB : gm (gmSlabOwnerBIdx n_max p) = b)
    (hS : gm (gmSlabOwnerSIdx n_max p) = s)
    (hinj : ∀ p₁ < gm 0, ∀ p₂ < gm 0,
      gm (gmSlabOwnerBIdx n_max p₁) = gm (gmSlabOwnerBIdx n_max p₂) →
      gm (gmSlabOwnerSIdx n_max p₁) = gm (gmSlabOwnerSIdx n_max p₂) → p₁ = p₂) :
    slabPtrOf n_max gm b s = p := by
  unfold slabPtrOf
  have hex : ∃ q ∈ List.range (gm 0),
      decide (gm (gmSlabOwnerBIdx n_max q) = b ∧ gm (gmSlabOwnerSIdx n_max q) = s) = true :=
    ⟨p, List.mem_range.mpr hp, decide_eq_true ⟨hB, hS⟩⟩
  obtain ⟨q, hfind⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex)
  rw [hfind, Option.getD_some]
  have hq_mem : q < gm 0 := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
  have hq_pred : gm (gmSlabOwnerBIdx n_max q) = b ∧ gm (gmSlabOwnerSIdx n_max q) = s :=
    of_decide_eq_true (by simpa using List.find?_some hfind)
  exact hinj q hq_mem p hp (hq_pred.1.trans hB.symm) (hq_pred.2.trans hS.symm)

/-- Physical slot `g < n_max` of logical bucket index `j` in bucket `b`.
Within full slabs, intra-slab offsets are reversed (`slabSize n_max - 1 - j % slabSize n_max`)
so that the `K`-step slab promotion and demotion loops preserve disjointness of active slab and
tail slots at every intermediate step even when `gm 0 * slabSize n_max + gm 1 = n_max`. -/
@[expose]
def slotOf (n_max : ℕ) (gm : ℕ → ℕ) (b j : ℕ) : ℕ :=
  if bucketBits n_max = 0 then j
  else if j < gm (gmQIdx b) * slabSize n_max then
    slabPtrOf n_max gm b (j / slabSize n_max) * slabSize n_max +
      (slabSize n_max - 1 - j % slabSize n_max)
  else
    n_max - 1 - gm (gmTailPtrIdx n_max b (j - gm (gmQIdx b) * slabSize n_max))

/-- Flat 1-D bijection between active tail descriptors `d = b * tailCapPerBucket n_max + r`
(`b < numBuckets n_max`, `r < r_fn b`) and physical tail offsets `0 .. n_tails - 1`. -/
structure TailBijection (n_max : ℕ) (gm : ℕ → ℕ) (r_fn : ℕ → ℕ) (n_tails : ℕ) : Prop where
  ntails_eq : gm 1 = n_tails
  ntails_le : n_tails ≤ maxTailItems n_max
  r_le : ∀ b < numBuckets n_max, r_fn b ≤ tailCapPerBucket n_max
  ptr_lt : ∀ b < numBuckets n_max, ∀ r < r_fn b,
    gm (gmTailPtrIdx n_max b r) < n_tails
  owner_ptr : ∀ b < numBuckets n_max, ∀ r < r_fn b,
    gm (gmTailOwnerIdx n_max (gm (gmTailPtrIdx n_max b r))) =
      b * tailCapPerBucket n_max + r
  owner_valid : ∀ t < n_tails,
    let d := gm (gmTailOwnerIdx n_max t)
    d / tailCapPerBucket n_max < numBuckets n_max ∧
    d % tailCapPerBucket n_max < r_fn (d / tailCapPerBucket n_max) ∧
    gm (gmTailPtrFlatIdx n_max d) = t

/-- Pointwise algebraic bijection between active logical slabs `(b, s)` (`b < numBuckets n_max`,
`s < q_fn b`) and physical slabs `0 .. n_slabs - 1`. -/
structure SlabBijection (n_max : ℕ) (gm : ℕ → ℕ) (q_fn : ℕ → ℕ) (n_slabs : ℕ) : Prop where
  nslabs_eq : gm 0 = n_slabs
  nslabs_le : n_slabs ≤ maxFullSlabs n_max
  ptr_lt : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    slabPtrOf n_max gm b s < n_slabs
  ownerB_ptr : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    gm (gmSlabOwnerBIdx n_max (slabPtrOf n_max gm b s)) = b
  ownerS_ptr : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    gm (gmSlabOwnerSIdx n_max (slabPtrOf n_max gm b s)) = s
  owner_valid : ∀ p < n_slabs,
    let b := gm (gmSlabOwnerBIdx n_max p)
    let s := gm (gmSlabOwnerSIdx n_max p)
    b < numBuckets n_max ∧ s < q_fn b ∧ slabPtrOf n_max gm b s = p
  dir_eq : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    s < dirSlabsPerBucket n_max → gm (gmSlabDirIdx n_max b s) = slabPtrOf n_max gm b s
  top_eq : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    s + 1 = q_fn b → gm (gmSlabTopIdx b) = slabPtrOf n_max gm b s
  below_eq : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    0 < s → gm (gmSlabBelowIdx n_max (slabPtrOf n_max gm b s)) = slabPtrOf n_max gm b (s - 1)
  above_eq : ∀ b < numBuckets n_max, ∀ s < q_fn b,
    s + 1 < q_fn b → gm (gmSlabAboveIdx n_max (slabPtrOf n_max gm b s)) =
      slabPtrOf n_max gm b (s + 1)

/-- Full invariant of the slab/tail slot store in `GlobalMeta`. -/
structure SlotStoreInv (n_max : ℕ) (gm : ℕ → ℕ) : Prop where
  single_valid : bucketBits n_max = 0 → gm 0 ≤ n_max
  multi_tail : 0 < bucketBits n_max →
    TailBijection n_max gm (fun b => gm (gmRIdx b)) (gm 1)
  multi_slab : 0 < bucketBits n_max →
    SlabBijection n_max gm (fun b => gm (gmQIdx b)) (gm 0)
  multi_r_bounds : 0 < bucketBits n_max →
    ∀ b < numBuckets n_max,
      gm (gmRIdx b) < tailCapPerBucket n_max ∧
      (0 < gm (gmQIdx b) → 1 ≤ gm (gmRIdx b))
  multi_total_le : 0 < bucketBits n_max →
    gm 0 * slabSize n_max + gm 1 ≤ n_max

/-- Potential function `∑_{b < numBuckets n_max} |r_b - K|` controlling amortized slab promotions
and demotions (`0` in the single-bucket regime). -/
@[expose]
def slotPotential (n_max : ℕ) (gm : ℕ → ℕ) : ℕ :=
  if bucketBits n_max = 0 then 0
  else
    ∑ b ∈ Finset.range (numBuckets n_max),
      bucketPotential (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))

/-- An all-zero `GlobalMeta` array satisfies `SlotStoreInv` with `bCount = 0` and
`slotPotential = 0`. -/
theorem slotStoreInv_of_zero (n_max : ℕ) {gm : ℕ → ℕ} (hzero : ∀ i, gm i = 0) :
    SlotStoreInv n_max gm ∧
      (∀ b, bCount n_max gm b = 0) ∧
      slotPotential n_max gm = 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro _; rw [hzero 0]; exact Nat.zero_le n_max
  · intro hb
    refine ⟨rfl, by rw [hzero 1]; exact Nat.zero_le _, ?_, ?_, ?_, ?_⟩
    · intro b _; rw [hzero]; exact Nat.zero_le _
    · intro b _ r hr; rw [hzero] at hr; omega
    · intro b _ r hr; rw [hzero] at hr; omega
    · intro t ht; rw [hzero 1] at ht; omega
  · intro hb
    refine ⟨rfl, by rw [hzero 0]; exact Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b _ s hs; rw [hzero] at hs; omega
    · intro b _ s hs; rw [hzero] at hs; omega
    · intro b _ s hs; rw [hzero] at hs; omega
    · intro p hp; rw [hzero 0] at hp; omega
    · intro b _ s hs; rw [hzero] at hs; omega
    · intro b _ s hs; rw [hzero] at hs; omega
    · intro b _ s hs; rw [hzero] at hs; omega
    · intro b _ s hs; rw [hzero] at hs; omega
  · intro hb b _
    rw [hzero, hzero]
    have hK := slabSize_pos n_max
    have hb0 : bucketBits n_max ≠ 0 := by omega
    refine ⟨?_, by omega⟩
    unfold tailCapPerBucket
    rw [ite_eq_right hb0]
    omega
  · intro _; rw [hzero 0, hzero 1]; simp
  · intro b
    unfold bCount
    split_ifs <;> simp [hzero]
  · unfold slotPotential
    split_ifs
    · rfl
    · apply Finset.sum_eq_zero
      intro b _
      simp [hzero, bucketPotential]

/-- Key slot-store theorem: under `SlotStoreInv n_max gm`, every logical slot `(b, j)` with
`b < numBuckets n_max` and `j < bCount n_max gm b` maps to a valid physical slot
`slotOf n_max gm b j < n_max`, and `slotOf n_max gm` is injective across all active `(b, j)`. -/
theorem slotOf_lt_and_injective {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm) :
    (∀ b < numBuckets n_max, ∀ j < bCount n_max gm b, slotOf n_max gm b j < n_max) ∧
    (∀ b₁ < numBuckets n_max, ∀ j₁ < bCount n_max gm b₁,
      ∀ b₂ < numBuckets n_max, ∀ j₂ < bCount n_max gm b₂,
      slotOf n_max gm b₁ j₁ = slotOf n_max gm b₂ j₂ → b₁ = b₂ ∧ j₁ = j₂) := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · have hB1 : numBuckets n_max = 1 := by simp [numBuckets, hb0]
    have hc0 : gm 0 ≤ n_max := hinv.single_valid hb0
    refine ⟨?_, ?_⟩
    · intro b hb j hj
      have hb_eq : b = 0 := by omega
      subst hb_eq
      unfold bCount at hj
      simp only [hb0, ↓reduceIte] at hj
      unfold slotOf
      simp only [hb0, ↓reduceIte]
      omega
    · intro b₁ hb₁ j₁ _ b₂ hb₂ j₂ _ heq
      have hb1 : b₁ = 0 := by omega
      have hb2 : b₂ = 0 := by omega
      unfold slotOf at heq
      simp only [hb0, ↓reduceIte] at heq
      exact ⟨by omega, heq⟩
  · have hb_ne : bucketBits n_max ≠ 0 := by omega
    have htail := hinv.multi_tail hb_pos
    have hslab := hinv.multi_slab hb_pos
    have htot := hinv.multi_total_le hb_pos
    have hK : 0 < slabSize n_max := slabSize_pos n_max
    have hTcap : 0 < tailCapPerBucket n_max := by
      unfold tailCapPerBucket
      rw [ite_eq_right hb_ne]
      omega
    have hslot_dichot : ∀ b < numBuckets n_max, ∀ j < bCount n_max gm b,
        (j < gm (gmQIdx b) * slabSize n_max ∧
          slotOf n_max gm b j < gm 0 * slabSize n_max) ∨
        (gm (gmQIdx b) * slabSize n_max ≤ j ∧
          gm 0 * slabSize n_max ≤ slotOf n_max gm b j ∧
          slotOf n_max gm b j < n_max) := by
      intro b hb j hj
      unfold bCount at hj
      simp only [hb_ne, ↓reduceIte, hb] at hj
      unfold slotOf
      simp only [hb_ne, ↓reduceIte]
      split_ifs with hj_slab
      · left
        have hs_lt : j / slabSize n_max < gm (gmQIdx b) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hp_lt : slabPtrOf n_max gm b (j / slabSize n_max) < gm 0 := by
          rw [hslab.nslabs_eq]
          exact hslab.ptr_lt b hb _ hs_lt
        have hmod_lt : j % slabSize n_max < slabSize n_max := Nat.mod_lt j hK
        refine ⟨hj_slab, ?_⟩
        have h1 : (slabPtrOf n_max gm b (j / slabSize n_max) + 1) * slabSize n_max ≤
            gm 0 * slabSize n_max :=
          Nat.mul_le_mul_right _ hp_lt
        rw [Nat.add_one_mul] at h1
        omega
      · right
        have hj_ge : gm (gmQIdx b) * slabSize n_max ≤ j := by omega
        have hr_lt : j - gm (gmQIdx b) * slabSize n_max < gm (gmRIdx b) := by omega
        have ht_lt : gm (gmTailPtrIdx n_max b (j - gm (gmQIdx b) * slabSize n_max)) < gm 1 := by
          rw [htail.ntails_eq]
          exact htail.ptr_lt b hb _ hr_lt
        refine ⟨hj_ge, by omega, by omega⟩
    refine ⟨?_, ?_⟩
    · intro b hb j hj
      rcases hslot_dichot b hb j hj with ⟨_, hlt⟩ | ⟨_, _, hlt⟩
      · omega
      · exact hlt
    · intro b₁ hb₁ j₁ hj₁ b₂ hb₂ j₂ hj₂ heq
      rcases hslot_dichot b₁ hb₁ j₁ hj₁ with ⟨hj1_lt, hs1_lt⟩ | ⟨hj1_ge, hs1_ge, _⟩ <;>
      rcases hslot_dichot b₂ hb₂ j₂ hj₂ with ⟨hj2_lt, hs2_lt⟩ | ⟨hj2_ge, hs2_ge, _⟩
      · -- Both in slabs
        unfold slotOf at heq
        simp only [hb_ne, ↓reduceIte, hj1_lt, hj2_lt] at heq
        have hmod1 : j₁ % slabSize n_max < slabSize n_max := Nat.mod_lt j₁ hK
        have hmod2 : j₂ % slabSize n_max < slabSize n_max := Nat.mod_lt j₂ hK
        have hp_eq : slabPtrOf n_max gm b₁ (j₁ / slabSize n_max) =
            slabPtrOf n_max gm b₂ (j₂ / slabSize n_max) := by
          rcases lt_trichotomy (slabPtrOf n_max gm b₁ (j₁ / slabSize n_max))
              (slabPtrOf n_max gm b₂ (j₂ / slabSize n_max)) with hlt | hlt | hlt
          · have := Nat.mul_le_mul_right (slabSize n_max) hlt
            rw [Nat.add_one_mul] at this; omega
          · exact hlt
          · have := Nat.mul_le_mul_right (slabSize n_max) hlt
            rw [Nat.add_one_mul] at this; omega
        have hrem_eq : j₁ % slabSize n_max = j₂ % slabSize n_max := by
          rw [hp_eq] at heq
          omega
        have hs1_q : j₁ / slabSize n_max < gm (gmQIdx b₁) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hs2_q : j₂ / slabSize n_max < gm (gmQIdx b₂) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hb_eq : b₁ = b₂ := by
          rw [← hslab.ownerB_ptr b₁ hb₁ _ hs1_q, hp_eq, hslab.ownerB_ptr b₂ hb₂ _ hs2_q]
        have hs_eq : j₁ / slabSize n_max = j₂ / slabSize n_max := by
          rw [← hslab.ownerS_ptr b₁ hb₁ _ hs1_q, hp_eq, hslab.ownerS_ptr b₂ hb₂ _ hs2_q]
        refine ⟨hb_eq, ?_⟩
        rw [← Nat.div_add_mod j₁ (slabSize n_max), ← Nat.div_add_mod j₂ (slabSize n_max),
          hs_eq, hrem_eq]
      · omega
      · omega
      · -- Both in tails
        have hnot1 : ¬(j₁ < gm (gmQIdx b₁) * slabSize n_max) := by omega
        have hnot2 : ¬(j₂ < gm (gmQIdx b₂) * slabSize n_max) := by omega
        unfold slotOf at heq
        simp only [hb_ne, ↓reduceIte, hnot1, hnot2] at heq
        unfold bCount at hj₁ hj₂
        simp only [hb_ne, ↓reduceIte, hb₁, hb₂] at hj₁ hj₂
        have hr1_lt : j₁ - gm (gmQIdx b₁) * slabSize n_max < gm (gmRIdx b₁) := by omega
        have hr2_lt : j₂ - gm (gmQIdx b₂) * slabSize n_max < gm (gmRIdx b₂) := by omega
        have ht1_lt : gm (gmTailPtrIdx n_max b₁ (j₁ - gm (gmQIdx b₁) * slabSize n_max)) < gm 1 := by
          rw [htail.ntails_eq]
          exact htail.ptr_lt b₁ hb₁ _ hr1_lt
        have ht2_lt : gm (gmTailPtrIdx n_max b₂ (j₂ - gm (gmQIdx b₂) * slabSize n_max)) < gm 1 := by
          rw [htail.ntails_eq]
          exact htail.ptr_lt b₂ hb₂ _ hr2_lt
        have ht_eq : gm (gmTailPtrIdx n_max b₁ (j₁ - gm (gmQIdx b₁) * slabSize n_max)) =
            gm (gmTailPtrIdx n_max b₂ (j₂ - gm (gmQIdx b₂) * slabSize n_max)) := by omega
        have hown := congrArg (gm ∘ gmTailOwnerIdx n_max) ht_eq
        dsimp only [Function.comp_apply] at hown
        rw [htail.owner_ptr b₁ hb₁ _ hr1_lt, htail.owner_ptr b₂ hb₂ _ hr2_lt] at hown
        have hr1_cap : j₁ - gm (gmQIdx b₁) * slabSize n_max < tailCapPerBucket n_max :=
          lt_of_lt_of_le hr1_lt (htail.r_le b₁ hb₁)
        have hr2_cap : j₂ - gm (gmQIdx b₂) * slabSize n_max < tailCapPerBucket n_max :=
          lt_of_lt_of_le hr2_lt (htail.r_le b₂ hb₂)
        have hb_eq : b₁ = b₂ := by
          rcases lt_trichotomy b₁ b₂ with hlt | hlt | hlt
          · have := Nat.mul_le_mul_right (tailCapPerBucket n_max) hlt
            rw [Nat.add_one_mul] at this; omega
          · exact hlt
          · have := Nat.mul_le_mul_right (tailCapPerBucket n_max) hlt
            rw [Nat.add_one_mul] at this; omega
        subst hb_eq
        have hr_eq : j₁ - gm (gmQIdx b₁) * slabSize n_max =
            j₂ - gm (gmQIdx b₁) * slabSize n_max := by omega
        exact ⟨rfl, by omega⟩


end Cslib.DataStructure.Dictionary.WordRAM.Succinct
