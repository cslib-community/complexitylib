/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.LeafStep
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Clear
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Weight
public import Complexity.Computability.WordRAM.Heap

/-!
# Memory and register invariants for actual controller nodes

## Main definitions

* `PrunedQuery.KernelRegs`: the unchanged native parameters and computed workspace pointers.
* `PrunedQuery.nodeWrites`: the descendant rows that one node may change.

## Main results

* `PrunedQuery.exec_node_zero`: the terminal node case, with the existing mathematical result,
  concrete frame and timestamp preservation, and charged native continuation.

The invariants describe ordinary register and memory values. They contain no execution,
solver, time-bound or all-state-fit field. Execution is proved separately in native semantics.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Fixed caller parameters and the explicit workspace partition computed by `locate`.
This is a register-value assertion, with no assumed execution or resource guarantee. -/
structure KernelRegs (L f a b : ℕ) (x : Data registers) : Prop where
  /-- Original recursion depth. -/
  depth_eq : x.regs inputDepth = L
  /-- Actual source-array and row capacity. -/
  span_eq : x.regs span = 10 ^ L
  /-- Left input-array pointer. -/
  left_eq : x.regs arrayA = a
  /-- Right input-array pointer. -/
  right_eq : x.regs arrayB = b
  /-- First stored frame. -/
  frames_eq : x.regs frames = f
  /-- First query row, after the four-word frames. -/
  lists_eq : x.regs lists = f + 4 * (L + 1)
  /-- First value row, after all query rows. -/
  values_eq : x.regs values = f + 4 * (L + 1) + (L + 1) * 10 ^ L
  /-- Shared timestamp directory, after all value rows. -/
  stamps_eq : x.regs stamps = f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L
  /-- Constant zero. -/
  nil_eq : x.regs nil = 0
  /-- Constant one. -/
  one_eq : x.regs one = 1
  /-- Constant ten. -/
  ten_eq : x.regs ten = 10
  /-- Constant inner-output digit. -/
  nine_eq : x.regs nine = 9
  /-- Four ordinary words per frame. -/
  frameWidth_eq : x.regs frameWidth = 4

/-- The exact permitted workspace rows for a node at depth `d`. Its own query row is read-only;
descendant query rows, current/descendant value rows, frame suffix and timestamps may change. -/
def nodeWrites (L f d : ℕ) : Finset ℕ :=
  (Block.mk (f + 4 * d) (4 * (L + 1 - d))).footprint ∪
  (Block.mk (f + 4 * (L + 1) + (d + 1) * 10 ^ L) ((L - d) * 10 ^ L)).footprint ∪
  (Block.mk (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L)
    ((L + 1 - d) * 10 ^ L)).footprint ∪
  (Block.mk (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) (10 ^ L)).footprint

private theorem KernelRegs.of_leafStep {L f a b : ℕ} {x y : Data registers}
    (h : KernelRegs L f a b x)
    (hy : ∀ i, ¬LeafStepLocal i → y.regs i = x.regs i) : KernelRegs L f a b y := by
  constructor
  · exact (hy inputDepth (by decide)).trans h.depth_eq
  · exact (hy span (by decide)).trans h.span_eq
  · exact (hy arrayA (by decide)).trans h.left_eq
  · exact (hy arrayB (by decide)).trans h.right_eq
  · exact (hy frames (by decide)).trans h.frames_eq
  · exact (hy lists (by decide)).trans h.lists_eq
  · exact (hy values (by decide)).trans h.values_eq
  · exact (hy stamps (by decide)).trans h.stamps_eq
  · exact (hy nil (by decide)).trans h.nil_eq
  · exact (hy one (by decide)).trans h.one_eq
  · exact (hy ten (by decide)).trans h.ten_eq
  · exact (hy nine (by decide)).trans h.nine_eq
  · exact (hy frameWidth (by decide)).trans h.frameWidth_eq

/-- Every branch of the actual controller preserves the fixed caller parameters. -/
theorem KernelRegs.of_step {w T L f a b : ℕ} {x y : Data registers}
    (h : KernelRegs L f a b x) (he : ExecWithin w step x y T) : KernelRegs L f a b y := by
  constructor
  · exact (he.regs_eq (by decide : step.Preserves inputDepth)).trans h.depth_eq
  · exact (he.regs_eq (by decide : step.Preserves span)).trans h.span_eq
  · exact (he.regs_eq (by decide : step.Preserves arrayA)).trans h.left_eq
  · exact (he.regs_eq (by decide : step.Preserves arrayB)).trans h.right_eq
  · exact (he.regs_eq (by decide : step.Preserves frames)).trans h.frames_eq
  · exact (he.regs_eq (by decide : step.Preserves lists)).trans h.lists_eq
  · exact (he.regs_eq (by decide : step.Preserves values)).trans h.values_eq
  · exact (he.regs_eq (by decide : step.Preserves stamps)).trans h.stamps_eq
  · exact (he.regs_eq (by decide : step.Preserves nil)).trans h.nil_eq
  · exact (he.regs_eq (by decide : step.Preserves one)).trans h.one_eq
  · exact (he.regs_eq (by decide : step.Preserves ten)).trans h.ten_eq
  · exact (he.regs_eq (by decide : step.Preserves nine)).trans h.nine_eq
  · exact (he.regs_eq (by decide : step.Preserves frameWidth)).trans h.frameWidth_eq

/-- The terminal induction case is a proved actual controller iteration. The requested values
are the existing `Pruned.result`; an empty set leaves the value row untouched. The memory
frame and timestamp bound hold at the same final state as the charged continuation. -/
theorem exec_node_zero {w L f a0 b0 p E : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hab : GenericRAM.Signed.Fits w (a * b))
    (S : Finset (OutStr 0)) (x : Data registers) (hregs : KernelRegs L f a0 b0 x)
    (hd : x.regs level = L) (hm : x.regs mode = 0) (hactive : x.regs active = 1)
    (hcount : x.mem (f + 4 * L) = S.card) (hpref : x.mem (f + 4 * L + 1) = p)
    (hleft : x.mem (a0 + p) = encode a) (hright : x.mem (b0 + p) = encode b)
    (hE : x.regs epoch = E)
    (hmarks : ∀ q < 10 ^ L,
      x.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ E)
    (hw : Fits (w + 2) (f + 4 * (L + 1) + (f + 4 * (L + 1)) +
      (f + 4 * (L + 1) + (L + 1) * 10 ^ L) + (L + 1) * 10 ^ L + L +
      a0 + p + b0 + p + 12)) :
    ∃ y, KernelRegs L f a0 b0 y ∧
      y.regs level = (if L = 0 then 0 else L - 1) ∧
      y.regs mode = (if L = 0 then 0 else 2) ∧
      y.regs active = (if L = 0 then 0 else 1) ∧ y.regs epoch = E ∧
      (∀ q < 10 ^ L,
        y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ E) ∧
      (∀ q ∈ S, y.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + L * 10 ^ L +
        (queryIndex q).val) = encode (Pruned.result 0 (fun _ => a) (fun _ => b) S q)) ∧
      Modifies (nodeWrites L f L) x.mem y.mem ∧
      (∀ i, ¬LeafStepLocal i → y.regs i = x.regs i) ∧
      ∀ z U, ExecWithin (w + 2) controller y z U →
        ExecWithin (w + 2) controller x z (traceWeight S + U) := by
  obtain ⟨y, hmem, hyl, hym, hya, hreg, hrun⟩ := exec_controller_leaf ha hb hab x
    hregs.nil_eq hregs.one_eq hregs.frameWidth_eq hm (hd.trans hregs.depth_eq.symm)
    hactive
    (by simpa only [hregs.frames_eq, hd] using hpref)
    (by simpa only [hregs.left_eq] using hleft)
    (by simpa only [hregs.right_eq] using hright)
    (by simpa only [hregs.frames_eq, hregs.lists_eq, hregs.values_eq, hregs.span_eq,
      hregs.left_eq, hregs.right_eq, hd] using hw)
  have hm' : y.mem = if S.card = 0 then x.mem else
      Function.update x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + L * 10 ^ L)
        (encode (a * b)) := by
    simpa only [hregs.frames_eq, hd, hcount, hregs.values_eq, hregs.span_eq] using hmem
  have hpow : 0 < (10 : ℕ) ^ L := by positivity
  have haway (q : ℕ) : f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q ≠
      f + 4 * (L + 1) + (L + 1) * 10 ^ L + L * 10 ^ L := by nlinarith
  refine ⟨y, hregs.of_leafStep hreg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hreg, ?_⟩
  · simpa only [hd] using hyl
  · simpa only [hd] using hym
  · simpa only [hd] using hya
  · exact (hreg epoch (by decide)).trans hE
  · intro q hq
    rw [hm']
    split_ifs
    · exact hmarks q hq
    · rw [Function.update_of_ne (haway q)]
      exact hmarks q hq
  · intro q hq
    have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr ⟨q, hq⟩
    have hq0 : (queryIndex q).val = 0 := by have := (queryIndex q).isLt; omega
    simp only [hm', hc, ↓reduceIte, hq0, Nat.add_zero, Function.update_self,
      Pruned.result, Pruned.run, Finset.piecewise, hq]
  · intro c hc
    rw [hm']
    split_ifs
    · rfl
    · apply Function.update_of_ne
      intro he
      apply hc
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [Block.mem_footprint]
      change _ ≤ c ∧ c < _
      subst c
      simp only [Nat.add_sub_cancel_left]
      constructor <;> omega
  · intro z U hz
    exact (hrun z U hz).mono (by rw [traceWeight_zero]; omega)

/-- Enter an internal node by clearing only its listed accumulators and storing the actual
zero term counter. This is a complete controller step, including frame loads and comparisons.
Its displayed address budget contains only ordinary workspace parameters and list length. -/
theorem exec_node_enter {w L f a0 b0 d N : ℕ} (x : Data registers)
    (hregs : KernelRegs L f a0 b0 x) (hd : x.regs level = d) (hdL : d < L)
    (hm : x.regs mode = 0) (hN : x.mem (f + 4 * d) = N) (hcap : N ≤ 10 ^ L)
    (input : ℕ → ℕ)
    (hinput : ∀ i < N, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i)
    (hcodes : ∀ i < N, input i < 10 ^ L)
    (hw : Fits w (8 * f + 64 * (L + 1) * 10 ^ L + 128)) :
    ∃ y, ExecWithin w step x y (7 * N + 28) ∧ KernelRegs L f a0 b0 y ∧
      y.regs level = d ∧ y.regs mode = 1 ∧ y.regs epoch = x.regs epoch ∧
      y.regs active = x.regs active ∧
      y.mem = Function.update
        (zeroQueryPrefix x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L)
          input N) (f + 4 * d + 3) 0 ∧
      (∀ i < N, y.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = input i) ∧
      Modifies (nodeWrites L f d) x.mem y.mem := by
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hmul : (d + 1) * 10 ^ L ≤ (L + 1) * 10 ^ L :=
    Nat.mul_le_mul_right _ (by omega)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  obtain ⟨u, hu, humem, huf, huc, _, _, _, hul, huv, _, _, _, hureg⟩ :=
    exec_loadFrame x hregs.one_eq hregs.frameWidth_eq (hw.of_le (by
      rw [hregs.frames_eq, hregs.lists_eq, hregs.values_eq, hregs.span_eq, hd]
      nlinarith only [hpow, hmul, hL, hdL, hcap]))
  have fixed (i : Fin registers) (hi : ¬LoadFrameLocal i) : u.regs i = x.regs i :=
    hureg i hi
  have huf' : u.regs frame = f + 4 * d := by simpa only [hregs.frames_eq, hd] using huf
  have hul' : u.regs listBase = f + 4 * (L + 1) + d * 10 ^ L := by
    simpa only [hregs.lists_eq, hregs.span_eq, hd] using hul
  have huv' : u.regs valueBase = f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L := by
    simpa only [hregs.values_eq, hregs.span_eq, hd] using huv
  have hc : u.regs count = N := by simpa only [hregs.frames_eq, hd, hN] using huc
  have hu0 := (fixed nil (by decide)).trans hregs.nil_eq
  have hu1 := (fixed one (by decide)).trans hregs.one_eq
  have hu4 := (fixed frameWidth (by decide)).trans hregs.frameWidth_eq
  obtain ⟨y, hy, _, _, hym, hymem, hyread, _⟩ := exec_clearValues u input hc
    (by simpa only [hul', humem] using hinput) hcodes
    (Or.inl (by rw [hul', huv']; nlinarith only [hpow, hmul, hL, hdL, hcap]))
    (Or.inl (by rw [huf', hul']; omega)) hu0 hu1 hu4
    (hw.of_le (by rw [hul', huv']; nlinarith only [hpow, hmul, hL, hdL, hcap]))
    (hw.of_le (by rw [huf']; nlinarith only [hpow, hmul, hL, hdL, hcap]))
  have hnotLeaf : ¬(Cond.eq level inputDepth).Holds u := by
    simp only [Cond.holds_eq, fixed level (by decide), fixed inputDepth (by decide),
      hd, hregs.depth_eq]
    omega
  have hentry : ExecWithin w enter u y (7 * N + 10) := hy.branch_neg hnotLeaf
  have hbranch : ExecWithin w
      (ram[ if mode = nil then [ ⟪enter⟫ ] else [
        if mode = one then [ ⟪dispatch⟫ ] else [ ⟪accumulate⟫ ] ] ]) u y (7 * N + 11) :=
    hentry.branch_pos (by simp only [Cond.holds_eq, fixed mode (by decide),
      fixed nil (by decide), hm, hregs.nil_eq])
  have he : ExecWithin w step x y (7 * N + 28) := (hu.seq hbranch).mono (by omega)
  have hmem : y.mem = Function.update
      (zeroQueryPrefix x.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L)
        input N) (f + 4 * d + 3) 0 := by
    simpa only [humem, huv', huf'] using hymem
  refine ⟨y, he, hregs.of_step he, ?_, hym, ?_, ?_, hmem, ?_, ?_⟩
  · exact ((hy.regs_eq (by decide : clearValues.Preserves level)).trans
      (fixed level (by decide))).trans hd
  · exact (hy.regs_eq (by decide : clearValues.Preserves epoch)).trans
      (fixed epoch (by decide))
  · exact (hy.regs_eq (by decide : clearValues.Preserves active)).trans
      (fixed active (by decide))
  · simpa only [hul'] using hyread
  · intro c hc'
    have hf : ¬(Block.mk (f + 4 * d) (4 * (L + 1 - d))).Owns c := by
      intro h
      exact hc' (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Block.mem_footprint.mpr h))))
    have hv : ¬(Block.mk
        (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L) (10 ^ L)).Owns c := by
      intro h
      apply hc'
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [Block.mem_footprint]
      change f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L ≤ c ∧
        c < f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L +
          (L + 1 - d) * 10 ^ L
      change f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L ≤ c ∧
        c < f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + 10 ^ L at h
      have hrem : 1 ≤ L + 1 - d := by omega
      have hm' := Nat.mul_le_mul_right (10 ^ L) hrem
      exact ⟨h.1, by omega⟩
    rw [hmem, Function.update_of_ne (by
      intro heq
      apply hf
      change f + 4 * d ≤ c ∧ c < f + 4 * d + 4 * (L + 1 - d)
      have hrem : 1 ≤ L + 1 - d := by omega
      omega)]
    exact zeroQueryPrefix_outside hcodes hv

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
