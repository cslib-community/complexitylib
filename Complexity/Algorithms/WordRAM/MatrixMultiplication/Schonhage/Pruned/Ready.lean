/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Bounds
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Node

/-!
# Entry and return assertions for the native node induction

## Main definitions

* `PrunedQuery.NodeReady`: the actual stored frame and timestamped query representation.
* `PrunedQuery.NodeResult`: register, value and spatial conclusions after returning.

## Main results

* `PrunedQuery.exec_ready_zero`: the terminal induction case for arbitrary supplied arrays.

Neither assertion contains execution, time or fit fields. Width and magnitude assumptions are
ordinary numerical input bounds, and execution is proved in the existing native semantics.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Entry to one node, as established by the native root scan or a native child push. -/
structure NodeReady (L f a0 b0 n d p E : ℕ) (S : Finset (OutStr n))
    (x : Data registers) : Prop where
  /-- The computed workspace pointers and constant registers. -/
  regs : KernelRegs L f a0 b0 x
  /-- The two tuple lengths agree with the original depth. -/
  depth_add : d + n = L
  /-- The leaf prefix is within its already processed digit space. -/
  prefix_lt : p < 10 ^ d
  /-- The actual cursor points to this frame. -/
  level_eq : x.regs level = d
  /-- This node has not begun its entry phase. -/
  mode_eq : x.regs mode = 0
  /-- The traversal is still active. -/
  active_eq : x.regs active = 1
  /-- Current actual timestamp generation. -/
  epoch_eq : x.regs epoch = E
  /-- Four stored words: count, prefix, stride and first term. -/
  frame : (Block.mk (f + 4 * d) 4).Realizes x.mem ![S.card, p, 10 ^ d, 0]
  /-- The actual list and directory represent exactly the requested numerical codes. -/
  requests : ScanMemory x.mem (f + 4 * (L + 1) + d * 10 ^ L)
    (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L) E (10 ^ L)
    (S.image fun q => (queryIndex q).val)

/-- The spatial and mathematical result of one node. This is a postcondition on the actual
data, with no execution or time claim embedded in it. -/
structure NodeResult (L f a0 b0 n d E : ℕ) (S : Finset (OutStr n))
    (a b : Leaf n → ℤ) (x y : Data registers) : Prop where
  /-- Constant parameters remain unchanged. -/
  regs : KernelRegs L f a0 b0 y
  /-- Return to the parent, keeping zero at the root. -/
  level_eq : y.regs level = if d = 0 then 0 else d - 1
  /-- A parent resumes accumulation after a non-root node. -/
  mode_eq : 0 < d → y.regs mode = 2
  /-- Only returning from the root stops traversal. -/
  active_eq : y.regs active = if d = 0 then 0 else 1
  /-- Timestamp generations do not go backwards. -/
  epoch_le : E ≤ y.regs epoch
  /-- All fresh generations are covered by the remaining-depth allowance. -/
  epoch_upper : y.regs epoch ≤ E + epochAllowance n
  /-- The directory is ready for the next fresh-generation scan. -/
  timestamps : ∀ q < 10 ^ L,
    y.mem (f + 4 * (L + 1) + 2 * (L + 1) * 10 ^ L + q) ≤ y.regs epoch
  /-- Every requested cell holds the existing pruned result, in its original code position. -/
  values : ∀ q ∈ S,
    y.mem (f + 4 * (L + 1) + (L + 1) * 10 ^ L + d * 10 ^ L + (queryIndex q).val) =
      encode (Pruned.result n a b S q)
  /-- Caller memory, including ancestor rows, is preserved outside the concrete node frame. -/
  frame : Modifies (nodeWrites L f d) x.mem y.mem

/-- A ready frame's stored count cannot exceed its actual list row capacity. -/
theorem NodeReady.card_le {L f a0 b0 n d p E : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x) : S.card ≤ 10 ^ L := by
  simpa only [card_image_queryIndex] using h.requests.card_le

/-- The occupied words of the actual row encode exactly the requested output strings. -/
theorem NodeReady.image_read {L f a0 b0 n d p E : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x) :
    (Finset.range S.card).image (fun i =>
      x.mem (f + 4 * (L + 1) + d * 10 ^ L + i)) =
        S.image (fun q => (queryIndex q).val) := by
  simpa only [card_image_queryIndex] using h.requests.image_read

/-- Every occupied source-list word comes from one of the requested mathematical outputs. -/
theorem NodeReady.exists_of_read {L f a0 b0 n d p E i : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x) (hi : i < S.card) :
    ∃ q ∈ S, (queryIndex q).val = x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) := by
  apply Finset.mem_image.mp
  rw [← h.image_read]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- Actual query words fit the remaining query space, not only the original workspace row. -/
theorem NodeReady.read_lt {L f a0 b0 n d p E i : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x) (hi : i < S.card) :
    x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) < 10 ^ n := by
  obtain ⟨q, _, hq⟩ := h.exists_of_read hi
  exact hq ▸ (queryIndex q).isLt

/-- Every requested output occurs at a concrete occupied position of the native list. -/
theorem NodeReady.exists_read {L f a0 b0 n d p E : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x) {q : OutStr n} (hq : q ∈ S) :
    ∃ i < S.card, x.mem (f + 4 * (L + 1) + d * 10 ^ L + i) = (queryIndex q).val := by
  have hm : (queryIndex q).val ∈ S.image (fun v => (queryIndex v).val) :=
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  rw [← h.image_read] at hm
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
  exact ⟨i, Finset.mem_range.mp hi, he⟩

/-- Distinct occupied positions cannot name the same parent query. -/
theorem NodeReady.injOn_read {L f a0 b0 n d p E : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x) :
    Set.InjOn (fun i => x.mem (f + 4 * (L + 1) + d * 10 ^ L + i)) {i | i < S.card} := by
  simpa only [card_image_queryIndex] using h.requests.injOn_read

/-- Each strided input address remains inside the original input block below the workspace. -/
theorem NodeReady.source_before {L f a0 b0 n d p E base : ℕ} {S : Finset (OutStr n)}
    {x : Data registers} (h : NodeReady L f a0 b0 n d p E S x)
    (hbase : base + 10 ^ L ≤ f) (v : Leaf n) :
    base + p + 10 ^ d * (Encoding.leafIndex v).val < f := by
  have hs : (10 : ℕ) ^ d * 10 ^ n = 10 ^ L := by rw [← pow_add, h.depth_add]
  have hv := leafAddress_lt h.prefix_lt hs v
  omega

/-- The terminal node proof obtains its signed fits from the common original magnitude
envelope. The same returned memory satisfies the result and the charged native continuation. -/
theorem exec_ready_zero {w L f a0 b0 d p E A B : ℕ} (S : Finset (OutStr 0))
    (a b : Leaf 0 → ℤ) (x : Data registers) (hx : NodeReady L f a0 b0 0 d p E S x)
    (hleft : ∀ v, x.mem (a0 + p + 10 ^ d * (Encoding.leafIndex v).val) = encode (a v))
    (hright : ∀ v, x.mem (b0 + p + 10 ^ d * (Encoding.leafIndex v).val) = encode (b v))
    (ha : ∀ v, |a v| ≤ (A : ℤ)) (hb : ∀ v, |b v| ≤ (B : ℤ))
    (hw : 0 < w) (hmag : magnitudeBound L A B < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (nodeBudget L f a0 b0 E 0)) :
    ∃ y, NodeResult L f a0 b0 0 d E S a b x y ∧
      ∀ z U, ExecWithin (w + 2) controller y z U →
        ExecWithin (w + 2) controller x z (traceWeight S + U) := by
  have hd : d = L := by have := hx.depth_add; omega
  subst d
  have henv := magnitudeBound_fits hw hmag
  have hi : (Encoding.leafIndex (Fin.elim0 : Leaf 0)).val = 0 := by decide
  have hcount : x.mem (f + 4 * L) = S.card := hx.frame 0
  have hpref : x.mem (f + 4 * L + 1) = p := hx.frame 1
  have hA : x.mem (a0 + p) = encode (a Fin.elim0) := by
    simpa only [hi, Nat.mul_zero, Nat.add_zero] using hleft Fin.elim0
  have hB : x.mem (b0 + p) = encode (b Fin.elim0) := by
    simpa only [hi, Nat.mul_zero, Nat.add_zero] using hright Fin.elim0
  have hpow : 1 ≤ (10 : ℕ) ^ L := Nat.one_le_pow L _ (by decide)
  have hL : L + 1 ≤ (L + 1) * 10 ^ L := by nlinarith only [hpow]
  obtain ⟨y, hregs, hyl, hym, hya, hye, hmarks, hvalue, hframe, _, hrun⟩ :=
    exec_node_zero (fits_left henv (ha Fin.elim0)) (fits_right henv (hb Fin.elim0))
      (fits_product henv (ha Fin.elim0) (hb Fin.elim0)) S x hx.regs hx.level_eq
      hx.mode_eq hx.active_eq hcount hpref hA hB hx.epoch_eq hx.requests.stamp_le
      (hfit.of_le (by
        unfold nodeBudget
        rw [epochAllowance_zero]
        nlinarith only [hpow, hL, hx.prefix_lt]))
  refine ⟨y, ⟨hregs, hyl, ?_, hya, ?_, ?_, ?_, hvalue, hframe⟩, hrun⟩
  · intro hLpos
    simpa only [ite_eq_right (by omega : L ≠ 0)] using hym
  · omega
  · simp only [hye, epochAllowance_zero, Nat.add_zero, le_refl]
  · intro q hq
    simpa only [hye] using hmarks q hq

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
