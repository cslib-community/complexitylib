/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.State
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Push

/-!
# Computed Strassen child buffers

All six child fields below are produced by the actual `locateChild` block. The layout
assertions are internal loop invariants derived from its numerical result, never a
precomputed layout parameter supplied to the program. The common parent header and every
earlier frame word survive this read-only stage.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Exact child words computed by the native six-instruction buffer calculation. -/
structure ChildBuffers (p k scratch : ℕ) (x : Data 64) : Prop where
  /-- Runtime quarter length. -/
  quarter_eq : x.regs Reg.quarter = 4 ^ k * p
  /-- Actual first form buffer. -/
  formA_eq : x.regs Reg.formA = scratch
  /-- Actual second form buffer. -/
  formB_eq : x.regs Reg.formB = scratch + 4 ^ k * p
  /-- Actual child output buffer. -/
  product_eq : x.regs Reg.product = scratch + 2 * (4 ^ k * p)
  /-- Remaining scratch begins after the three real buffers. -/
  scratch_eq : x.regs Reg.childScratch = scratch + 3 * (4 ^ k * p)
  /-- Actual child depth. -/
  depth_eq : x.regs Reg.childDepth = k

/-- The low-bank operand kernels preserve every computed child-buffer register. -/
theorem ChildBuffers.of_regs_eq {p k scratch : ℕ} {x y : Data 64}
    (h : ChildBuffers p k scratch x)
    (hr : ∀ i, 50 ≤ i.val → i.val < 56 → y.regs i = x.regs i) :
    ChildBuffers p k scratch y :=
  ⟨(hr _ (by decide) (by decide)).trans h.quarter_eq,
    (hr _ (by decide) (by decide)).trans h.formA_eq,
    (hr _ (by decide) (by decide)).trans h.formB_eq,
    (hr _ (by decide) (by decide)).trans h.product_eq,
    (hr _ (by decide) (by decide)).trans h.scratch_eq,
    (hr _ (by decide) (by decide)).trans h.depth_eq⟩

/-- The native block derives all child buffer words and preserves the parent header/phase,
using only the original node address envelope for every arithmetic fit. -/
theorem exec_locateChild_header {w p k a b out scratch frames frame : ℕ}
    (x : Data 64) (hx : NodeHeader p (k + 1) a b out scratch frames frame x)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (haddr : Fits w (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin w locateChild x y 6 ∧
      NodeHeader p (k + 1) a b out scratch frames frame y ∧
      ChildBuffers p k scratch y ∧ y.mem = x.mem ∧
      ∀ i, i.val < 50 → y.regs i = x.regs i := by
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  have hq : x.regs Reg.size / 4 = 4 ^ k * p := by rw [hx.size_eq, hsize]; omega
  have hbefore := hl.scratch_before
  obtain ⟨y, hy, hm, hquarter, ha, hb, hp, hs, hd, hr⟩ := exec_locateChild x hx.one_eq hx.four_eq
    (by
      rw [hx.scratch_eq, hx.size_eq, hx.depth_eq]
      exact haddr.of_le (by unfold addressBound; omega))
  have hhigh (i : Fin 64) (hi : i.val < 50) : y.regs i = x.regs i :=
    hr i (by intro he; subst i; contradiction) (by intro he; subst i; contradiction)
      (by intro he; subst i; contradiction) (by intro he; subst i; contradiction)
      (by intro he; subst i; contradiction) (by intro he; subst i; contradiction)
  refine ⟨y, hy, hx.of_regs_eq (fun i _ hi => hhigh i hi), ?_, hm, hhigh⟩
  refine ⟨hquarter.trans hq, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hx.scratch_eq] using ha
  · simpa only [hx.scratch_eq, hq] using hb
  · simpa only [hx.scratch_eq, hq] using hp
  · simpa only [hx.scratch_eq, hq] using hs
  · simpa only [hx.depth_eq, Nat.add_sub_cancel_right] using hd

end Cslib.Algorithms.WordRAM.Strassen
