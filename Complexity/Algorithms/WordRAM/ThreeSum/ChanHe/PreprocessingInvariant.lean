/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLoad
public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Frame

/-!
# Shared resources across all native frontend roots

The outer loop reserves heap and pointer cells for every remaining root. A particular root gets
only its own remaining allocation, so its execution theorem cannot consume another root's budget.

## Main definitions

* `rootArena`: the existing traversal arena restricted to one root's actual remaining budget.
* `ForestCursor`, `ForestCursor.Invariant`: exact root index, output and global resource relation.

## Main results

* `rootArena_ready`: the global signed envelope derives each dynamic root envelope.

These native composition invariants are original; the program remains the existing native code.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Restrict a root call to its own heap and pointer-table allowance. All addresses stay fixed. -/
def rootArena (a : Traversal.Arena) (x : Data 128) (ns : List (ℕ × Node)) : Traversal.Arena :=
  { a with
    ceiling := x.regs Traversal.heap +
      Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N
    outputCapacity := ns.length + Traversal.Math.work a.fuel }

/-- Monotonicity of the existing polynomial envelope derives every root's actual local fit. -/
theorem rootArena_ready {a : Traversal.Arena} {w : ℕ} {x : Data 128}
    {ns : List (ℕ × Node)} (hw : a.Ready w)
    (hh : (rootArena a x ns).ceiling ≤ a.ceiling) : (rootArena a x ns).Ready w := by
  refine ⟨hw.1, hw.2.1, ?_⟩
  apply GenericRAM.Signed.Fits.of_natAbs_le hw.2.2
  simp only [Int.natAbs_natCast]
  dsimp only [Traversal.envelope]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [rootArena] at *; omega) 4)

/-- Mathematical proof state of the native outer descriptor loop. -/
structure ForestCursor where
  /-- Number of root descriptors already executed. -/
  index : ℕ
  /-- Actual native pointer and existing-node pairs already emitted. -/
  nodes : List (ℕ × Node)

/-- Exact frontend output, native controller registers and all remaining-root reservations. -/
structure ForestCursor.Invariant (a : Traversal.Arena) (w : ℕ) (l : Frontend.Layout)
    (U : ℕ) (rs : List (ℕ × ℕ)) (s : ForestCursor) (x : Data 128) : Prop where
  /-- Every actual word fits. -/
  bounded : x.Bounded (w + 2)
  /-- The traversal constants remain actual registers. -/
  controls : a.Controls x
  /-- Every frontend descriptor and compact array is still available. -/
  frontend : Frontend.Output l U rs x.mem
  /-- Actual descriptor base and root count. -/
  descriptors : x.regs descriptors = l.descriptors
  roots : x.regs roots = l.count
  /-- Actual root index and shared fuel. -/
  current : x.regs current = s.index
  levels : x.regs levels = a.fuel
  /-- Native descriptor stride and outer increment constant. -/
  stride : x.regs stride = 6
  one : x.regs one = 1
  /-- The actual index never passes the last descriptor. -/
  index_le : s.index ≤ l.count
  /-- Every candidate prime still has its actual bitmap bit. -/
  bitmap : a.Bitmap x.mem
  /-- The heap avoids all shared reservations. -/
  floor : a.floor ≤ x.regs Traversal.heap
  /-- All unprocessed roots retain their complete allocation budgets. -/
  heapBudget : x.regs Traversal.heap + (l.count - s.index) *
    (Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N) ≤ a.ceiling
  /-- The native count agrees with the emitted list. -/
  count : x.regs Traversal.outputCount = s.nodes.length
  /-- All unprocessed roots retain their complete pointer-table budgets. -/
  tableBudget : s.nodes.length + (l.count - s.index) * Traversal.Math.work a.fuel ≤
    a.outputCapacity
  /-- Exact native pointer-table and packed-cell readback. -/
  output : Traversal.StoredNodes a.U a.N a.table s.nodes x.mem
  /-- Every earlier packed array is safely below the current fresh allocation. -/
  outputBounds : ∀ i : Fin s.nodes.length,
    a.floor ≤ s.nodes[i.val].1 ∧ s.nodes[i.val].1 + 4 * a.N ≤ x.regs Traversal.heap
  /-- The emitted prefix and untouched roots give exactly the original finite forest. -/
  exactOutput : s.nodes.map Prod.snd ++
    Traversal.Math.output (Nat.primesLE a.m) a.Λ
      (((entries l U rs).drop s.index).map Traversal.Entry.task) =
    Traversal.Math.output (Nat.primesLE a.m) a.Λ
      ((entries l U rs).map Traversal.Entry.task)
  /-- Original memory below the shared stack is retained throughout the forest. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- A live outer iteration has room for the one root it is about to execute. -/
theorem ForestCursor.Invariant.root_budgets {a : Traversal.Arena} {w U : ℕ}
    {l : Frontend.Layout} {rs : List (ℕ × ℕ)} {s : ForestCursor} {x : Data 128}
    (h : s.Invariant a w l U rs x)
    (hc : (Cond.lt Preprocessing.current Preprocessing.roots).Holds x) :
    (rootArena a x s.nodes).ceiling ≤ a.ceiling ∧
      (rootArena a x s.nodes).outputCapacity ≤ a.outputCapacity := by
  have hi : s.index < l.count := by
    simpa only [Cond.holds_lt, h.current, h.roots] using hc
  have hm : 1 ≤ l.count - s.index := by omega
  have hh := Nat.mul_le_mul_left
    (Traversal.Math.work a.fuel * Traversal.allocationSize a.n a.m a.N) hm
  have ht := Nat.mul_le_mul_left (Traversal.Math.work a.fuel) hm
  rw [Nat.mul_one, Nat.mul_comm _ (l.count - s.index)] at hh ht
  constructor <;> dsimp only [rootArena]
  · have := h.heapBudget
    omega
  · have := h.tableBudget
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
