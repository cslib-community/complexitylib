/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.Encoding
import CslibFrontier.Tactic.Realize

/-!
# Compact heap initialization primitives

Existing realization rules reserve the original three-array span and compute three layout
words. Reservation preserves the complete physical memory; a separately supplied local-zero
block gives the existing compact empty invariant. Metadata staging is actual charged scalar
glue and copies, leaving both input words and every memory cell intact.

The separate canonical allocator certificate preserves `Memory.allocLayout`'s two dirty queries
and larger `3*n+2` span, wrapping its final layout in the existing faithful sigma encoding.
These primitives do not replace `Memory.allocLayout`, instantiate a local-zero generic
allocator, choose the final caller ABI or claim the legacy eleven-instruction initializer.
Code, scratch and exchange constants are uniform before all runtime sizes, bases and widths.

## Main results

* `realizes_reserve`, `reserve_exec`: reserve exactly `space n`, returning the old frontier.
* `realizes_metadata`, `metadata_exec`: compute `[n,base+n,1]` with charged native glue.
* `reserve_empty`: the actual reservation gives the existing compact empty heap under local zero.
* `realizes_allocLayout`, `allocLayout_exec`: certify the unchanged allocator used by Dijkstra.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize

open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.BinaryHeap (space)

private theorem space_add (n : ℕ) : space n = (n + n) + n + 1 := by
  unfold space
  omega

/-- Reserve the exact original span. The addition spelling avoids materializing a constant
three, which need not fit in an admitted one-bit zero-handle initialization. -/
theorem realizes_reserve : Realizes .exact (fun n : ℕ => Memory.allocDirty (space n))
    (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
    (fun w n s => Fits w (s.frontier + space n)) (fun _ _ => 0) := by
  have h : Realizes .exact (fun n : ℕ => Memory.allocDirty ((n + n) + n + 1))
      (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w n s => Fits w (s.frontier + space n)) (fun _ _ => 0) := by
    realize
    all_goals exact h.of_le (by unfold space; omega)
  exact h.congr (fun n => by rw [space_add])

/-- One selected reservation emitter returns the old frontier, preserves every cell and moves
the frontier by exactly the old span. Its one memory charge plus the fixed exit unit cost at
most `2*factor`; caller inputs and all non-scratch registers are framed. -/
theorem reserve_exec {r : ℕ} (frontier : Fin r) (src : Fin 1 → Fin r)
    (tmp : Fin (1 + realizes_reserve.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w n : ℕ} (x : Data r) (hx : x.Bounded w)
    (hin : x.regs ∘ src = WordEncoding.encode (α := ℕ) n)
    (hfit : Fits w (x.regs frontier + space n)) :
    ∃ y, ExecWithin w (realizes_reserve.code frontier src tmp) x y
        (2 * realizes_reserve.factor) ∧ y.Bounded w ∧
      y.mem = x.mem ∧ y.regs frontier = x.regs frontier + space n ∧
      y.regs (tmp (Fin.castAdd (realizes_reserve.scratchSize + 1) 0)) = x.regs frontier ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  have hv : (Memory.spec w).ValidHistory (memoryState frontier x)
      ((Memory.spec w).clientHistory (memoryState frontier x) (Memory.allocDirty (space n))) :=
    ⟨hfit, trivial⟩
  obtain ⟨y, hy, hm, ho, hframe⟩ :=
    (realizes_reserve.code_spec frontier src tmp hi hd hf hs).2 w n x hx hin hfit hv
  have hc : memoryCost (Memory.allocDirty (space n)) (memoryState frontier x) = 1 := rfl
  refine ⟨y, ?_, hy.bounded hx, congrArg Memory.State.mem hm,
    congrArg Memory.State.frontier hm, ho 0, hframe⟩
  simpa only [hc, Nat.add_zero, Nat.mul_comm] using hy

/-- Reserve-only initialization of a locally zero old span gives the existing empty invariant.
This is a one-run source/representation statement, not a generic allocator precondition. -/
theorem reserve_empty {r n : ℕ} (frontier : Fin r) {x y : Data r}
    (hm : y.mem = x.mem) (hfr : y.regs frontier = x.regs frontier + space n)
    (hz : ∀ a, (Block.mk (x.regs frontier) (space n)).Owns a → x.mem a = 0) :
    BinaryHeap.Memory.Inv (BinaryHeap.Memory.compactLayout n (x.regs frontier))
        (memoryState frontier y) ∧
      BinaryHeap.Memory.abs (BinaryHeap.Memory.compactLayout n (x.regs frontier))
        (memoryState frontier y) = IndexedMinPQ.empty n := by
  apply BinaryHeap.Memory.inv_compactLayout
  · change x.regs frontier + space n ≤ y.regs frontier
    exact hfr.ge
  · intro a ha
    change y.mem a = 0
    rw [hm]
    exact hz a ha

/-- Compute three future layout registers from faithfully encoded `(n,base)`. The result vector
is itself faithfully encoded, with the original input registers framed. Every coordinate and
copy is paid through the existing pure-glue rule; no host computation installs the result. -/
theorem realizes_metadata : Realizes .exact
    (fun p : ℕ × ℕ => pure (![p.1, p.2 + p.1, 1] : Fin 3 → ℕ))
    (WordEncoding.encode (α := ℕ × ℕ)) (.refl (Fin 3 → ℕ))
    (fun w p _ => Fits w (p.2 + space p.1)) (fun _ _ => 0) := by
  let g : Fin 3 → (Fin 2 → ℕ) → ℕ := ![fun v => v 0, fun v => v 1 + v 0, fun _ => 1]
  let bound : (Fin 2 → ℕ) → ℕ := fun v => v 1 + space (v 0)
  have hp0 : GlueComputable .exact (fun v : Fin 2 → ℕ => v 0) (fun _ => True) bound :=
    GlueComputable.proj 0 (fun v _ => by dsimp only [bound]; unfold space; omega)
  have hp1 : GlueComputable .exact (fun v : Fin 2 → ℕ => v 1) (fun _ => True) bound :=
    GlueComputable.proj 1 (fun v _ => by dsimp only [bound]; unfold space; omega)
  have hcoord (i : Fin 3) : GlueComputable .exact (g i) (fun _ => True) bound := by
    fin_cases i
    · exact hp0
    · exact hp1.add hp0 (fun v _ => by dsimp only [bound]; unfold space; omega)
    · exact GlueComputable.const 1 (fun v _ => by dsimp only [bound]; unfold space; omega)
  refine (Realizes.pure₀ (WordEncoding.encode (α := ℕ × ℕ)) (.refl (Fin 3 → ℕ))
    (fun p => ![p.1, p.2 + p.1, 1]) g (fun w v => Fits w (bound v))
    (fun p i => by fin_cases i <;> rfl) hcoord (fun _ _ _ _ h => h)).consequence ?_
      (fun _ _ => le_rfl)
  intro w p s _ _ h
  exact ⟨trivial, h⟩

/-- The selected metadata code performs its charged computation even though its source history
is empty. It leaves the frontier, whole memory and both live input words unchanged. -/
theorem metadata_exec {r : ℕ} (frontier : Fin r) (src : Fin 2 → Fin r)
    (tmp : Fin (3 + realizes_metadata.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w : ℕ} (p : ℕ × ℕ) (x : Data r) (hx : x.Bounded w)
    (hin : x.regs ∘ src = WordEncoding.encode (α := ℕ × ℕ) p)
    (hfit : Fits w (p.2 + space p.1)) :
    ∃ y, ExecWithin w (realizes_metadata.code frontier src tmp) x y
        realizes_metadata.factor ∧ y.Bounded w ∧ memoryState frontier y = memoryState frontier x ∧
      (∀ i : Fin 3, y.regs (tmp (Fin.castAdd (realizes_metadata.scratchSize + 1) i)) =
        ![p.1, p.2 + p.1, 1] i) ∧
      y.regs ∘ src = WordEncoding.encode (α := ℕ × ℕ) p ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  obtain ⟨y, hy, hm, ho, hframe⟩ :=
    (realizes_metadata.code_spec frontier src tmp hi hd hf hs).2 w p x hx hin hfit trivial
  refine ⟨y, ?_, hy.bounded hx, hm, ho, ?_, hframe⟩
  · simpa only [memoryCost_pure, Nat.zero_add, Nat.mul_one] using hy
  · funext i
    exact (hframe (src i) (hs i) (fun j => (hd i j).symm)).trans (congrFun hin i)

/-- The canonical source allocator keeps its two dirty queries and its extra count word.
Only its result is placed in the existing fixed Sigma carrier for uniform native code. -/
theorem allocLayout_run (w n : ℕ) (s : Memory.State) :
    (Memory.spec w).runClient s
      (do let L ← BinaryHeap.Memory.allocLayout n; pure (⟨n, L⟩ : HeapLayout)) =
      (⟨n, BinaryHeap.Memory.allocated n s.frontier⟩,
        ⟨s.mem, s.frontier + 1 + space n⟩, [.allocDirty 1, .allocDirty (space n)]) := rfl

/-- Realize the unchanged canonical allocator. This is the `3*n+2` source used by Dijkstra,
not the compact reserve-only primitive; no global zero claim is hidden in its native domain. -/
theorem realizes_allocLayout : Realizes .exact
    (fun n : ℕ => do let L ← BinaryHeap.Memory.allocLayout n; pure (⟨n, L⟩ : HeapLayout))
    (WordEncoding.encode (α := ℕ)) layoutWords
    (fun w n s => Fits w (s.frontier + 1 + space n)) (fun _ _ => 0) := by
  have h : Realizes .exact
      (fun n : ℕ => do
        let size ← Memory.allocBlockDirty 1
        let arrays ← Memory.allocBlockDirty ((n + n) + n + 1)
        pure (⟨n, ⟨size, arrays.base⟩⟩ : HeapLayout))
      (WordEncoding.encode (α := ℕ)) layoutWords
      (fun w n s => Fits w (s.frontier + 1 + space n)) (fun _ _ => 0) := by
    realize
    all_goals exact h.of_le (by unfold space; omega)
  exact h.congr (fun n => by
    simp only [BinaryHeap.Memory.allocLayout, space_add, bind_assoc, pure_bind])

/-- One selected code before all runtime sizes/frontiers/widths runs the actual two-query
allocator. Memory is literally unchanged; the original allocated layout is really staged in
four output words, and the source's two memory charges give the native `3*factor` bound. -/
theorem allocLayout_exec {r : ℕ} (frontier : Fin r) (src : Fin 1 → Fin r)
    (tmp : Fin (4 + realizes_allocLayout.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {w n : ℕ} (x : Data r) (hx : x.Bounded w)
    (hin : x.regs ∘ src = WordEncoding.encode (α := ℕ) n)
    (hfit : Fits w (x.regs frontier + 1 + space n)) :
    ∃ y, ExecWithin w (realizes_allocLayout.code frontier src tmp) x y
        (3 * realizes_allocLayout.factor) ∧ y.Bounded w ∧ y.mem = x.mem ∧
      y.regs frontier = x.regs frontier + 1 + space n ∧
      (∀ i : Fin 4,
        y.regs (tmp (Fin.castAdd (realizes_allocLayout.scratchSize + 1) i)) =
          layoutWords ⟨n, BinaryHeap.Memory.allocated n (x.regs frontier)⟩ i) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  have hv : (Memory.spec w).ValidHistory (memoryState frontier x)
      ((Memory.spec w).clientHistory (memoryState frontier x)
        (do let L ← BinaryHeap.Memory.allocLayout n; pure (⟨n, L⟩ : HeapLayout))) := by
    change Fits w (x.regs frontier + 1) ∧
      Fits w (x.regs frontier + 1 + space n) ∧ True
    exact ⟨hfit.of_le (by omega), hfit, trivial⟩
  obtain ⟨y, hy, hm, ho, hframe⟩ :=
    (realizes_allocLayout.code_spec frontier src tmp hi hd hf hs).2 w n x hx hin hfit hv
  have hc : memoryCost
      (do let L ← BinaryHeap.Memory.allocLayout n; pure (⟨n, L⟩ : HeapLayout))
      (memoryState frontier x) = 2 := rfl
  refine ⟨y, ?_, hy.bounded hx, congrArg Memory.State.mem hm,
    congrArg Memory.State.frontier hm, ho, hframe⟩
  simpa only [hc, Nat.add_zero, Nat.mul_comm] using hy

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native.Initialize
