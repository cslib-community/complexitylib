/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalPending
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalOutput
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalResources
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalTime

/-!
# Concrete worklist invariant for the native Chan–He traversal

The invariant connects the reserved native stack, existing finite recursion, retained arrays,
output-pointer table and fresh heap. Remaining work pays for both future output cells and future
allocations. In particular, allocation bounds decrease with the mathematical work measure rather
than granting an unbounded heap to each kernel call.

## Main definitions

* `Arena`: fixed caller parameters and disjoint stack/table/heap reservations.
* `Cursor`: represented pending entries and the already emitted native pointers and nodes.
* `Cursor.Invariant`: readback, frames, exact remaining output and concrete space reservations.

These proof invariants are original and do not add a machine model or operational oracle.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Fixed parameters and concrete memory reservations of a complete native root traversal. -/
structure Arena where
  /-- Maximum column cardinality. -/
  n : ℕ
  /-- Candidate-prime bound. -/
  m : ℕ
  /-- Label-bit parameter. -/
  Λ : ℕ
  /-- Node input magnitude. -/
  U : ℕ
  /-- Common number of four-cell packed groups. -/
  N : ℕ
  /-- Root recursion fuel. -/
  fuel : ℕ
  /-- Prime bitmap base. -/
  primes : ℕ
  /-- Reserved native word-stack base. -/
  stack : ℕ
  /-- Reserved native word-stack capacity. -/
  capacity : ℕ
  /-- Unsigned output-pointer table base. -/
  table : ℕ
  /-- Reserved output-pointer table capacity. -/
  outputCapacity : ℕ
  /-- First address permitted for allocated heavy and packed arrays. -/
  floor : ℕ
  /-- Final upper bound on the fresh heap pointer. -/
  ceiling : ℕ
  /-- Protected original memory below the stack, including the complete frontend forest. -/
  retained : ℕ → ℕ

/-- Persistent caller registers, including actual zero and one used by native branches. -/
def Arena.Controls (a : Arena) (x : Data 128) : Prop :=
  x.regs limit = a.m ∧ x.regs digits = a.Λ ∧ x.regs magnitude = a.U ∧
    x.regs groups = a.N ∧ x.regs bitmap = a.primes ∧
    x.regs primeCount = (Nat.primesLE a.m).card ∧ x.regs outputs = a.table ∧
    x.regs stackBase = a.stack ∧ x.regs stackCapacity = a.capacity ∧
    x.regs zero = 0 ∧ x.regs one = 1

/-- Exact register preservation transfers all persistent caller parameters. The heap and
accumulated count are deliberately absent from this fixed register set. -/
theorem Arena.Controls.congr {a : Arena} {x y : Data 128} (h : a.Controls x)
    (hp : ∀ i : Fin 128, i.val ∈ [71, 72, 73, 74, 75, 76, 78, 80, 81, 82, 83] →
      y.regs i = x.regs i) : a.Controls y := by
  rcases h with ⟨hm, hΛ, hU, hN, hb, hc, ht, hs, hcap, hz, ho⟩
  exact ⟨(hp _ (by decide)).trans hm, (hp _ (by decide)).trans hΛ,
    (hp _ (by decide)).trans hU, (hp _ (by decide)).trans hN,
    (hp _ (by decide)).trans hb, (hp _ (by decide)).trans hc,
    (hp _ (by decide)).trans ht, (hp _ (by decide)).trans hs,
    (hp _ (by decide)).trans hcap, (hp _ (by decide)).trans hz,
    (hp _ (by decide)).trans ho⟩

/-- Concrete non-overlap and capacity obligations for the reserved native layout. -/
def Arena.Separated (a : Arena) : Prop :=
  a.primes + a.m < a.stack ∧ a.stack + a.capacity ≤ a.table ∧
    a.table + a.outputCapacity ≤ a.floor ∧ 7 * (2 * a.fuel + 1) ≤ a.capacity

/-- A single signed envelope covers both actual native kernels at every worklist transition. -/
def Arena.Ready (a : Arena) (w : ℕ) : Prop :=
  2 ≤ a.m ∧ 2 * a.m ^ 2 ≤ a.N ∧
    GenericRAM.Signed.Fits w ((envelope a.ceiling a.n a.m a.Λ a.U a.N : ℕ) : ℤ)

/-- The actual native bitmap is retained below the reserved stack. -/
def Arena.Bitmap (a : Arena) (mem : ℕ → ℕ) : Prop :=
  ∀ q ≤ a.m, mem (a.primes + q) = if q.Prime then 1 else 0

/-- Proof state of the actual stack loop; no part of this structure is evaluated by the program. -/
structure Cursor where
  /-- Top-first pending entries. -/
  pending : List Entry
  /-- Packed base pointers and their existing mathematical nodes in emitted order. -/
  emitted : List (ℕ × Node)

/-- Remaining transitions include empty entries and zero-fuel leaves. -/
def Cursor.work (s : Cursor) : ℕ := Math.potential (s.pending.map Entry.task)

/-- Full readback and allocation invariant at the actual native loop header. -/
structure Cursor.Invariant (a : Arena) (w : ℕ) (target : List Node)
    (s : Cursor) (x : Data 128) : Prop where
  /-- All actual native words fit. -/
  bounded : x.Bounded (w + 2)
  /-- Persistent caller parameters have not changed. -/
  controls : a.Controls x
  /-- The actual bitmap still represents all candidate primes. -/
  bitmap : a.Bitmap x.mem
  /-- The actual word stack represents exactly the pending entries. -/
  stack : Stack.Rep (w + 2) a.stack a.capacity
    (s.pending.flatMap Entry.words) (x.comap registers)
  /-- The existing finite depth invariant bounds pending entries. -/
  depth : Math.Bounded a.fuel (s.pending.map Entry.task)
  /-- Every pending entry retains its duplicate-free existing admissibility promise. -/
  valid : ∀ e ∈ s.pending, e.Valid a.n a.U
  /-- Every pending array has exact signed-encoded native readback. -/
  stored : ∀ e ∈ s.pending, e.Stored x.mem
  /-- Pending arrays avoid the entire reserved stack and output-table gap. -/
  around : ∀ e ∈ s.pending, e.Around a.stack (a.floor - a.stack)
  /-- Every pending array lies below the current fresh allocation. -/
  ends : ∀ e ∈ s.pending, ∀ j, e.source j + (e.data j).length ≤ x.regs heap
  /-- The fresh heap never enters the reserved table or stack. -/
  floor : a.floor ≤ x.regs heap
  /-- Remaining work reserves enough space for every later allocation. -/
  heapBudget : x.regs heap + s.work * allocationSize a.n a.m a.N ≤ a.ceiling
  /-- The accumulated native count equals the actual emitted sequence length. -/
  count : x.regs outputCount = s.emitted.length
  /-- Remaining work reserves enough output-table cells. -/
  tableBudget : s.emitted.length + s.work ≤ a.outputCapacity
  /-- Every emitted pointer and every packed cell has exact existing-node readback. -/
  output : StoredNodes a.U a.N a.table s.emitted x.mem
  /-- Retained packed arrays lie above the reserved output table and below the fresh heap. -/
  outputBounds : ∀ i : Fin s.emitted.length,
    a.floor ≤ s.emitted[i.val].1 ∧ s.emitted[i.val].1 + 4 * a.N ≤ x.regs heap
  /-- The emitted prefix followed by the exact pending recursion is the target sequence. -/
  exactOutput : s.emitted.map Prod.snd ++
    Math.output (Nat.primesLE a.m) a.Λ (s.pending.map Entry.task) = target
  /-- Every original cell below the reserved stack remains available to subsequent roots. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- A live loop has at least one pending entry, since each entry occupies seven actual words. -/
theorem Cursor.Invariant.nonempty {a : Arena} {w : ℕ} {target : List Node}
    {s : Cursor} {x : Data 128} (h : s.Invariant a w target x)
    (hc : (Cond.lt zero (registers Stack.len)).Holds x) : s.pending ≠ [] := by
  intro he
  have hz := h.controls.2.2.2.2.2.2.2.2.2.1
  have hl := h.stack.length_eq
  change x.regs zero < x.regs (registers Stack.len) at hc
  simp only [he, List.flatMap_nil, List.length_nil, Data.comap_regs] at hl
  omega

/-- A finished actual loop has emitted the complete target, with every array already read back. -/
theorem Cursor.Invariant.finished {a : Arena} {w : ℕ} {target : List Node}
    {s : Cursor} {x : Data 128} (h : s.Invariant a w target x)
    (hc : ¬(Cond.lt zero (registers Stack.len)).Holds x) :
    s.pending = [] ∧ s.emitted.map Prod.snd = target := by
  have hz := h.controls.2.2.2.2.2.2.2.2.2.1
  have hl := h.stack.length_eq
  rw [length_serialized] at hl
  change ¬x.regs zero < x.regs (registers Stack.len) at hc
  change x.regs (registers Stack.len) = 7 * s.pending.length at hl
  have he : s.pending = [] := List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨he, ?_⟩
  simpa only [he, List.map_nil, Math.output, List.flatMap_nil, List.append_nil] using h.exactOutput

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
