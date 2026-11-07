/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Basic

/-!
# Records and the Fibonacci heap's record, on concrete data

* A record of two cells placed in memory by a concrete `Record.Layout`: a small program run
  through `Record.wp`, and through `Record.refinement` over the memory oracle.
* The all-zero heap record satisfies `Inv`, so the invariant is not vacuous.
* Three insertions from it, two with equal keys: the answers, the minimum root, the counts and the
  exact cost of the run, checked by evaluation; and the specifications `wp_insert` applied in
  sequence, which give the invariant of the final record and its amortized cost bound.
-/

@[expose] public section

namespace ComplexityTests.FibonacciHeapRecord

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
  Cslib.DataStructure.PriorityQueue.FibonacciHeap

/-! ## A record of two cells in memory -/

/-- Cell `false` at address `5` and cell `true` at address `3`. -/
def layout : Record.Layout (fun _ : Bool => True) where
  addr b := if b then 3 else 5
  addr_injOn i j _ _ h := by cases i <;> cases j <;> simp_all

/-- Read cell `false` and write its successor to cell `true`. -/
def bump : Record.Prog Bool Unit := do
  let x ← Record.read false
  Record.write true (x + 1)

/-- Memory holding `6` at address `5`, with six words allocated. -/
def mem : Memory.State := ⟨fun a => if a = 5 then 6 else 0, 6⟩

/-- The record stored in `mem` holds `6` in cell `false`. -/
example : layout.abs mem false = 6 ∧ layout.abs mem true = 0 := by decide

/-- The specification of `bump`: two admissible operations, after which cell `true` holds `7`. -/
theorem bump_spec : Record.wp (fun _ : Bool => True) 4 bump
    (fun _ g t => g true = 7 ∧ g false = 6 ∧ t = 2) (layout.abs mem) := by
  simp only [bump, Record.wp_read_bind, Record.wp_write]
  decide

/-- Both cells are allocated in `mem`. -/
theorem mem_inv : (Record.refinement layout 4).inv mem := fun i _ => by cases i <;> decide

/-- Over memory, `bump` reads address `5` and writes address `3`. -/
example : ((Memory.spec 4).clientState mem (link (layout.methods 4) bump)).mem 3 = 7 := by decide

/-- The refinement theorem applies: the memory run is admissible and stores the record that the
record specification computes. -/
example : (Record.refinement layout 4).abs
      ((Memory.spec 4).clientState mem (link (Record.refinement layout 4).methods bump)) =
    (Record.spec (fun _ : Bool => True) 4).clientState (layout.abs mem) bump :=
  ((Record.refinement layout 4).simulates_client bump mem_inv
    ((Record.wp_iff _ _ _).mp bump_spec).1).2.2.1

/-! ## The heap's record -/

/-- The record specification for heaps on three handles at word size `4`. -/
abbrev heap : StateTransitionSpec := Record.spec (Cell.ok 3) 4

/-- The empty heap: every cell zero. -/
def empty : Cell → ℕ := fun _ => 0

/-- **The invariant is not vacuous**: the all-zero record is a valid empty heap. -/
theorem inv_empty : Inv 3 9 empty :=
  (inv_of_fibRawInv (WordRAM.FibonacciHeap.FibRawInv.empty (fun _ => rfl) (fun _ _ => rfl) rfl rfl
    rfl rfl)).1

/-- Insert handle `1` with key `4`, handle `0` with key `7`, and handle `2` with key `4`. -/
def inserts : Prog Unit := do
  insert 1 4
  insert 0 7
  insert 2 4

/-- All three handles are present with their keys. -/
example : abs 3 (heap.clientState empty inserts) = ![some 7, some 4, some 4] := by decide

/-- The minimum root is handle `1`: it ties with handle `2` on the key and has the smaller handle.
The three handles are roots, and none is marked. -/
example : (view 3 (heap.clientState empty inserts)).minRoot = 1 + 1 ∧
    (view 3 (heap.clientState empty inserts)).numRoots = 3 ∧
    (view 3 (heap.clientState empty inserts)).numMarked = 0 := by decide

/-- The run's exact cost: `14` record operations for the first insertion, into an empty root list,
and `18` for each of the others, which leave the minimum root in place. -/
example : (heap.clientHistory empty inserts).length = 50 := by decide

/-- **The specifications compose on this run**: three applications of `wp_insert` give the
invariant of the final record, its contents, and the amortized bound `3 * (19 + credit)`. -/
theorem inserts_spec : Record.wp (Cell.ok 3) 4 inserts (fun _ g t => Inv 3 9 g ∧
    abs 3 g = ![some 7, some 4, some 4] ∧
      t + potential 3 g ≤ 3 * (19 + credit) + potential 3 empty) empty := by
  have hn : Fits 4 3 := by decide
  have hK : Fits 4 9 := by decide
  simp only [inserts, Record.wp_bind]
  refine Record.wp_mono ?_ (wp_insert (v := 1) (k := 4) inv_empty (by decide) (by decide) hn hK)
  rintro _ g₁ t₁ ⟨habs₁, hI₁, hc₁⟩
  refine Record.wp_mono ?_ (wp_insert (v := 0) (k := 7) hI₁ (by rw [habs₁]; decide) (by decide)
    hn hK)
  rintro _ g₂ t₂ ⟨habs₂, hI₂, hc₂⟩
  refine Record.wp_mono ?_ (wp_insert (v := 2) (k := 4) hI₂ (by rw [habs₂, habs₁]; decide)
    (by decide) hn hK)
  rintro _ g₃ t₃ ⟨habs₃, hI₃, hc₃⟩
  refine ⟨hI₃, by rw [habs₃, habs₂, habs₁]; decide, ?_⟩
  omega

/-- So every operation of the run is admissible, and the record after it satisfies the
invariant. -/
example : heap.ValidHistory empty (heap.clientHistory empty inserts) ∧
    Inv 3 9 (heap.clientState empty inserts) :=
  ⟨((Record.wp_iff _ _ _).mp inserts_spec).1, ((Record.wp_iff _ _ _).mp inserts_spec).2.1⟩

end ComplexityTests.FibonacciHeapRecord
