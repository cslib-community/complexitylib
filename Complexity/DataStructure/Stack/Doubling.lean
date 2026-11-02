/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Alloc
public import Complexity.DataStructure.Memory.Copy
public import Complexity.DataStructure.Memory.Field
public import Complexity.DataStructure.Stack.WordRAM.Basic

/-!
# A stack in a doubling array over the memory oracle

The bounded stack `Stack.WordRAM.spec w C` is implemented by a growing array: a dynamic array
used as a stack. A header of three cells at `hdr` holds the number of items, the capacity, and the
base address of the item array. A push into a full array first allocates an array of twice the
capacity, copies the items into it and switches the header to it (`grow`). The old array is
abandoned, since memory is never reused.

So the structure allocates inside its operations. It is a `Memory.Framed` refinement whose
footprint, the header and the current array, moves into fresh cells as it grows, and whose room,
`4 C - 2 · capacity`, is what its future growth may still allocate: doubling from capacity `c`
allocates `2 c` cells and lowers the room by exactly `2 c`. Its invariant asks that the frontier
plus the room fit a word, which is what makes each allocation admissible. In a product with other
structures that allocate (`Memory.Framed.prod`), the shared room budget keeps this true.

Every operation costs at most `13` memory units, amortized, with the potential
`2 (2 · count - capacity)`: a push into a full array of `n` items costs `9 + 2 n` and releases
the potential `2 n`. The allocator (`allocator`) sets up an empty stack of capacity one in four
cells, at a cost of seven units, and reserves `4 C + 4` cells in all.

The word RAM's counterpart is `DynamicArray.WordRAM`, whose append routine is stepped
instruction by instruction and which assumes that it is the only allocator.

## Main definitions

* `count`, `capacity`, `base`: the header's cells, read from memory.
* `grow`, `push`, `pop`, `size`, `methods`: the operations as memory programs.
* `abs`, `Inv`, `footprint`, `room`, `potential`: the representation.
* `refinement`, `framed`: the doubling stack as a refinement, and framed with room.
* `create`, `allocator`: allocate an empty doubling stack.

## Main results

* `push_full`, `push_not_full`, `pop_of_ne_zero`: the operations' effects on the header and the
  cells.
* `congr`, `modifies_methods`: the frame, with the footprint growing into fresh cells and the
  frontier advancing by at most the room given up.
* `amortized`: every operation costs at most thirteen memory units, amortized.
* `amortized_allocator`: the allocator's cost certificate.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 17.4][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Stack.Doubling

open Cslib.WordRAM Cslib.WordRAM.ArrayCopy Cslib.DataStructure Cslib.DataStructure.Memory
  Cslib.DataStructure.Queue

/-! ## The representation -/

variable (hdr : ℕ)

/-- The number of items, in the header's first cell. -/
def count (s : State) : ℕ := s.mem hdr

/-- The capacity of the item array, in the header's second cell. -/
def capacity (s : State) : ℕ := s.mem (hdr + 1)

/-- The base address of the item array, in the header's third cell. -/
def base (s : State) : ℕ := s.mem (hdr + 2)

/-- The item array. -/
def items (s : State) : Block := ⟨base hdr s, capacity hdr s⟩

/-- The stored stack, top first: the first `count` items, reversed. -/
def abs (s : State) : List ℕ := ((items hdr s).entries (count hdr s) s.mem).reverse

/-- The header's three cells and the current item array. -/
def footprint (s : State) : Finset ℕ := (Block.mk hdr 3).footprint ∪ (items hdr s).footprint

/-- The cells that growing to capacity `2 C` may still allocate. -/
def room (C : ℕ) (s : State) : ℕ := 4 * C - 2 * capacity hdr s

/-- Two credits per item beyond half the capacity, which pay for copying them. -/
def potential (s : State) : ℕ := 2 * (2 * count hdr s - capacity hdr s)

/-- The implementation invariant. -/
structure Inv (w C : ℕ) (s : State) : Prop where
  /-- The item array lies above the header. -/
  header_le : hdr + 3 ≤ base hdr s
  /-- The item array is allocated. -/
  items_le : base hdr s + capacity hdr s ≤ s.frontier
  /-- The capacity is positive, so doubling grows it. -/
  one_le_capacity : 1 ≤ capacity hdr s
  /-- The items fit the array. -/
  count_le : count hdr s ≤ capacity hdr s
  /-- The frontier plus the room fits a word, so growing is admissible. -/
  fits_room : Fits w (s.frontier + room hdr C s)
  /-- The items are words. -/
  items_fit : ∀ i < count hdr s, Fits w (s.mem (base hdr s + i))

/-! ## The operations -/

/-- Double the capacity of a full array of `n` items: allocate `2 n` cells, copy the items, and
switch the header to the new array. -/
def grow (n : ℕ) : Prog Unit := do
  let p ← read (hdr + 2)
  let q ← allocDirty (2 * n)
  copy p q n
  write (hdr + 2) q
  write (hdr + 1) (2 * n)

/-- Grow the array if the `n` items fill its capacity `c`. -/
def ensure (n c : ℕ) : Prog Unit := if n = c then grow hdr n else pure ()

/-- Write the item `v` after the `n` items, and count it. -/
def append (n v : ℕ) : Prog Unit := do
  let p ← read (hdr + 2)
  write (p + n) v
  write hdr (n + 1)

/-- Push: grow a full array, then append. -/
def push (v : ℕ) : Prog Unit := do
  let n ← read hdr
  let c ← read (hdr + 1)
  ensure hdr n c >>= fun _ => append hdr n v

/-- Pop: an empty stack returns `none`; otherwise read the top item and decrement the count. -/
def pop : Prog (Option ℕ) := do
  let n ← read hdr
  if n = 0 then pure none else do
    let p ← read (hdr + 2)
    let v ← read (p + (n - 1))
    write hdr (n - 1)
    pure (some v)

/-- Size: read the count. -/
def size : Prog ℕ := read hdr

/-- The stack operations as memory programs. -/
def methods (w C : ℕ) : Methods (Stack.WordRAM.spec w C) (Memory.spec w)
  | .push v => push hdr v
  | .pop => pop hdr
  | .size => size hdr

/-! ## Evaluation -/

variable {w : ℕ}

/-- The memory after growing a full array of `n` items. -/
def grown (n : ℕ) (s : State) : State :=
  ⟨Function.update (Function.update (copyPrefix s.mem (base hdr s) s.frontier n) (hdr + 2)
    s.frontier) (hdr + 1) (2 * n), s.frontier + 2 * n⟩

/-- Growing moves the items to a fresh array of twice the size. -/
theorem clientState_grow (n : ℕ) (s : State) (h : base hdr s + n ≤ s.frontier) :
    (spec w).clientState s (grow hdr n) = grown hdr n s := by
  change (spec w).clientState ⟨s.mem, s.frontier + 2 * n⟩
      (copy (s.mem (hdr + 2)) s.frontier n >>= fun _ =>
        write (hdr + 2) s.frontier >>= fun _ => write (hdr + 1) (2 * n)) = _
  rw [(spec w).clientState_bind,
    clientState_copy (s.mem (hdr + 2)) s.frontier n ⟨s.mem, s.frontier + 2 * n⟩ (.inl h)]
  rfl

/-- Growing costs `4 + 2 n` memory units. -/
theorem totalCost_grow (n : ℕ) (s : State) :
    (spec w).totalCost charge s ((spec w).clientHistory s (grow hdr n)) = 4 + 2 * n := by
  change 1 + (1 + (spec w).totalCost charge ⟨s.mem, s.frontier + 2 * n⟩
      ((spec w).clientHistory ⟨s.mem, s.frontier + 2 * n⟩
        (copy (s.mem (hdr + 2)) s.frontier n >>= fun _ =>
          write (hdr + 2) s.frontier >>= fun _ => write (hdr + 1) (2 * n)))) = _
  rw [(spec w).clientHistory_bind, StateTransitionSpec.totalCost_append, totalCost_copy]
  change 1 + (1 + (2 * n + 2)) = _
  omega

/-- Growing is admissible when the old array is allocated and holds words, and the new frontier
fits a word. -/
theorem validHistory_grow (n : ℕ) (s : State) (hh : hdr + 3 ≤ s.frontier)
    (h : base hdr s + n ≤ s.frontier) (hfit : Fits w (s.frontier + 2 * n))
    (hitems : ∀ i < n, Fits w (s.mem (base hdr s + i))) :
    (spec w).ValidHistory s ((spec w).clientHistory s (grow hdr n)) := by
  change hdr + 2 < s.frontier ∧ Fits w (s.frontier + 2 * n) ∧
    (spec w).ValidHistory ⟨s.mem, s.frontier + 2 * n⟩
      ((spec w).clientHistory ⟨s.mem, s.frontier + 2 * n⟩
        (copy (s.mem (hdr + 2)) s.frontier n >>= fun _ =>
          write (hdr + 2) s.frontier >>= fun _ => write (hdr + 1) (2 * n)))
  rw [(spec w).clientHistory_bind, StateTransitionSpec.validHistory_append,
    StateTransitionSpec.run_runClient,
    clientState_copy (s.mem (hdr + 2)) s.frontier n ⟨s.mem, s.frontier + 2 * n⟩ (.inl h)]
  refine ⟨by omega, hfit, validHistory_copy _ _ _ ⟨s.mem, s.frontier + 2 * n⟩ (.inl h)
    (show base hdr s + n ≤ s.frontier + 2 * n by omega)
    (show s.frontier + n ≤ s.frontier + 2 * n by omega) hitems, ?_⟩
  change (hdr + 2 < s.frontier + 2 * n ∧ Fits w s.frontier) ∧
    (hdr + 1 < s.frontier + 2 * n ∧ Fits w (2 * n)) ∧ True
  exact ⟨⟨by omega, hfit.of_le (by omega)⟩, ⟨by omega, hfit.of_le (by omega)⟩, trivial⟩

/-- Appending reads the base, writes the item and the new count. -/
theorem runClient_append (n v : ℕ) (s : State) :
    (spec w).runClient s (append hdr n v) =
      ((), ⟨Function.update (Function.update s.mem (base hdr s + n) v) hdr (n + 1), s.frontier⟩,
        [.read (hdr + 2), .write (base hdr s + n) v, .write hdr (n + 1)]) := rfl

/-- A push into an array with room reads the count and capacity, then appends. -/
theorem runClient_push_not_full (v : ℕ) (s : State) (h : count hdr s ≠ capacity hdr s) :
    (spec w).runClient s (push hdr v) =
      ((), ⟨Function.update (Function.update s.mem (base hdr s + count hdr s) v) hdr
          (count hdr s + 1), s.frontier⟩,
        [.read hdr, .read (hdr + 1), .read (hdr + 2), .write (base hdr s + count hdr s) v,
          .write hdr (count hdr s + 1)]) := by
  have he : ensure hdr (count hdr s) (capacity hdr s) = pure () := by
    simp only [ensure, h, ↓reduceIte]
  unfold push
  simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.stepFn, step_read]
  rw [show ensure hdr (s.mem hdr) (s.mem (hdr + 1)) = pure () from he]
  rfl

/-- A push into a full array grows it, then appends. -/
theorem push_full_eq (v : ℕ) (s : State) (h : count hdr s = capacity hdr s) :
    (spec w).clientState s (push hdr v) =
        (spec w).clientState s (grow hdr (count hdr s) >>= fun _ => append hdr (count hdr s) v) ∧
      (spec w).clientHistory s (push hdr v) =
        .read hdr :: .read (hdr + 1) ::
          (spec w).clientHistory s (grow hdr (count hdr s) >>= fun _ =>
            append hdr (count hdr s) v) := by
  have he : ensure hdr (count hdr s) (capacity hdr s) = grow hdr (count hdr s) := by
    simp only [ensure, h, ↓reduceIte]
  exact ⟨by
    change (spec w).clientState s (ensure hdr (count hdr s) (capacity hdr s) >>= fun _ =>
      append hdr (count hdr s) v) = _
    rw [he], by
    change _ :: _ :: (spec w).clientHistory s (ensure hdr (count hdr s) (capacity hdr s) >>=
      fun _ => append hdr (count hdr s) v) = _
    rw [he]⟩

/-- A pop from an empty stack reads the count only. -/
theorem runClient_pop_of_eq_zero (s : State) (h : count hdr s = 0) :
    (spec w).runClient s (pop hdr) = (none, s, [.read hdr]) := by
  simp only [count] at h
  simp [pop, h]

/-- A pop from a nonempty stack reads the count, the base and the top item, and writes the new
count. -/
theorem runClient_pop_of_ne_zero (s : State) (h : count hdr s ≠ 0) :
    (spec w).runClient s (pop hdr) =
      (some (s.mem (base hdr s + (count hdr s - 1))),
        ⟨Function.update s.mem hdr (count hdr s - 1), s.frontier⟩,
        [.read hdr, .read (hdr + 2), .read (base hdr s + (count hdr s - 1)),
          .write hdr (count hdr s - 1)]) := by
  simp only [count] at h
  unfold pop
  simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.stepFn, step_read, h,
    ↓reduceIte]
  rfl

/-- A size query reads the count. -/
theorem runClient_size (s : State) :
    (spec w).runClient s (size hdr) = (count hdr s, s, [.read hdr]) := rfl


/-! ## The operations' effects -/

variable {hdr} {C : ℕ}

/-- The stored stack lists the first `count` items of the array, top first. -/
theorem abs_eq (s : State) :
    abs hdr s = ((List.range (count hdr s)).map fun i => s.mem (base hdr s + i)).reverse := rfl

/-- The stack has as many elements as the count. -/
@[simp] theorem length_abs (s : State) : (abs hdr s).length = count hdr s := by simp [abs]

/-- Two states whose counts agree and whose arrays agree up to the count store the same stack. -/
theorem abs_congr {s s' : State} (hn : count hdr s' = count hdr s)
    (h : ∀ i < count hdr s, s'.mem (base hdr s' + i) = s.mem (base hdr s + i)) :
    abs hdr s' = abs hdr s := by
  rw [abs_eq, abs_eq, hn, List.map_congr_left fun i hi => h i (List.mem_range.mp hi)]

/-- A state with one more item `v` on top stores `v` on top of the stack. -/
theorem abs_push {s s' : State} (hn : count hdr s' = count hdr s + 1)
    (h : ∀ i < count hdr s, s'.mem (base hdr s' + i) = s.mem (base hdr s + i))
    {v : ℕ} (hv : s'.mem (base hdr s' + count hdr s) = v) :
    abs hdr s' = v :: abs hdr s := by
  rw [abs_eq, abs_eq, hn, List.range_succ, List.map_append, List.map_singleton, hv,
    List.reverse_append, List.map_congr_left fun i hi => h i (List.mem_range.mp hi)]
  rfl

/-- A push into an array with room writes the item and the count, and keeps the rest. -/
theorem push_not_full {s : State} (hs : Inv hdr w C s) (h : count hdr s ≠ capacity hdr s)
    (v : ℕ) :
    count hdr ((spec w).clientState s (push hdr v)) = count hdr s + 1 ∧
      capacity hdr ((spec w).clientState s (push hdr v)) = capacity hdr s ∧
      base hdr ((spec w).clientState s (push hdr v)) = base hdr s ∧
      ((spec w).clientState s (push hdr v)).frontier = s.frontier ∧
      ((spec w).clientState s (push hdr v)).mem (base hdr s + count hdr s) = v ∧
      ∀ a, a ≠ hdr → a ≠ base hdr s + count hdr s →
        ((spec w).clientState s (push hdr v)).mem a = s.mem a := by
  have hb := hs.header_le
  simp only [StateTransitionSpec.clientState, runClient_push_not_full hdr v s h, count, capacity,
    base] at hb ⊢
  refine ⟨by simp, ?_, ?_, trivial, ?_, fun a ha ha' => ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne ha, Function.update_of_ne ha']

/-- After growing, the array starts at the old frontier. -/
theorem base_grown (n : ℕ) (s : State) : base hdr (grown hdr n s) = s.frontier := by
  simp only [base, grown]
  rw [Function.update_of_ne (by omega), Function.update_self]

/-- A push into a full array moves the items to a fresh array of twice the capacity at the
frontier, writes the item and the count, and keeps every other allocated cell. -/
theorem push_full {s : State} (hs : Inv hdr w C s) (h : count hdr s = capacity hdr s)
    (v : ℕ) :
    count hdr ((spec w).clientState s (push hdr v)) = count hdr s + 1 ∧
      capacity hdr ((spec w).clientState s (push hdr v)) = 2 * count hdr s ∧
      base hdr ((spec w).clientState s (push hdr v)) = s.frontier ∧
      ((spec w).clientState s (push hdr v)).frontier = s.frontier + 2 * count hdr s ∧
      ((spec w).clientState s (push hdr v)).mem (s.frontier + count hdr s) = v ∧
      (∀ i < count hdr s,
        ((spec w).clientState s (push hdr v)).mem (s.frontier + i) = s.mem (base hdr s + i)) ∧
      ∀ a < s.frontier, a ≠ hdr → a ≠ hdr + 1 → a ≠ hdr + 2 →
        ((spec w).clientState s (push hdr v)).mem a = s.mem a := by
  have hb := hs.header_le
  have hi := hs.items_le
  rw [(push_full_eq hdr v s h).1, (spec w).clientState_bind,
    clientState_grow hdr _ s (by rw [h]; exact hi)]
  simp only [StateTransitionSpec.clientState, runClient_append, base_grown]
  simp only [grown, count, capacity, base] at hb hi h ⊢
  have h1 := hs.one_le_capacity
  simp only [capacity] at h1
  refine ⟨by simp, ?_, ?_, trivial, ?_, fun i hi' => ?_, fun a ha h₀ h₁ h₂ => ?_⟩ <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_self, copyPrefix_read,
      copyPrefix_outside]

/-- A push into a full array of `n` items costs `9 + 2 n` memory units. -/
theorem totalCost_push_full {s : State} (h : count hdr s = capacity hdr s) (v : ℕ) :
    (spec w).totalCost charge s ((spec w).clientHistory s (push hdr v)) = 9 + 2 * count hdr s := by
  rw [(push_full_eq hdr v s h).2, (spec w).clientHistory_bind]
  change 1 + (1 + (spec w).totalCost charge s (_ ++ _)) = _
  rw [StateTransitionSpec.totalCost_append, totalCost_grow, StateTransitionSpec.run_runClient]
  change 1 + (1 + (4 + 2 * count hdr s + 3)) = _
  omega

/-- A push of a word into a full array is admissible when twice its capacity fits the room. -/
theorem validHistory_push_full {s : State} (hs : Inv hdr w C s)
    (h : count hdr s = capacity hdr s) {v : ℕ} (hv : Fits w v)
    (hroom : 2 * count hdr s ≤ room hdr C s) :
    (spec w).ValidHistory s ((spec w).clientHistory s (push hdr v)) := by
  have hb := hs.header_le
  have hi := hs.items_le
  have h1 := hs.one_le_capacity
  have hfit : Fits w (s.frontier + 2 * count hdr s) := hs.fits_room.of_le (by omega)
  rw [(push_full_eq hdr v s h).2, (spec w).clientHistory_bind]
  refine ⟨by simp only [valid_read, base] at hb hi ⊢; omega,
    by simp only [StateTransitionSpec.stepFn, step_read, valid_read, base] at hb hi ⊢; omega, ?_⟩
  change (spec w).ValidHistory s (_ ++ _)
  rw [StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient,
    clientState_grow hdr _ s (by rw [h]; exact hi)]
  refine ⟨validHistory_grow hdr _ s (by omega) (by rw [h]; exact hi) hfit
    fun i hi' => hs.items_fit i hi', ?_⟩
  simp only [StateTransitionSpec.clientHistory, runClient_append, base_grown]
  change hdr + 2 < s.frontier + 2 * count hdr s ∧
    (s.frontier + count hdr s < s.frontier + 2 * count hdr s ∧ Fits w v) ∧
    (hdr < s.frontier + 2 * count hdr s ∧ Fits w (count hdr s + 1)) ∧ True
  simp only [base, capacity, count] at hb hi h1 h ⊢
  exact ⟨by omega, ⟨by omega, hv⟩, ⟨by omega, hfit.of_le (by omega)⟩, trivial⟩

/-- A pop from a nonempty stack decrements the count and keeps the rest. -/
theorem pop_of_ne_zero {s : State} (h : count hdr s ≠ 0) :
    count hdr ((spec w).clientState s (pop hdr)) = count hdr s - 1 ∧
      capacity hdr ((spec w).clientState s (pop hdr)) = capacity hdr s ∧
      base hdr ((spec w).clientState s (pop hdr)) = base hdr s ∧
      ((spec w).clientState s (pop hdr)).frontier = s.frontier ∧
      ∀ a, a ≠ hdr → ((spec w).clientState s (pop hdr)).mem a = s.mem a := by
  simp only [StateTransitionSpec.clientState, runClient_pop_of_ne_zero hdr s h, count, capacity,
    base]
  exact ⟨by simp, Function.update_of_ne (by omega) _ _, Function.update_of_ne (by omega) _ _,
    trivial, fun a ha => Function.update_of_ne ha _ _⟩


/-! ## The refinement -/

/-- The header is allocated. -/
theorem Inv.header_lt {s : State} (hs : Inv hdr w C s) : hdr + 3 ≤ s.frontier :=
  hs.header_le.trans ((Nat.le_add_right _ _).trans hs.items_le)

/-- The frontier fits a word. -/
theorem Inv.fits_frontier {s : State} (hs : Inv hdr w C s) : Fits w s.frontier :=
  hs.fits_room.of_le (Nat.le_add_right _ _)

/-- The stack before a pop is the popped item on top of the stack after it. -/
theorem abs_of_ne_zero {s : State} (hs : Inv hdr w C s) (h : count hdr s ≠ 0) :
    abs hdr s = s.mem (base hdr s + (count hdr s - 1)) ::
      abs hdr ((spec w).clientState s (pop hdr)) := by
  obtain ⟨hn, -, hb, -, hmem⟩ := pop_of_ne_zero (w := w) h
  have hh := hs.header_le
  refine abs_push (by omega) (fun i _ => ?_) (by rw [hn])
  rw [hb, hmem _ (by omega)]

/-- **The doubling array implements the bounded stack.** -/
def refinement (hdr w C : ℕ) : Refinement (Stack.WordRAM.spec w C) (Memory.spec w) :=
  Refinement.ofFn (methods hdr w C) (Inv hdr w C) (abs hdr)
    (by
      intro s o hs hv
      have hh := hs.header_lt
      have hb := hs.header_le
      have hi := hs.items_le
      have hc := hs.count_le
      have hf := hs.fits_frontier
      cases o with
      | push v =>
        obtain ⟨hlen, hfit⟩ := hv
        rw [length_abs] at hlen
        by_cases heq : count hdr s = capacity hdr s
        · exact validHistory_push_full hs heq hfit (by simp only [room]; omega)
        · simp only [methods, StateTransitionSpec.clientHistory,
            runClient_push_not_full hdr v s heq, StateTransitionSpec.validHistory_cons,
            StateTransitionSpec.stepFn, step_read, step_write, valid_read, valid_write]
          exact ⟨by omega, by omega, by omega, ⟨by omega, hfit⟩, ⟨by omega, hf.of_le (by omega)⟩,
            trivial⟩
      | pop =>
        by_cases h0 : count hdr s = 0
        · simp only [methods, StateTransitionSpec.clientHistory, runClient_pop_of_eq_zero hdr s h0,
            StateTransitionSpec.validHistory_cons, valid_read]
          exact ⟨by omega, trivial⟩
        · simp only [methods, StateTransitionSpec.clientHistory,
            runClient_pop_of_ne_zero hdr s h0, StateTransitionSpec.validHistory_cons,
            StateTransitionSpec.stepFn, step_read, step_write, valid_read, valid_write]
          exact ⟨by omega, by omega, by omega, ⟨by omega, hf.of_le (by omega)⟩, trivial⟩
      | size =>
        simp only [methods, StateTransitionSpec.clientHistory, runClient_size,
          StateTransitionSpec.validHistory_cons, valid_read]
        exact ⟨by omega, trivial⟩)
    (by
      intro s o hs hv
      have hb := hs.header_le
      have hi := hs.items_le
      have hc := hs.count_le
      have h1 := hs.one_le_capacity
      cases o with
      | push v =>
        obtain ⟨hlen, hfit⟩ := hv
        rw [length_abs] at hlen
        simp only [methods]
        by_cases heq : count hdr s = capacity hdr s
        · obtain ⟨hn, hcap, hbase, hfr, hv', hcopy, -⟩ := push_full hs heq v
          refine ⟨?_, ⟨by omega, by omega, by omega, by omega, ?_, fun i hi' => ?_⟩⟩
          · change (v :: abs hdr s, ()) = (abs hdr ((spec w).clientState s (push hdr v)), ())
            rw [abs_push hn (fun i hi' => by rw [hbase, hcopy i hi']) (by rw [hbase, hv'])]
          · rw [hfr]
            exact hs.fits_room.of_le (by simp only [room] at *; omega)
          · rw [hbase]
            rcases Nat.lt_succ_iff_lt_or_eq.mp (hn ▸ hi') with hi' | rfl
            · rw [hcopy i hi']
              exact hs.items_fit i hi'
            · rwa [hv']
        · obtain ⟨hn, hcap, hbase, hfr, hv', hmem⟩ := push_not_full hs heq v
          have hlt : count hdr s < capacity hdr s := Nat.lt_of_le_of_ne hc heq
          have hold : ∀ i < count hdr s, ((spec w).clientState s (push hdr v)).mem
              (base hdr s + i) = s.mem (base hdr s + i) := fun i hi' => hmem _ (by omega) (by omega)
          refine ⟨?_, ⟨by omega, by omega, by omega, by omega, ?_, fun i hi' => ?_⟩⟩
          · change (v :: abs hdr s, ()) = (abs hdr ((spec w).clientState s (push hdr v)), ())
            rw [abs_push hn (fun i hi' => by rw [hbase]; exact hold i hi') (by rw [hbase, hv'])]
          · rw [hfr, show room hdr C ((spec w).clientState s (push hdr v)) =
              room hdr C s by simp only [room]; rw [hcap]]
            exact hs.fits_room
          · rw [hbase]
            rcases Nat.lt_succ_iff_lt_or_eq.mp (hn ▸ hi') with hi' | rfl
            · rw [hold i hi']
              exact hs.items_fit i hi'
            · rwa [hv']
      | pop =>
        by_cases h0 : count hdr s = 0
        · simp only [methods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
            runClient_pop_of_eq_zero hdr s h0]
          have he : abs hdr s = [] := List.eq_nil_of_length_eq_zero (by simp [h0])
          simp [he, hs]
        · obtain ⟨hn, hcap, hbase, hfr, hmem⟩ := pop_of_ne_zero (w := w) h0
          simp only [methods]
          refine ⟨?_, ⟨by rw [hbase]; omega, by rw [hbase, hcap, hfr]; omega, by omega,
            by omega, ?_, fun i hi' => ?_⟩⟩
          · rw [abs_of_ne_zero hs h0]
            simp only [StateTransitionSpec.clientResult, runClient_pop_of_ne_zero hdr s h0]
            rfl
          · rw [hfr, show room hdr C ((spec w).clientState s (pop hdr)) = room hdr C s by
              simp only [room]; rw [hcap]]
            exact hs.fits_room
          · rw [hbase, hmem _ (by omega)]
            exact hs.items_fit i (by omega)
      | size =>
        simp only [methods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
          runClient_size]
        exact ⟨by simp, hs⟩)


/-! ## The frame: footprint and room -/

/-- The footprint is the header and the item array. -/
theorem mem_footprint {s : State} {a : ℕ} :
    a ∈ footprint hdr s ↔
      (hdr ≤ a ∧ a < hdr + 3) ∨ (base hdr s ≤ a ∧ a < base hdr s + capacity hdr s) := by
  simp [footprint, items, Block.mem_footprint, Block.Owns]

/-- The invariant, the abstraction, the footprint and the room read only the footprint, and
survive a growing frontier that leaves the room fitting a word. -/
theorem congr {s s' : State} (hs : Inv hdr w C s)
    (h : ∀ a ∈ footprint hdr s, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier)
    (hroom : Fits w (s'.frontier + room hdr C s)) :
    Inv hdr w C s' ∧ abs hdr s' = abs hdr s ∧ footprint hdr s' = footprint hdr s ∧
      room hdr C s' = room hdr C s := by
  have hn : count hdr s' = count hdr s := h _ (mem_footprint.mpr (.inl (by omega)))
  have hcap : capacity hdr s' = capacity hdr s := h _ (mem_footprint.mpr (.inl (by omega)))
  have hbase : base hdr s' = base hdr s := h _ (mem_footprint.mpr (.inl (by omega)))
  have hitem : ∀ i < capacity hdr s, s'.mem (base hdr s + i) = s.mem (base hdr s + i) :=
    fun i hi => h _ (mem_footprint.mpr (.inr (by omega)))
  have hc := hs.count_le
  have hroom' : room hdr C s' = room hdr C s := by simp only [room, hcap]
  refine ⟨⟨by rw [hbase]; exact hs.header_le, by rw [hbase, hcap]; exact hs.items_le.trans hf,
    by rw [hcap]; exact hs.one_le_capacity, by rw [hn, hcap]; exact hc, by rwa [hroom'],
    fun i hi => ?_⟩, abs_congr hn fun i hi => by rw [hbase, hitem i (by omega)], ?_, hroom'⟩
  · rw [hn] at hi
    rw [hbase, hitem i (by omega)]
    exact hs.items_fit i hi
  · simp only [footprint, items, hbase, hcap]

/-- Each admissible operation changes no allocated cell outside the footprint, grows the
footprint only into fresh cells, and advances the frontier by at most the room it gives up. -/
theorem modifies_methods {s : State} (hs : Inv hdr w C s) (o : StackOp ℕ)
    (hv : (Stack.WordRAM.spec w C).valid (abs hdr s) o) :
    (∀ b < s.frontier, b ∉ footprint hdr s →
        ((spec w).clientState s (methods hdr w C o)).mem b = s.mem b) ∧
      (∀ b ∈ footprint hdr ((spec w).clientState s (methods hdr w C o)),
        b ∈ footprint hdr s ∨ s.frontier ≤ b) ∧
      ((spec w).clientState s (methods hdr w C o)).frontier +
          room hdr C ((spec w).clientState s (methods hdr w C o)) ≤
        s.frontier + room hdr C s := by
  have hc := hs.count_le
  cases o with
  | push v =>
    obtain ⟨hlen, -⟩ := hv
    rw [length_abs] at hlen
    simp only [methods]
    by_cases heq : count hdr s = capacity hdr s
    · obtain ⟨hn, hcap, hbase, hfr, -, -, hrest⟩ := push_full hs heq v
      refine ⟨fun b hb hb' => hrest b hb ?_ ?_ ?_, fun b hb => ?_, ?_⟩
      · exact fun h => hb' (mem_footprint.mpr (.inl (by omega)))
      · exact fun h => hb' (mem_footprint.mpr (.inl (by omega)))
      · exact fun h => hb' (mem_footprint.mpr (.inl (by omega)))
      · rcases mem_footprint.mp hb with hb | hb
        · exact .inl (mem_footprint.mpr (.inl hb))
        · exact .inr (by omega)
      · simp only [room, hcap, hfr]
        omega
    · obtain ⟨hn, hcap, hbase, hfr, -, hmem⟩ := push_not_full hs heq v
      have hlt : count hdr s < capacity hdr s := Nat.lt_of_le_of_ne hc heq
      refine ⟨fun b _ hb' => hmem b ?_ ?_, fun b hb => .inl ?_, ?_⟩
      · exact fun h => hb' (mem_footprint.mpr (.inl (by omega)))
      · exact fun h => hb' (mem_footprint.mpr (.inr (by omega)))
      · simpa only [footprint, items, hbase, hcap] using hb
      · simp only [room, hcap, hfr, le_refl]
  | pop =>
    simp only [methods]
    by_cases h0 : count hdr s = 0
    · have hs' : (spec w).clientState s (pop hdr) = s := by
        simp only [StateTransitionSpec.clientState, runClient_pop_of_eq_zero hdr s h0]
      rw [hs']
      exact ⟨fun _ _ _ => rfl, fun _ hb => .inl hb, le_rfl⟩
    · obtain ⟨hn, hcap, hbase, hfr, hmem⟩ := pop_of_ne_zero (w := w) h0
      refine ⟨fun b _ hb' => hmem b fun h => hb' (mem_footprint.mpr (.inl (by omega))),
        fun b hb => .inl ?_, ?_⟩
      · simpa only [footprint, items, hbase, hcap] using hb
      · simp only [room, hcap, hfr, le_refl]
  | size => exact ⟨fun _ _ _ => rfl, fun _ hb => .inl hb, le_rfl⟩

/-- **The doubling stack, framed** by its header and current array, with the room its growth may
still allocate. -/
def framed (hdr w C : ℕ) : Memory.Framed (Stack.WordRAM.spec w C) w where
  toRefinement := refinement hdr w C
  footprint := footprint hdr
  room := room hdr C
  lt_frontier {s a} hs ha := by
    have hi := hs.items_le
    have hh := hs.header_le
    rcases mem_footprint.mp ha with ha | ha <;> omega
  congr hs h hf hr := congr hs h hf hr
  modifies {s} o {a s' tr} hs hv hrun := by
    obtain ⟨_, _, rfl, _⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
    exact modifies_methods hs o hv

/-- The potential reads only the header. -/
theorem local_potential : (framed hdr w C).Local (potential hdr) := fun hs h hf hr => by
  have hn : count hdr _ = count hdr _ := h _ (mem_footprint.mpr (.inl (by omega)))
  have hcap : capacity hdr _ = capacity hdr _ := h _ (mem_footprint.mpr (.inl (by omega)))
  simp only [potential, hn, hcap]

/-- **Every operation costs at most thirteen memory units, amortized**: a push into a full array
of `n` items costs `9 + 2 n` and releases the potential `2 n` that the last `n / 2` pushes
saved. -/
theorem amortized : (framed hdr w C).Amortized charge (fun _ _ => 13) (potential hdr) := by
  apply Refinement.Amortized.ofFn
  intro s o hs hv
  change Inv hdr w C s at hs
  have hc := hs.count_le
  cases o with
  | push v =>
    change (spec w).totalCost charge s ((spec w).clientHistory s (push hdr v)) +
      potential hdr ((spec w).clientState s (push hdr v)) ≤ 13 + potential hdr s
    by_cases heq : count hdr s = capacity hdr s
    · obtain ⟨hn, hcap, -⟩ := push_full hs heq v
      rw [totalCost_push_full heq]
      simp only [potential, hn, hcap]
      omega
    · obtain ⟨hn, hcap, -⟩ := push_not_full hs heq v
      simp only [StateTransitionSpec.clientHistory, runClient_push_not_full hdr v s heq]
      simp only [StateTransitionSpec.clientState, runClient_push_not_full hdr v s heq] at hn hcap
      simp only [StateTransitionSpec.clientState, runClient_push_not_full hdr v s heq, potential,
        hn, hcap, StateTransitionSpec.totalCost_cons, charge_read, charge_write,
        StateTransitionSpec.totalCost_nil]
      omega
  | pop =>
    change (spec w).totalCost charge s ((spec w).clientHistory s (pop hdr)) +
      potential hdr ((spec w).clientState s (pop hdr)) ≤ 13 + potential hdr s
    by_cases h0 : count hdr s = 0
    · simp [StateTransitionSpec.clientHistory, StateTransitionSpec.clientState,
        runClient_pop_of_eq_zero hdr s h0]
    · obtain ⟨hn, hcap, -⟩ := pop_of_ne_zero (w := w) h0
      simp only [potential, hn, hcap]
      simp only [StateTransitionSpec.clientHistory, runClient_pop_of_ne_zero hdr s h0,
        StateTransitionSpec.totalCost_cons, charge_read, charge_write,
        StateTransitionSpec.totalCost_nil]
      omega
  | size =>
    change (spec w).totalCost charge s ((spec w).clientHistory s (size hdr)) +
      potential hdr ((spec w).clientState s (size hdr)) ≤ 13 + potential hdr s
    simp [StateTransitionSpec.clientHistory, StateTransitionSpec.clientState, runClient_size]


/-! ## Allocation -/

/-- Allocate an empty doubling stack: a zeroed header of three cells, then an item array of one
cell, recorded in the header. Returns the header's address. -/
def create : Prog ℕ := do
  let h ← Memory.alloc 3
  let p ← allocDirty 1
  write (h + 1) 1
  write (h + 2) p
  pure h

/-- Creation allocates the header at the frontier and the array of one cell above it. -/
theorem runClient_create (s : State) :
    (spec w).runClient s create =
      (s.frontier, ⟨Function.update (Function.update (clear s.mem s.frontier 3) (s.frontier + 1) 1)
          (s.frontier + 2) (s.frontier + 3), s.frontier + 3 + 1⟩,
        [.alloc 3, .allocDirty 1, .write (s.frontier + 1) 1,
          .write (s.frontier + 2) (s.frontier + 3)]) := rfl

/-- The header of a created stack: no items, capacity one, and the array just above. -/
theorem create_header (s : State) :
    count s.frontier ((spec w).clientState s create) = 0 ∧
      capacity s.frontier ((spec w).clientState s create) = 1 ∧
      base s.frontier ((spec w).clientState s create) = s.frontier + 3 := by
  simp only [StateTransitionSpec.clientState, runClient_create, count, capacity, base]
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      clear_of_owns (show s.frontier ≤ s.frontier ∧ s.frontier < s.frontier + 3 by omega)]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_self]

/-- **The doubling stack as an allocator**: an empty stack in four cells at a memory cost of
seven units, reserving `4 C + 4` cells for itself and its growth to capacity `2 C`. -/
def allocator (w C : ℕ) : Allocator (Stack.WordRAM.spec w C) w where
  Handle := ℕ
  alloc := create
  methods hdr := methods hdr w C
  init := []
  room := 4 * C + 4
  cost := 7
  framed s _ _ := framed s.frontier w C
  allocates s _ hroom := by
    obtain ⟨hn, hcap, hbase⟩ := create_header (w := w) s
    have hfr : ((spec w).clientState s create).frontier = s.frontier + 3 + 1 := rfl
    refine
      { validHistory := ?_, cost_le := ?_, mem_eq := ?_, methods_eq := rfl, inv := ?_,
        abs_eq := ?_, of_mem_footprint := ?_, room_le := ?_ }
    · simp only [StateTransitionSpec.clientHistory, runClient_create,
        StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, step_alloc,
        step_allocDirty, step_write, valid_alloc, valid_allocDirty, valid_write]
      exact ⟨hroom.of_le (by omega), hroom.of_le (by omega), ⟨by omega, hroom.of_le (by omega)⟩,
        ⟨by omega, hroom.of_le (by omega)⟩, trivial⟩
    · simp [StateTransitionSpec.clientHistory, runClient_create]
    · intro a ha
      simp only [StateTransitionSpec.clientState, runClient_create]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        clear_of_not_owns (by simp only [Block.Owns]; omega)]
    · refine ⟨by rw [hbase], by rw [hbase, hcap, hfr], by rw [hcap], by rw [hn, hcap]; omega, ?_,
        fun i hi => by rw [hn] at hi; omega⟩
      rw [hfr]
      exact hroom.of_le (by simp only [room, hcap]; omega)
    · exact List.eq_nil_of_length_eq_zero (by change (abs _ _).length = 0; rw [length_abs, hn])
    · intro a ha
      change a ∈ footprint _ _ at ha
      right
      rcases mem_footprint.mp ha with ha | ha <;> omega
    · change ((spec w).clientState s create).frontier +
        room s.frontier C ((spec w).clientState s create) ≤ s.frontier + (4 * C + 4)
      simp only [room, hcap, hfr]
      omega

/-- The allocated stack is empty. -/
@[simp] theorem init_allocator (w C : ℕ) : (allocator w C).init = [] := rfl

/-- **The allocator's cost certificate**: thirteen memory units per operation, amortized, and no
potential once allocated. -/
theorem amortized_allocator : (allocator w C).Amortized (fun _ _ => 13) 0 := by
  intro s _ _
  obtain ⟨hn, hcap, -⟩ := create_header (w := w) s
  refine ⟨potential s.frontier, amortized, local_potential, ?_⟩
  change potential s.frontier ((spec w).clientState s create) ≤ 0
  simp only [potential, hn, hcap]
  omega

end Cslib.DataStructure.Stack.Doubling
