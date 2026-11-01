/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Field
public import Complexity.DataStructure.StateTransition.Refinement
public import Complexity.DataStructure.Stack.WordRAM.Basic

/-!
# An array stack over the memory oracle

The bounded stack `Stack.WordRAM.spec w C` is implemented by three short programs over
`Memory.spec w`. The storage is a `Layout` with two named fields: a one-cell `count` and an
`items` array of `C` cells, bottom first. The abstraction function reads the first `count` items
and reverses them, so the top comes first. Each operation is one read, two writes at most, and a
single branch; its evaluation is definitional (`runClient_push`, `runClient_pop_of_pos`, …), and
the refinement obligations follow from those equations and the list view of the array.

Every operation costs at most three memory units, with no potential (`amortized`). The methods
write only the layout's cells and never allocate (`modifies_methods`), and the abstraction and
invariant depend only on those cells (`abs_congr`, `Inv.congr`). Two stacks with disjoint
layouts therefore implement the product of two stacks (`pairRefinement`).

This is the same specification that `Stack.WordRAM` implements by a hand-stepped nine-register
dispatcher. Here no register, instruction count or word-fit chain appears; fits enter only
through the admissibility of `Memory.spec w`.

## Main definitions

* `Layout`, `Layout.footprint`, `Layout.Valid`: the two fields, the cells they own, and their
  static well-formedness.
* `push`, `pop`, `size`, `methods`: the operations as memory programs.
* `abs`, `Inv`: the abstraction function and the implementation invariant.
* `refinement`: the array stack as a `Refinement` of the bounded stack.
* `pairMethods`, `pairRefinement`: two array stacks with disjoint layouts implement the pair of
  stacks.
* `allocLayout`: allocate an empty stack.

## Main results

* `amortized`: every operation costs at most three memory units.
* `pair_amortized`: so does every operation of the pair.
* `pairRefinement_methods`: the pair's methods do not depend on the proofs about its layouts.
* `modifies_methods`, `abs_congr`, `Inv.congr`: the frame of a stack.
* `runClient_allocLayout_bind`, `inv_allocLayout`, `abs_allocLayout`: allocation yields an empty
  stack in three memory units.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Stack.Memory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Queue

/-- The storage of an array stack: a one-cell field holding the number of items, and the item
array, bottom first. -/
structure Layout where
  /-- One cell holding the number of stored items. -/
  count : Block
  /-- The items, bottom first. -/
  items : Block

namespace Layout

/-- The cells a stack owns. -/
def footprint (L : Layout) : Finset ℕ := L.count.footprint ∪ L.items.footprint

/-- Static well-formedness for capacity `C` at word size `w`: the count field is one cell outside
the item array, the array has `C` cells, and `C` fits a word. -/
structure Valid (L : Layout) (w C : ℕ) : Prop where
  /-- The count field is one cell. -/
  count_length : L.count.length = 1
  /-- The count cell is not an item. -/
  count_not_owns : ¬L.items.Owns L.count.base
  /-- The item array has the capacity. -/
  items_length : L.items.length = C
  /-- The capacity fits a word, so every count does. -/
  capacity_fits : Fits w C

/-- The count cell belongs to the footprint. -/
theorem count_mem_footprint (L : Layout) (hL : L.count.length = 1) :
    L.count.base ∈ L.footprint :=
  Finset.mem_union_left _ (Block.mem_footprint.mpr ⟨le_rfl, by omega⟩)

/-- Every item cell belongs to the footprint. -/
theorem item_mem_footprint (L : Layout) {i : ℕ} (hi : i < L.items.length) :
    L.items.base + i ∈ L.footprint :=
  Finset.mem_union_right _ (Block.mem_footprint.mpr (Block.owns_add hi))

end Layout

variable (L : Layout)

/-- Push: write the item above the top, then increment the count. -/
def push (v : ℕ) : Prog Unit := do
  let n ← L.count.get 0
  L.items.set n v
  L.count.set 0 (n + 1)

/-- Pop: an empty stack returns `none`; otherwise read the top item and decrement the count. -/
def pop : Prog (Option ℕ) := do
  let n ← L.count.get 0
  if n = 0 then pure none else do
    let v ← L.items.get (n - 1)
    L.count.set 0 (n - 1)
    pure (some v)

/-- Size: read the count. -/
def size : Prog ℕ := L.count.get 0

/-- The stack operations as memory programs. -/
def methods (w C : ℕ) : Methods (Stack.WordRAM.spec w C) (Memory.spec w)
  | .push v => push L v
  | .pop => pop L
  | .size => size L

/-- The stored stack, top first: the first `count` items, reversed. -/
def abs (s : Memory.State) : List ℕ := (L.items.entries (s.mem L.count.base) s.mem).reverse

/-- The implementation invariant: both fields are allocated and the count is within capacity. -/
structure Inv (s : Memory.State) : Prop where
  /-- The count cell is allocated. -/
  count_allocated : L.count.Allocated s
  /-- The item array is allocated. -/
  items_allocated : L.items.Allocated s
  /-- The count is at most the capacity. -/
  count_le : s.mem L.count.base ≤ L.items.length

/-! ## Evaluation -/

variable {w : ℕ}

/-- A push reads the count, writes the item and writes the new count. -/
theorem runClient_push (s : Memory.State) (v : ℕ) :
    (Memory.spec w).runClient s (push L v) =
      ((), ⟨Function.update (Function.update s.mem (L.items.base + s.mem L.count.base) v)
          L.count.base (s.mem L.count.base + 1), s.frontier⟩,
        [.read L.count.base, .write (L.items.base + s.mem L.count.base) v,
          .write L.count.base (s.mem L.count.base + 1)]) := rfl

/-- A pop from an empty stack reads the count only. -/
theorem runClient_pop_of_eq_zero (s : Memory.State) (h : s.mem L.count.base = 0) :
    (Memory.spec w).runClient s (pop L) = (none, s, [.read L.count.base]) := by
  simp [pop, h]

/-- A pop from a nonempty stack reads the count and the top item and writes the new count. -/
theorem runClient_pop_of_pos (s : Memory.State) (h : s.mem L.count.base ≠ 0) :
    (Memory.spec w).runClient s (pop L) =
      (some (s.mem (L.items.base + (s.mem L.count.base - 1))),
        ⟨Function.update s.mem L.count.base (s.mem L.count.base - 1), s.frontier⟩,
        [.read L.count.base, .read (L.items.base + (s.mem L.count.base - 1)),
          .write L.count.base (s.mem L.count.base - 1)]) := by
  unfold pop
  simp only [Block.runClient_get_bind, Nat.add_zero, h, ↓reduceIte]
  rfl

/-- A size query reads the count. -/
theorem runClient_size (s : Memory.State) :
    (Memory.spec w).runClient s (size L) = (s.mem L.count.base, s, [.read L.count.base]) := rfl

/-! ## The list view -/

variable {L} {C : ℕ}

/-- The stack has as many elements as the count. -/
@[simp] theorem length_abs (s : Memory.State) : (abs L s).length = s.mem L.count.base := by
  simp [abs]

/-- Writing the count leaves the items in place. -/
theorem abs_update_count (hL : L.Valid w C) (m : ℕ → ℕ) (f : ℕ) {n : ℕ} (hn : n ≤ C) :
    abs L ⟨Function.update m L.count.base n, f⟩ = (L.items.entries n m).reverse := by
  simp only [abs, Function.update_self]
  rw [Block.entries_update_of_not_owns _ (hL.items_length ▸ hn) hL.count_not_owns]

/-- The abstraction and the invariant read only the layout's cells and the frontier. -/
theorem abs_congr {s s' : Memory.State} (hL : L.Valid w C) (hs : Inv L s)
    (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) : abs L s' = abs L s := by
  have hc : s'.mem L.count.base = s.mem L.count.base :=
    h _ (L.count_mem_footprint hL.count_length)
  simp only [abs, hc]
  rw [Block.entries_congr _ _ fun i hi => h _ (L.item_mem_footprint (by
    have := hs.count_le
    omega))]

/-- The invariant reads only the layout's cells and survives a growing frontier. -/
theorem Inv.congr {s s' : Memory.State} (hL : L.Valid w C) (hs : Inv L s)
    (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier) : Inv L s' where
  count_allocated := hs.count_allocated.mono hf
  items_allocated := hs.items_allocated.mono hf
  count_le := by
    rw [h _ (L.count_mem_footprint hL.count_length)]
    exact hs.count_le

/-! ## The refinement -/

/-- The count cell is an admissible address. -/
theorem Inv.count_lt (hL : L.Valid w C) {s : Memory.State} (hs : Inv L s) :
    L.count.base < s.frontier := by
  simpa using hs.count_allocated.lt_frontier (i := 0) (by rw [hL.count_length]; omega)

/-- Item `i` below the capacity is an admissible address. -/
theorem Inv.item_lt {s : Memory.State} (hs : Inv L s) {i : ℕ} (hi : i < L.items.length) :
    L.items.base + i < s.frontier :=
  hs.items_allocated.lt_frontier hi

/-- The array stack implements the bounded stack of capacity `C`. -/
def refinement (hL : L.Valid w C) : Refinement (Stack.WordRAM.spec w C) (Memory.spec w) :=
  Refinement.ofFn (methods L w C) (Inv L) (abs L)
    (by
      intro s o hs hv
      have hcount := hs.count_lt hL
      have hC := hL.items_length
      cases o with
      | push v =>
        obtain ⟨hlen, hfit⟩ := hv
        rw [length_abs] at hlen
        simp only [methods, StateTransitionSpec.clientHistory, runClient_push]
        simp only [StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
          step_read, step_write, valid_read, valid_write]
        exact ⟨hcount, ⟨hs.item_lt (by omega), hfit⟩, ⟨hcount,
          hL.capacity_fits.of_le (by omega)⟩, trivial⟩
      | pop =>
        by_cases h0 : s.mem L.count.base = 0
        · simp only [methods, StateTransitionSpec.clientHistory, runClient_pop_of_eq_zero L s h0]
          exact ⟨hcount, trivial⟩
        · simp only [methods, StateTransitionSpec.clientHistory, runClient_pop_of_pos L s h0]
          simp only [StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
            step_read, step_write, valid_read, valid_write]
          have := hs.count_le
          exact ⟨hcount, hs.item_lt (by omega), ⟨hcount,
            hL.capacity_fits.of_le (by omega)⟩, trivial⟩
      | size =>
        simp only [methods, StateTransitionSpec.clientHistory, runClient_size]
        exact ⟨hcount, trivial⟩)
    (by
      intro s o hs hv
      have hle := hs.count_le
      have hC := hL.items_length
      cases o with
      | push v =>
        obtain ⟨hlen, -⟩ := hv
        rw [length_abs] at hlen
        simp only [methods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
          runClient_push]
        refine ⟨?_, ⟨hs.count_allocated, hs.items_allocated, by simp; omega⟩⟩
        rw [abs_update_count hL _ _ (by omega), Block.entries_succ,
          Block.entries_update_of_le _ le_rfl, Function.update_self]
        simp [abs]
      | pop =>
        by_cases h0 : s.mem L.count.base = 0
        · simp only [methods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
            runClient_pop_of_eq_zero L s h0]
          have he : abs L s = [] := List.eq_nil_of_length_eq_zero (by simp [h0])
          simp [he, hs]
        · simp only [methods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
            runClient_pop_of_pos L s h0]
          refine ⟨?_, ⟨hs.count_allocated, hs.items_allocated, by simp; omega⟩⟩
          obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
          have habs : abs L s =
              s.mem (L.items.base + n) :: (L.items.entries n s.mem).reverse := by
            simp [abs, hn, Block.entries_succ]
          rw [abs_update_count hL _ _ (by omega), habs]
          simp [hn]
      | size =>
        simp only [methods, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
          runClient_size]
        exact ⟨by simp, hs⟩)

/-- Every operation costs at most three memory units, so the stack needs no potential. -/
theorem amortized (hL : L.Valid w C) :
    (refinement hL).Amortized charge (fun _ _ => 3) fun _ => 0 := by
  apply Refinement.Amortized.ofFn
  intro s o _ _
  cases o with
  | push v => simp [refinement, methods, StateTransitionSpec.clientHistory, runClient_push]
  | pop =>
    by_cases h0 : s.mem L.count.base = 0
    · simp [refinement, methods, StateTransitionSpec.clientHistory,
        runClient_pop_of_eq_zero L s h0]
    · simp [refinement, methods, StateTransitionSpec.clientHistory, runClient_pop_of_pos L s h0]
  | size => simp [refinement, methods, StateTransitionSpec.clientHistory, runClient_size]

/-! ## The frame of a stack -/

/-- Each admissible operation writes only the layout's cells and never allocates. -/
theorem modifies_methods (hL : L.Valid w C) {s : Memory.State} (o : StackOp ℕ)
    (hv : (Stack.WordRAM.spec w C).valid (abs L s) o) :
    (∀ a ∉ L.footprint,
        ((Memory.spec w).clientState s (methods L w C o)).mem a = s.mem a) ∧
      ((Memory.spec w).clientState s (methods L w C o)).frontier = s.frontier := by
  have hc : L.count.base ∈ L.footprint := L.count_mem_footprint hL.count_length
  cases o with
  | push v =>
    obtain ⟨hlen, -⟩ := hv
    rw [length_abs] at hlen
    have hi : L.items.base + s.mem L.count.base ∈ L.footprint :=
      L.item_mem_footprint (by rw [hL.items_length]; exact hlen)
    simp only [methods, StateTransitionSpec.clientState, runClient_push]
    exact ⟨fun a ha => by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hc ha).symm,
        Function.update_of_ne (ne_of_mem_of_not_mem hi ha).symm], trivial⟩
  | pop =>
    by_cases h0 : s.mem L.count.base = 0
    · simp only [methods, StateTransitionSpec.clientState, runClient_pop_of_eq_zero L s h0]
      exact ⟨fun _ _ => trivial, trivial⟩
    · simp only [methods, StateTransitionSpec.clientState, runClient_pop_of_pos L s h0]
      exact ⟨fun a ha => Function.update_of_ne (ne_of_mem_of_not_mem hc ha).symm _ _, trivial⟩
  | size => exact ⟨fun _ _ => rfl, rfl⟩

/-- A stack's operations leave a stack with a disjoint layout unchanged. -/
theorem frame {L' : Layout} (hL : L.Valid w C) (hL' : L'.Valid w C)
    (hd : Disjoint L.footprint L'.footprint) {s : Memory.State} (hs' : Inv L' s)
    (o : StackOp ℕ) (hv : (Stack.WordRAM.spec w C).valid (abs L s) o) :
    abs L' ((Memory.spec w).clientState s (methods L w C o)) = abs L' s ∧
      Inv L' ((Memory.spec w).clientState s (methods L w C o)) := by
  obtain ⟨hm, hf⟩ := modifies_methods hL o hv
  have h : ∀ a ∈ L'.footprint,
      ((Memory.spec w).clientState s (methods L w C o)).mem a = s.mem a :=
    fun a ha => hm a (Finset.disjoint_right.mp hd ha)
  exact ⟨abs_congr hL' hs' h, hs'.congr hL' h hf.ge⟩

/-! ## Two stacks in one memory -/

/-- The operations of two stacks, each on its own layout. -/
def pairMethods (L₁ L₂ : Layout) (w C : ℕ) :
    Methods (product (Stack.WordRAM.spec w C) (Stack.WordRAM.spec w C)) (Memory.spec w)
  | .inl o => methods L₁ w C o
  | .inr o => methods L₂ w C o

/-- Two array stacks with disjoint layouts implement a pair of bounded stacks. -/
def pairRefinement {L₁ L₂ : Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) :
    Refinement (product (Stack.WordRAM.spec w C) (Stack.WordRAM.spec w C)) (Memory.spec w) :=
  (refinement h₁).prod (refinement h₂)
    (fun {s} o {a s' tr} hs₁ hs₂ hv hrun => by
      obtain ⟨_, _, rfl, _⟩ := ((Memory.spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
      exact frame h₁ h₂ hd hs₂ o hv)
    (fun {s} o {a s' tr} hs₁ hs₂ hv hrun => by
      obtain ⟨_, _, rfl, _⟩ := ((Memory.spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
      exact frame h₂ h₁ hd.symm hs₁ o hv)

/-- The pair's methods are `pairMethods`, whatever the proofs about the layouts. -/
theorem pairRefinement_methods {L₁ L₂ : Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) :
    (pairRefinement h₁ h₂ hd).methods = pairMethods L₁ L₂ w C := by
  funext o
  cases o <;> rfl

/-- Every operation of the pair costs at most three memory units. -/
theorem pair_amortized {L₁ L₂ : Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) :
    (pairRefinement h₁ h₂ hd).Amortized charge (fun _ _ => 3) fun _ => 0 := by
  have h : (pairRefinement h₁ h₂ hd).Amortized charge
      (productCharge (fun _ _ => 3) (fun _ _ => 3)) fun _ => 0 :=
    (amortized h₁).prod (amortized h₂) (fun _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ _ => rfl)
  rwa [productCharge_const] at h

/-! ## Allocation -/

/-- Allocate an empty stack of capacity `C`: a zeroed count cell and an item array that is not
cleared. -/
def allocLayout (C : ℕ) : Prog Layout := do
  let count ← allocBlock 1
  let items ← allocBlockDirty C
  pure ⟨count, items⟩

/-- Allocation places the count at the frontier and the items just above it. -/
theorem runClient_allocLayout_bind {α : Type} (C : ℕ) (next : Layout → Prog α)
    (s : Memory.State) :
    (Memory.spec w).runClient s (allocLayout C >>= next) =
      let (v, s', os) := (Memory.spec w).runClient
        ⟨clear s.mem s.frontier 1, s.frontier + 1 + C⟩
        (next ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, C⟩⟩)
      (v, s', .alloc 1 :: .allocDirty C :: os) := rfl

/-- The allocated layout is well formed when its end fits a word. -/
theorem valid_allocLayout {f : ℕ} (hf : Fits w (f + 1 + C)) :
    Layout.Valid ⟨⟨f, 1⟩, ⟨f + 1, C⟩⟩ w C where
  count_length := rfl
  count_not_owns := by simp [Block.Owns]
  items_length := rfl
  capacity_fits := hf.of_le (by omega)

/-- The allocated stack satisfies the invariant and is empty. -/
theorem inv_allocLayout (s : Memory.State) :
    Inv ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, C⟩⟩ ⟨clear s.mem s.frontier 1, s.frontier + 1 + C⟩ ∧
      abs ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, C⟩⟩
        ⟨clear s.mem s.frontier 1, s.frontier + 1 + C⟩ = [] := by
  have h0 : clear s.mem s.frontier 1 s.frontier = 0 :=
    clear_of_owns ⟨le_rfl, show s.frontier < s.frontier + 1 from Nat.lt_add_one _⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · change s.frontier + 1 ≤ s.frontier + 1 + C
    omega
  · change s.frontier + 1 + C ≤ s.frontier + 1 + C
    exact le_rfl
  · change clear s.mem s.frontier 1 s.frontier ≤ C
    rw [h0]
    exact Nat.zero_le C
  · simp [abs, h0]

end Cslib.DataStructure.Stack.Memory
