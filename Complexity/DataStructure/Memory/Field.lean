/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.ListArray
public import Complexity.DataStructure.Memory.Spec

/-!
# Named field arrays over the memory oracle

A field array is a `Cslib.WordRAM.Block`: a base address and a length. A data structure lays out
its storage as a structure whose fields are blocks (a struct of arrays) and accesses entry `i` of
a field `f` with the programs `f.get i` and `f.set i v` over `Memory.spec w`. Addresses are thus
named (`par.get v`) rather than computed by hand (`base + n + v`), while computed indices, pointer
chasing (`do let p ← next.get v; key.get p`) and reuse of a block across operations remain
ordinary programs.

The lemmas here evaluate these programs, discharge their admissibility from `Block.Allocated`,
and describe their frame: a write to a field leaves every other address unchanged.
`Block.entries` reads the first `n` entries of a field as a list, which is how an abstraction
function usually sees an array. It realizes `Block.HoldsList`.

## Main definitions

* `Cslib.WordRAM.Block.get`, `Cslib.WordRAM.Block.set`: entry access through the oracle.
* `Cslib.WordRAM.Block.Allocated`: the block lies below the frontier.
* `Cslib.WordRAM.Block.entries`: the first `n` entries of a field in index order.
* `Cslib.DataStructure.Memory.allocBlock`, `Cslib.DataStructure.Memory.allocBlockDirty`:
  allocate a field.

## Main results

* `Cslib.WordRAM.Block.runClient_get_bind`, `Cslib.WordRAM.Block.runClient_set_bind`: one-step
  evaluation of field accesses.
* `Cslib.WordRAM.Block.Allocated.lt_frontier`, `Cslib.WordRAM.Block.Allocated.mono`: allocated
  entries are admissible addresses, and stay allocated.
* `Cslib.WordRAM.Block.entries_succ`, `Cslib.WordRAM.Block.entries_congr`,
  `Cslib.WordRAM.Block.entries_update_of_le`, `Cslib.WordRAM.Block.entries_update_of_not_owns`:
  the list view under appends and writes.
* `Cslib.WordRAM.Block.holdsList_entries`: the list view realizes `Block.HoldsList`.
* `Cslib.DataStructure.Memory.runClient_allocBlock_bind`: allocation hands out a zeroed,
  allocated block at the frontier.
-/

@[expose] public section

namespace Cslib.WordRAM.Block

open Cslib.DataStructure

/-- Read entry `i` of the field `b` through the memory oracle. -/
abbrev get (b : Block) (i : ℕ) : Memory.Prog ℕ := Memory.read (b.base + i)

/-- Write `v` to entry `i` of the field `b` through the memory oracle. -/
abbrev set (b : Block) (i v : ℕ) : Memory.Prog Unit := Memory.write (b.base + i) v

/-- The block lies below the frontier, so all of its entries are allocated. -/
def Allocated (b : Block) (s : Memory.State) : Prop := b.base + b.length ≤ s.frontier

/-- An entry of an allocated block is an allocated address. -/
theorem Allocated.lt_frontier {b : Block} {s : Memory.State} (h : b.Allocated s) {i : ℕ}
    (hi : i < b.length) : b.base + i < s.frontier := by
  unfold Allocated at h
  omega

/-- A block stays allocated as the frontier grows. -/
theorem Allocated.mono {b : Block} {s s' : Memory.State} (h : b.Allocated s)
    (hs : s.frontier ≤ s'.frontier) : b.Allocated s' :=
  le_trans h hs

/-- A block owns the address of each of its entries. -/
theorem owns_add {b : Block} {i : ℕ} (hi : i < b.length) : b.Owns (b.base + i) :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩

/-- Reading an entry returns the cell and leaves memory unchanged. -/
@[simp] theorem runClient_get_bind {w : ℕ} {α : Type} (b : Block) (i : ℕ) (k : ℕ → Memory.Prog α)
    (s : Memory.State) :
    (Memory.spec w).runClient s (b.get i >>= k) =
      let (v, s', os) := (Memory.spec w).runClient s (k (s.mem (b.base + i)))
      (v, s', .read (b.base + i) :: os) := rfl

/-- Writing an entry updates its cell. -/
@[simp] theorem runClient_set_bind {w : ℕ} {α : Type} (b : Block) (i v : ℕ)
    (k : Unit → Memory.Prog α) (s : Memory.State) :
    (Memory.spec w).runClient s (b.set i v >>= k) =
      let (r, s', os) := (Memory.spec w).runClient
        ⟨Function.update s.mem (b.base + i) v, s.frontier⟩ (k ())
      (r, s', .write (b.base + i) v :: os) := rfl

/-! ## The list of entries -/

/-- The first `n` entries of the field `b` in memory `m`, in index order. -/
def entries (b : Block) (n : ℕ) (m : ℕ → ℕ) : List ℕ :=
  (List.range n).map fun i => m (b.base + i)

@[simp] theorem length_entries (b : Block) (n : ℕ) (m : ℕ → ℕ) : (b.entries n m).length = n := by
  simp [entries]

@[simp] theorem entries_zero (b : Block) (m : ℕ → ℕ) : b.entries 0 m = [] := rfl

/-- Entry `i` of the list view is the cell at `b.base + i`. -/
@[simp] theorem getElem_entries (b : Block) (n : ℕ) (m : ℕ → ℕ) (i : ℕ)
    (hi : i < (b.entries n m).length) : (b.entries n m)[i] = m (b.base + i) := by
  simp [entries]

/-- One more entry appends its cell. -/
theorem entries_succ (b : Block) (n : ℕ) (m : ℕ → ℕ) :
    b.entries (n + 1) m = b.entries n m ++ [m (b.base + n)] := by
  simp [entries, List.range_succ]

/-- The list view depends only on the cells of its entries. -/
theorem entries_congr (b : Block) (n : ℕ) {m m' : ℕ → ℕ}
    (h : ∀ i < n, m' (b.base + i) = m (b.base + i)) : b.entries n m' = b.entries n m :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- Writing at or beyond entry `n` leaves the first `n` entries unchanged. -/
theorem entries_update_of_le (b : Block) {n i : ℕ} (hi : n ≤ i) (m : ℕ → ℕ) (v : ℕ) :
    b.entries n (Function.update m (b.base + i) v) = b.entries n m :=
  b.entries_congr n fun j hj => Function.update_of_ne (by omega) v m

/-- Writing outside the block leaves every entry unchanged. -/
theorem entries_update_of_not_owns (b : Block) {n : ℕ} (hn : n ≤ b.length) {a : ℕ}
    (ha : ¬b.Owns a) (m : ℕ → ℕ) (v : ℕ) :
    b.entries n (Function.update m a v) = b.entries n m :=
  b.entries_congr n fun j hj =>
    Function.update_of_ne (fun h => ha (by rw [← h]; exact owns_add (by omega))) v m

/-- The list view of `n` entries realizes the list at the block's base. -/
theorem holdsList_entries (b : Block) (n : ℕ) (m : ℕ → ℕ) :
    HoldsList b.base (b.entries n m) m := fun i => by
  simp [Block.read]

end Cslib.WordRAM.Block

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

/-- Allocate a zeroed field of `k` cells. -/
def allocBlock (k : ℕ) : Prog Block := do
  let base ← alloc k
  pure ⟨base, k⟩

/-- Allocate a field of `k` cells without clearing it. -/
def allocBlockDirty (k : ℕ) : Prog Block := do
  let base ← allocDirty k
  pure ⟨base, k⟩

/-- A zeroed allocation hands out the block at the frontier, clears it, and advances the
frontier past it. -/
@[simp] theorem runClient_allocBlock_bind {w : ℕ} {α : Type} (k : ℕ) (next : Block → Prog α)
    (s : State) :
    (spec w).runClient s (allocBlock k >>= next) =
      let (v, s', os) := (spec w).runClient
        ⟨clear s.mem s.frontier k, s.frontier + k⟩ (next ⟨s.frontier, k⟩)
      (v, s', .alloc k :: os) := rfl

/-- A dirty allocation hands out the block at the frontier without changing memory. -/
@[simp] theorem runClient_allocBlockDirty_bind {w : ℕ} {α : Type} (k : ℕ)
    (next : Block → Prog α) (s : State) :
    (spec w).runClient s (allocBlockDirty k >>= next) =
      let (v, s', os) := (spec w).runClient ⟨s.mem, s.frontier + k⟩ (next ⟨s.frontier, k⟩)
      (v, s', .allocDirty k :: os) := rfl

/-- A freshly allocated block is allocated in the new state. -/
theorem allocated_alloc (s : State) (k : ℕ) :
    (Block.mk s.frontier k).Allocated ⟨clear s.mem s.frontier k, s.frontier + k⟩ :=
  le_rfl

/-- A freshly allocated zeroed block holds zeros. -/
theorem entries_alloc (s : State) (k : ℕ) {n : ℕ} (hn : n ≤ k) :
    (Block.mk s.frontier k).entries n (clear s.mem s.frontier k) = List.replicate n 0 := by
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp only [Block.length_entries] at hi
  simp only [Block.getElem_entries, List.getElem_replicate]
  exact clear_of_owns (Block.owns_add (b := ⟨s.frontier, k⟩) (by simp only; omega))

end Cslib.DataStructure.Memory
