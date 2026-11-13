/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.BinaryHeap.Native.SiftUp
import CslibFrontier.Tactic.Realize

/-!
# Native insert and decrease-key through the realized sift

The existing memory programs keep their original queries and writes. Their bounded prefixes
compose with the shared sift-up certificate by static register wiring. Layouts, handles and keys
are runtime words; the bound and typed operation in the entry domain are proof data only.

## Main definitions

* `UpdateArgument`, `updateWords`: runtime layout, handle word and key.
* `insertSafe`, `decreaseSafe`: the original indexed-PQ admissibility and heap invariant.

## Main results

* `realizes_insert`, `realizes_decreaseKey`: source-faithful, zero-local-work certificates.

Argument delivery and initialization remain outside these installed-register certificates.
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.BinaryHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue.BinaryHeap

/-- Runtime layout and handle word, followed by the new key. -/
abbrev UpdateArgument := IndexArgument × ℕ

namespace UpdateArgument

/-- The runtime layout. -/
abbrev heap (d : UpdateArgument) : HeapLayout := d.1.1

/-- The number of handles. -/
abbrev capacity (d : UpdateArgument) : ℕ := d.1.1.1

/-- The heap layout. -/
abbrev layout (d : UpdateArgument) : Memory.Layout d.capacity := d.1.1.2

/-- The handle word. -/
abbrev handle (d : UpdateArgument) : ℕ := d.1.2

/-- The new key. -/
abbrev key (d : UpdateArgument) : ℕ := d.2

end UpdateArgument

/-- Runtime layout and handle, followed by the new key. -/
abbrev updateWords := appendWords indexWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- Exactly the existing valid insertion at a well-formed heap, with the word handle bound
visible. The key bound is proof data, not a parameter selecting emitted code. -/
def insertSafe (w : ℕ) (d : UpdateArgument) (s : Memory.State) : Prop :=
  ∃ (hv : d.handle < d.capacity) (K : ℕ), d.layout.Valid w K ∧ Memory.Inv d.layout s ∧
    IndexedMinPQ.valid K (Memory.abs d.layout s) (.insert ⟨d.handle, hv⟩ d.key)

/-- Exactly the existing valid decrease-key at a well-formed heap. -/
def decreaseSafe (w : ℕ) (d : UpdateArgument) (s : Memory.State) : Prop :=
  ∃ (hv : d.handle < d.capacity) (K : ℕ), d.layout.Valid w K ∧ Memory.Inv d.layout s ∧
    IndexedMinPQ.valid K (Memory.abs d.layout s) (.decreaseKey ⟨d.handle, hv⟩ d.key)

private def insertPrefix (d : UpdateArgument) : Memory.Prog ℕ := do
  let S ← d.layout.size.get 0
  d.layout.size.set 0 (S + 1)
  d.layout.key.set d.handle d.key
  d.layout.heap.set (S + 1) d.handle
  d.layout.pos.set d.handle (S + 1)
  pure (S + 1)

private def decreasePrefix (d : UpdateArgument) : Memory.Prog ℕ := do
  let p ← d.layout.pos.get d.handle
  d.layout.key.set d.handle d.key
  pure p

private theorem realizes_insertPrefix :
    Realizes .exact insertPrefix updateWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      insertSafe (fun _ _ => 0) := by
  realize
  all_goals
    rcases h with ⟨hv, K, hL, hs, hnone, hk⟩
    have hp : s.mem (d.layout.base + 2 * d.capacity + 1 + d.handle) = 0 := by
      by_contra hn
      simp [Memory.abs, stateOfMem, hn] at hnone
    have hSn := hs.heap.size_lt hv hp
    first
    | exact hL.n_fits.of_le (by omega)
    | exact hmem.fits_of_lt_frontier (Memory.key_lt hs.arrays_allocated hv)
    | exact hmem.fits_of_lt_frontier (Memory.heap_lt hs.arrays_allocated (by omega))
    | exact hmem.fits_of_lt_frontier (Memory.pos_lt hs.arrays_allocated hv)
    | apply hmem.fits_of_lt_frontier
      have hA := hs.arrays_allocated
      change d.layout.base + (3 * d.capacity + 1) ≤ s.frontier at hA
      omega

private theorem realizes_decreasePrefix :
    Realizes .exact decreasePrefix updateWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      decreaseSafe (fun _ _ => 0) := by
  realize
  all_goals
    rcases h with ⟨hv, K, hL, hs, hvalid⟩
    first
    | exact hmem.fits_of_lt_frontier (Memory.pos_lt hs.arrays_allocated hv)
    | exact hmem.fits_of_lt_frontier (Memory.key_lt hs.arrays_allocated hv)
    | apply hmem.fits_of_lt_frontier
      have hA := hs.arrays_allocated
      change d.layout.base + (3 * d.capacity + 1) ≤ s.frontier at hA
      omega

private theorem insertPrefix_shape {w : ℕ} {d : UpdateArgument} {s : Memory.State}
    (h : insertSafe w d s) :
    SiftUp.Shape w (d.heap, ()) ((Memory.spec 0).clientResult s (insertPrefix d))
      ((Memory.spec 0).clientState s (insertPrefix d)) := by
  rcases h with ⟨hv, K, hL, hs, hnone, hk⟩
  have hp : s.mem (d.layout.base + 2 * d.capacity + 1 + d.handle) = 0 := by
    by_contra hn
    simp [Memory.abs, stateOfMem, hn] at hnone
  have hsz := Memory.size_location hL
  have hpush := (Memory.heapInv_update_size hL hs.heap (s.mem d.layout.size.base + 1)).push hv
    (c := d.key) (by rw [Function.update_of_ne (by omega)]; exact hp)
  refine ⟨hL.n_fits, ?_, s.mem d.layout.size.base + 1, ?_, le_rfl, ?_⟩
  · exact hs.arrays_allocated
  · simp [insertPrefix, StateTransitionSpec.clientResult, -bind_pure_comp]
  · simpa [insertPrefix, StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      ← bind_pure_comp]
      using hpush.1

private theorem decreasePrefix_shape {w : ℕ} {d : UpdateArgument} {s : Memory.State}
    (h : decreaseSafe w d s) :
    SiftUp.Shape w (d.heap, ()) ((Memory.spec 0).clientResult s (decreasePrefix d))
      ((Memory.spec 0).clientState s (decreasePrefix d)) := by
  rcases h with ⟨hv, K, hL, hs, ⟨k₀, hk₀, hle⟩, hk⟩
  have hp : s.mem (d.layout.base + 2 * d.capacity + 1 + d.handle) ≠ 0 := by
    intro hn
    simp [Memory.abs, stateOfMem, hn] at hk₀
  have hkey : s.mem (d.layout.base + d.handle) = k₀ := by
    simpa [Memory.abs, stateOfMem, hp] using hk₀
  have hdec := hs.heap.decrease hv hp (c := d.key) (by omega)
  refine ⟨hL.n_fits, ?_, s.mem d.layout.size.base, ?_, ?_, ?_⟩
  · exact hs.arrays_allocated
  · simpa [decreasePrefix, StateTransitionSpec.clientResult, ← bind_pure_comp] using
      Nat.one_le_iff_ne_zero.mpr hp
  · simpa [decreasePrefix, StateTransitionSpec.clientResult, ← bind_pure_comp] using
      hs.heap.pos_le d.handle hv
  · simpa [decreasePrefix, StateTransitionSpec.clientState, ← bind_pure_comp] using hdec.1

/-- The shared sift-up body, wired to an update's layout and the position its prefix returns. -/
private theorem realizes_siftUpTail :
    Realizes .exact
      (fun d : UpdateArgument × ℕ => PriorityQueue.BinaryHeap.Memory.siftUp d.1.layout d.2)
      (appendWords updateWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
      (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => SiftUp.Shape w (d.1.heap, ()) d.2 s) (fun _ _ => 0) :=
  SiftUp.realizes_siftUp.reindex (fun d : UpdateArgument × ℕ => (d.1.heap, d.2))
    (appendWords updateWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding)
    ![0, 1, 2, 3, 6] (by intro d i; fin_cases i <;> rfl)

/-- Insert uses its original prefix and the same globally chosen sift body. -/
theorem realizes_insert :
    Realizes .exact (fun d : UpdateArgument => Memory.insert d.layout d.handle d.key)
      updateWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding insertSafe
      (fun _ _ => 0) := by
  refine (realizes_insertPrefix.bind₀ realizes_siftUpTail).congr (fun d => ?_) |>.consequence ?_
    (fun _ _ => le_rfl)
  · simp only [insertPrefix, Memory.insert, ← PFunctor.FreeM.bind_eq_bind,
      PFunctor.FreeM.bind_assoc, PFunctor.FreeM.pure_bind]
  · intro w d s _ _ h
    exact ⟨h, insertPrefix_shape h⟩

/-- Decrease-key uses the original write and the same globally chosen sift body. -/
theorem realizes_decreaseKey :
    Realizes .exact (fun d : UpdateArgument => Memory.decreaseKey d.layout d.handle d.key)
      updateWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding decreaseSafe
      (fun _ _ => 0) := by
  refine (realizes_decreasePrefix.bind₀ realizes_siftUpTail).congr (fun d => ?_)
    |>.consequence ?_ (fun _ _ => le_rfl)
  · simp only [decreasePrefix, Memory.decreaseKey, ← PFunctor.FreeM.bind_eq_bind,
      PFunctor.FreeM.bind_assoc, PFunctor.FreeM.pure_bind]
  · intro w d s _ _ h
    exact ⟨h, decreasePrefix_shape h⟩

end Cslib.DataStructure.PriorityQueue.BinaryHeap.Native
