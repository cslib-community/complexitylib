/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Bind
public import CslibFrontier.Computability.WordRAM.Realization.Branch
public import CslibFrontier.Computability.WordRAM.Realization.Glue
public import CslibFrontier.Computability.WordRAM.Realization.GlueVector
public import CslibFrontier.Computability.WordRAM.Realization.Primitive
public import CslibFrontier.DataStructure.Stack.Memory
import CslibFrontier.Tactic.Realize

/-!
# Native realizations of the memory-oracle stack

The certificates consume the existing `Stack.Memory` methods unchanged. Every field of the
runtime layout has a faithful word encoding, so the emitter is chosen before the layout's
allocation addresses and all operation arguments. The fixed public local-work allowances are
retained; `realize` certifies arithmetic, copies and control through shared closure rules and
a uniform native exchange factor in addition to the actual memory history.

## Main definitions

* `layoutWords`, `pushWords`: faithful encodings of the complete layout and push arguments.

## Main results

* `realizes_size`, `realizes_push`, `realizes_pop`: uniform native realizations of the existing
  stack methods.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.MemoryStack

open Cslib.DataStructure

/-- All four layout fields are retained: count base/length, then items base/length. -/
def layoutWords : Stack.Memory.Layout ↪ (Fin 4 → ℕ) where
  toFun L := ![L.count.base, L.count.length, L.items.base, L.items.length]
  inj' := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
    have ha := congrFun h 0
    have hb := congrFun h 1
    have hc := congrFun h 2
    have hd := congrFun h 3
    change a = a' at ha
    change b = b' at hb
    change c = c' at hc
    change d = d' at hd
    cases ha; cases hb; cases hc; cases hd
    rfl

/-- Push arguments append the unshifted value to the complete runtime layout. -/
def pushWords : Stack.Memory.Layout × ℕ ↪ (Fin 5 → ℕ) :=
  appendWords layoutWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- Size uses the existing count query with no additional local computation. -/
theorem realizes_size :
    Realizes .exact Stack.Memory.size layoutWords
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read layoutWords 0

/-- Push works uniformly for every runtime layout and value. The visible invariant and spare
capacity discharge the address and increment fit obligations. The fixed local-work allowance
remains ten; the tactic certifies all glue and control with one uniform exchange factor. -/
theorem realizes_push :
    Realizes .exact (fun d : Stack.Memory.Layout × ℕ => Stack.Memory.push d.1 d.2)
      pushWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun w d s => d.1.Valid w d.1.items.length ∧ Stack.Memory.Inv d.1 s ∧
        s.mem d.1.count.base < d.1.items.length) (fun _ _ => 10) := by
  realize
  all_goals
    rcases h with ⟨hL, hInv, hcap⟩
    first
    | exact hmem.fits_of_lt_frontier (hInv.item_lt hcap)
    | exact hL.capacity_fits.of_le (by omega)

/-- Pop returns a presence tag and unshifted payload. Its positive branch uses defined exact
subtraction and performs the existing memory reads/write. All copies and branch/bind overhead
are charged; the local-work allowance is 19 for either path, including the shorter empty path. -/
theorem realizes_pop :
    Realizes .exact Stack.Memory.pop layoutWords optionWords
      (fun w L s => L.Valid w L.items.length ∧ Stack.Memory.Inv L s) (fun _ _ => 19) := by
  realize
  all_goals
    rcases h with ⟨hL, hInv⟩
    have h1 : Fits w 1 := hL.count_length ▸ hwords 1
    first
    | omega
    | exact hmem.fits_of_lt_frontier (hInv.item_lt (by have := hInv.count_le; omega))

/-- The push's explicit local work is dominated by its actual three-query memory charge. -/
theorem push_work_bound (L : Stack.Memory.Layout) (v : ℕ) (s : Memory.State) :
    10 ≤ 4 * memoryCost (Stack.Memory.push L v) s := by
  change 10 ≤ 4 * 3
  decide

/-- Even the empty pop has a memory query. This domination uses the actual method history,
after separately certifying all 19 units of local work, and is not a general query-only rule. -/
theorem pop_work_bound (L : Stack.Memory.Layout) (s : Memory.State) :
    19 ≤ 19 * memoryCost (Stack.Memory.pop L) s := by
  by_cases h : s.mem L.count.base = 0
  · simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.runClient_pop_of_eq_zero,
      h, StateTransitionSpec.totalCost, Memory.charge]
  · simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.runClient_pop_of_pos,
      h, StateTransitionSpec.totalCost, Memory.charge]

end Cslib.WordRAM.Realization.MemoryStack
