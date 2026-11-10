/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Backend
public import CslibFrontier.Computability.WordRAM.Realization.Client.MemoryStack

/-!
# The array stack on the word RAM

`Stack.Memory` implements the bounded stack `Stack.spec w C` by three memory programs. Here each
program runs as the static body of its uniform realization, `MemoryStack.realizes_push`,
`realizes_pop` or `realizes_size`, selected by the operation's constructor through
`Realization.Backend`; no instruction is stepped by hand. The layout and a push value are
installed in registers before the body, uncharged, as a calling convention. A push answers `()`
with no result words.

Correctness is that of `Stack.Memory.refinement`. Its memory charges are constant
(`Stack.Memory.amortized`), so one constant, chosen before every width, capacity and layout,
bounds the instructions of every operation (`instruction_bound`). An adaptive client with `m`
operations then runs within `m` times that constant (`Bound.exists_executes_const`). Each
operation leaves its method's final memory (`Backend.exec_memoryState`), so it writes only the
layout's cells (`Stack.Memory.modifies_methods`).

## Main definitions

* `Tag`, `certificates`, `backend`: the operation constructors, their realizations, and the
  stack's operations on a layout.
* `implementation`: the native stack.

## Main results

* `implements`: the backend runs the methods of `Stack.Memory`.
* `instruction_bound`: a constant bound per operation.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]
-/

namespace Cslib.DataStructure.Stack.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Realization.MemoryStack
  Cslib.DataStructure.Queue

/-- The constructors of the stack's operations. -/
public inductive Tag
  | push
  | pop
  | size
  deriving DecidableEq

public instance : Fintype Tag := Fintype.ofList [.push, .pop, .size] fun t => by cases t <;> simp

/-- One realization per constructor. -/
public noncomputable def certificates : Tag → Certificate .exact
  | .push => Certificate.ofRealizes realizes_push
  | .pop => Certificate.ofRealizes realizes_pop
  | .size => Certificate.ofRealizes realizes_size

/-- The stack's operations on layout `L`: every operation passes the layout, a push its value. -/
public noncomputable def backend (w C : ℕ) (L : Stack.Memory.Layout) :
    Backend (Stack.spec w C) certificates where
  tag
    | .push _ => .push
    | .pop => .pop
    | .size => .size
  arg
    | .push v => (L, v)
    | .pop => L
    | .size => L
  answer
    | .push _ => id
    | .pop => id
    | .size => id

private theorem layoutWords_fits {w : ℕ} {L : Stack.Memory.Layout} {e : Memory.State}
    (hw : Memory.WellFormed w e) (hi : Stack.Memory.Inv L e) (j : Fin 4) :
    Fits w (layoutWords L j) := by
  have h₁ : L.count.base + L.count.length ≤ e.frontier := hi.count_allocated
  have h₂ : L.items.base + L.items.length ≤ e.frontier := hi.items_allocated
  refine hw.frontier_fits.of_le ?_
  fin_cases j <;> simp [layoutWords] <;> omega

/-- The backend runs the methods of `Stack.Memory`. -/
public theorem implements {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) :
    (backend w C L).Implements (Stack.Memory.refinement hL) where
  run o s := by cases o <;> rfl
  entry {e} o hw hi hv := by
    have hC := hL.items_length
    cases o with
    | push v =>
      obtain ⟨hlen, hv⟩ := hv
      change (Stack.Memory.abs L e).length < C at hlen
      rw [Stack.Memory.length_abs] at hlen
      exact ⟨fits_appendWords (d := L) (a := v) layoutWords
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (layoutWords_fits hw hi) fun _ => hv,
        hC ▸ hL, hi, (by omega : e.mem L.count.base < L.items.length)⟩
    | pop => exact ⟨layoutWords_fits hw hi, hC ▸ hL, hi⟩
    | size => exact ⟨layoutWords_fits hw hi, trivial⟩

/-- The native stack on layout `L`. -/
public noncomputable def implementation {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) :
    StateTransitionImpl (Stack.spec w C) ((backend w C L).exec w) :=
  Backend.implementation (implements hL)

/-- **Constant time per operation.** One constant `K`, chosen before every width, capacity,
layout, state and operation, bounds the instructions of every admissible operation. -/
public theorem instruction_bound : ∃ K, ∀ {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C),
    Bound (implementation hL) id fun _ _ => K :=
  ⟨Backend.factor certificates * 23, fun hL =>
    Backend.bound (implements hL) (Stack.Memory.amortized hL) 19 fun o _ _ => by
      cases o <;> exact Nat.le_of_ble_eq_true rfl⟩

end Cslib.DataStructure.Stack.Native
