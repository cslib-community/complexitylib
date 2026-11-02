/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Heap
public import Complexity.Computability.WordRAM.Realization.Backend
public import Complexity.Computability.WordRAM.Realization.Client.MemoryStack

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
bounds the instructions of every operation (`instruction_bound`), and an adaptive client with
`m` operations runs within `m` times that constant (`run_client`). Each operation writes only
the layout's cells (`modifies`, `frame`).

## Main definitions

* `Tag`, `certificates`, `backend`: the operation constructors, their realizations, and the
  stack's operations on a layout.
* `implementation`: the native stack.
* `initialLayout`, `initial`: an empty stack at a fixed address, as a calling-convention state.

## Main results

* `implements`: the backend runs the methods of `Stack.Memory`.
* `instruction_bound`, `run_client`: a constant bound per operation.
* `modifies`, `frame`: operations write only the layout's cells.
* `initial_rep`: the initial state represents the empty stack.

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
  | .push => ⟨realizes_push⟩
  | .pop => ⟨realizes_pop⟩
  | .size => ⟨realizes_size⟩

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

/-- **Adaptive clients.** Every client whose history is admissible has a native execution, one
operation at a time, that returns the specified answer and represents the specified final stack,
within `K` instructions per operation. The client's own computation is outside the machine. -/
public theorem run_client : ∃ K, ∀ {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C)
    {α : Type} (p : (Stack.spec w C).Client α) {vs : List ℕ}
    {x : Data (Backend.registers certificates)}, (implementation hL).rep vs x →
    (Stack.spec w C).ValidHistory vs ((Stack.spec w C).clientHistory vs p) →
    ∃ y traces, Executes ((backend w C L).exec w) p x ((Stack.spec w C).clientResult vs p) y
        traces ∧ (implementation hL).rep ((Stack.spec w C).clientState vs p) y ∧
      total id traces ≤ ((Stack.spec w C).clientHistory vs p).length * K := by
  obtain ⟨K, hK⟩ := instruction_bound
  exact ⟨K, fun hL _ p _ _ hr hv => Bound.exists_executes_const (hK hL) p hr hv⟩

/-- Every operation writes only the layout's cells and keeps the frontier. -/
public theorem modifies {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {vs : List ℕ}
    {x y : Data (Backend.registers certificates)} {o : StackOp ℕ}
    {a : (Stack.spec w C).Result o} {n : ℕ} (hr : (implementation hL).rep vs x)
    (hv : (Stack.spec w C).valid vs o) (he : (backend w C L).exec w x o a y n) :
    Modifies L.footprint x.mem y.mem ∧
      y.regs (Backend.frontier certificates) = x.regs (Backend.frontier certificates) := by
  have hm : memoryState (Backend.frontier certificates) y = (Memory.spec w).clientState
      (memoryState (Backend.frontier certificates) x) (Stack.Memory.methods L w C o) :=
    Backend.exec_memoryState (implements hL) hr hv he
  rw [← ((Backend.rep_iff _ _ _).mp hr).2.1] at hv
  obtain ⟨hmem, hfr⟩ := Stack.Memory.modifies_methods hL o hv
  rw [← hm] at hmem hfr
  exact ⟨hmem, hfr⟩

/-- Every operation preserves each heap assertion disjoint from the layout. -/
public theorem frame {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {vs : List ℕ}
    {x y : Data (Backend.registers certificates)} {o : StackOp ℕ}
    {a : (Stack.spec w C).Result o} {n : ℕ} (hr : (implementation hL).rep vs x)
    (hv : (Stack.spec w C).valid vs o) (he : (backend w C L).exec w x o a y n)
    {Q : HeapAssertion} (hQ : Q.holds x.mem) (hd : Disjoint Q.footprint L.footprint) :
    Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies hL hr hv he).1

/-- The layout of a stack of capacity `C` at `base`: the count cell `base`, then the items. -/
public def initialLayout (base C : ℕ) : Stack.Memory.Layout := ⟨⟨base, 1⟩, ⟨base + 1, C⟩⟩

/-- The initial layout is well formed when the end of the items fits a word. -/
public theorem valid_initialLayout {w base C : ℕ} (hf : Fits w (base + 1 + C)) :
    (initialLayout base C).Valid w C := Stack.Memory.valid_allocLayout hf

/-- An empty stack of capacity `C` at `base`: zero memory, and the frontier just past the items.
This is a calling-convention state, not an uncharged allocation; `Stack.Memory.allocLayout`
allocates. -/
public noncomputable def initial (base C : ℕ) : Data (Backend.registers certificates) :=
  Backend.data certificates ⟨fun _ => 0, base + 1 + C⟩

/-- The initial state represents the empty stack when the end of the items fits a word. -/
public theorem initial_rep {w base C : ℕ} (hf : Fits w (base + 1 + C)) :
    (implementation (valid_initialLayout hf)).rep [] (initial base C) :=
  Backend.rep_data _ ⟨hf, fun _ => fits_zero w⟩
    ⟨show base + 1 ≤ base + 1 + C by omega, le_rfl, Nat.zero_le _⟩
    (by simp [Stack.Memory.refinement, Stack.Memory.abs])

end Cslib.DataStructure.Stack.Native
