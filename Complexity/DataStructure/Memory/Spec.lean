/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Heap
public import Complexity.DataStructure.StateTransition

/-!
# Word-addressed memory as a state-transition specification

`Memory.spec w` is a memory oracle: the interface through which a data-structure implementation
reaches storage. Its state is the contents of every cell together with an allocation frontier.
Every address below the frontier is allocated, and allocation hands out the block that starts at
the frontier. The operations read a cell, write a cell, and allocate a block, either zeroed
(`alloc`, charged per cell) or with its old contents (`allocDirty`, charged one unit).

Admissibility carries the preconditions a word RAM needs. Accessed addresses must be allocated,
written values must fit a `w`-bit word, and the frontier after an allocation must fit. Under
these preconditions the frontier and every cell keep fitting a word (`WellFormed.step`), so an
allocated address fits too (`WellFormed.fits_of_lt_frontier`).

An implementation over this interface is an ordinary `Memory.Prog` program. Its correctness and
its operation charges are proved against `step` and `charge`, without registers or instruction
counts. `charge` is the memory-level currency; executing such a program on the word RAM is a
separate step that exchanges it into instructions. Allocation never reuses addresses, as in
`Cslib.WordRAM.alloc`, so blocks allocated at different times are disjoint
(`Cslib.WordRAM.Block.disjoint_of_le`). A program reuses memory by keeping a block it allocated.

## Main definitions

* `Memory.State`, `Memory.Op`, `Memory.step`, `Memory.valid`: cells and frontier, operations
  with their answers, the transition function and the admissibility preconditions.
* `Memory.spec`: the deterministic specification at word size `w`.
* `Memory.charge`: one unit per read, write and dirty allocation; `k + 1` for a zeroed block of
  `k` cells.
* `Memory.Prog`, `Memory.read`, `Memory.write`, `Memory.alloc`, `Memory.allocDirty`: programs
  over the oracle and its four one-call programs.
* `Memory.WellFormed`: the frontier and all cell contents fit a `w`-bit word.
* `Memory.State.init`: the word RAM's input convention as a memory state.

## Main results

* `Memory.WellFormed.step`, `Memory.WellFormed.run`: admissible operations preserve
  well-formedness.
* `Memory.WellFormed.fits_of_lt_frontier`: allocated addresses fit a word.
* `Memory.one_le_charge`: every operation costs at least one unit.
* `Memory.frontier_le_step`, `Memory.frontier_le_run`: the frontier never decreases.
* `Memory.mem_step_of_lt_frontier`: an operation changes an allocated cell only by writing it.
* `Memory.wellFormed_init`: the input convention is well formed.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

/-- Memory: the contents of every cell, and the frontier below which cells are allocated. -/
@[ext]
structure State where
  /-- The contents of the cell at each address. -/
  mem : ℕ → ℕ
  /-- Every address below the frontier is allocated; the next block starts here. -/
  frontier : ℕ

/-- Operations on memory. Addresses are words computed by the caller. -/
inductive Op where
  /-- Read the cell at an address. -/
  | read (addr : ℕ)
  /-- Write a value to the cell at an address. -/
  | write (addr value : ℕ)
  /-- Allocate `count` zeroed cells at the frontier and return their base address. -/
  | alloc (count : ℕ)
  /-- Allocate `count` cells at the frontier without clearing them and return their base
  address. -/
  | allocDirty (count : ℕ)
  deriving DecidableEq

/-- The answer type of each operation: a read and an allocation return a word. -/
abbrev Op.Result : Op → Type
  | .read _ => ℕ
  | .write _ _ => Unit
  | .alloc _ => ℕ
  | .allocDirty _ => ℕ

/-- The transition of each operation. An allocation returns the old frontier. -/
def step (s : State) : (o : Op) → State × o.Result
  | .read a => (s, s.mem a)
  | .write a v => (⟨Function.update s.mem a v, s.frontier⟩, ())
  | .alloc k => (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier)
  | .allocDirty k => (⟨s.mem, s.frontier + k⟩, s.frontier)

/-- Admissibility at word size `w`: accessed addresses are allocated, written values fit a word,
and an allocation leaves a fitting frontier. -/
def valid (w : ℕ) (s : State) : Op → Prop
  | .read a => a < s.frontier
  | .write a v => a < s.frontier ∧ Fits w v
  | .alloc k => Fits w (s.frontier + k)
  | .allocDirty k => Fits w (s.frontier + k)

instance (w : ℕ) (s : State) (o : Op) : Decidable (valid w s o) := by
  cases o <;> unfold valid <;> infer_instance

/-- Word-addressed memory at word size `w`. -/
abbrev spec (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := State) (Op := Op) (Result := Op.Result) step (valid w)

/-- The memory-level currency: one unit per read, write and dirty allocation, and `k + 1` units
for a zeroed block of `k` cells. -/
def charge (_ : State) : Op → ℕ
  | .alloc k => k + 1
  | _ => 1

/-- Programs over the memory oracle. They are the clients of `Memory.spec w` at every word size. -/
abbrev Prog (α : Type) : Type := PFunctor.FreeM ⟨Op, Op.Result⟩ α

/-- Read the cell at address `a`. -/
abbrev read (a : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.read a)

/-- Write `v` to the cell at address `a`. -/
abbrev write (a v : ℕ) : Prog Unit := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.write a v)

/-- Allocate `k` zeroed cells and return their base address. -/
abbrev alloc (k : ℕ) : Prog ℕ := PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.alloc k)

/-- Allocate `k` cells without clearing them and return their base address. -/
abbrev allocDirty (k : ℕ) : Prog ℕ :=
  PFunctor.FreeM.lift (P := ⟨Op, Op.Result⟩) (.allocDirty k)

@[simp] theorem step_read (s : State) (a : ℕ) : step s (.read a) = (s, s.mem a) := rfl

@[simp] theorem step_write (s : State) (a v : ℕ) :
    step s (.write a v) = (⟨Function.update s.mem a v, s.frontier⟩, ()) := rfl

@[simp] theorem step_alloc (s : State) (k : ℕ) :
    step s (.alloc k) = (⟨clear s.mem s.frontier k, s.frontier + k⟩, s.frontier) := rfl

@[simp] theorem step_allocDirty (s : State) (k : ℕ) :
    step s (.allocDirty k) = (⟨s.mem, s.frontier + k⟩, s.frontier) := rfl

@[simp] theorem valid_read (w : ℕ) (s : State) (a : ℕ) : valid w s (.read a) ↔ a < s.frontier :=
  Iff.rfl

@[simp] theorem valid_write (w : ℕ) (s : State) (a v : ℕ) :
    valid w s (.write a v) ↔ a < s.frontier ∧ Fits w v := Iff.rfl

@[simp] theorem valid_alloc (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.alloc k) ↔ Fits w (s.frontier + k) := Iff.rfl

@[simp] theorem valid_allocDirty (w : ℕ) (s : State) (k : ℕ) :
    valid w s (.allocDirty k) ↔ Fits w (s.frontier + k) := Iff.rfl

@[simp] theorem charge_read (s : State) (a : ℕ) : charge s (.read a) = 1 := rfl

@[simp] theorem charge_write (s : State) (a v : ℕ) : charge s (.write a v) = 1 := rfl

@[simp] theorem charge_alloc (s : State) (k : ℕ) : charge s (.alloc k) = k + 1 := rfl

@[simp] theorem charge_allocDirty (s : State) (k : ℕ) : charge s (.allocDirty k) = 1 := rfl

/-- Every memory operation costs at least one unit, so the number of operations, hence the
glue run after them, is paid for by their charges. -/
theorem one_le_charge (s : State) (o : Op) : 1 ≤ charge s o := by
  cases o <;> simp

/-- Admissibility of a concrete history is decidable. -/
instance decidableValidHistory (w : ℕ) (s : State) (os : List Op) :
    Decidable ((spec w).ValidHistory s os) := by
  induction os generalizing s with
  | nil => exact isTrue trivial
  | cons o os ih =>
    exact decidable_of_iff (valid w s o ∧ (spec w).ValidHistory (step s o).1 os) Iff.rfl

/-! ## Frontier and frame -/

/-- No operation lowers the frontier. -/
theorem frontier_le_step (s : State) (o : Op) : s.frontier ≤ (step s o).1.frontier := by
  cases o <;> simp

/-- No sequence of operations lowers the frontier. -/
theorem frontier_le_run {w : ℕ} (s : State) (os : List Op) :
    s.frontier ≤ ((spec w).run s os).1.frontier := by
  induction os generalizing s with
  | nil => exact le_rfl
  | cons o os ih => exact (frontier_le_step s o).trans (ih _)

/-- An operation changes an allocated cell only by writing to it. Allocation clears cells at or
above the frontier only. -/
theorem mem_step_of_lt_frontier (s : State) (o : Op) {a : ℕ} (ha : a < s.frontier)
    (hw : ∀ v, o ≠ .write a v) : (step s o).1.mem a = s.mem a := by
  cases o with
  | read => rfl
  | write b v =>
    have hab : a ≠ b := fun h => hw v (h ▸ rfl)
    exact Function.update_of_ne hab v s.mem
  | alloc k => exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  | allocDirty => rfl

/-! ## Word fit -/

/-- The frontier and every cell fit a `w`-bit word. Admissible operations preserve this. -/
structure WellFormed (w : ℕ) (s : State) : Prop where
  /-- The frontier fits a word, hence so does every allocated address. -/
  frontier_fits : Fits w s.frontier
  /-- Every cell holds a word. -/
  mem_fits : ∀ a, Fits w (s.mem a)

/-- Allocated addresses fit a word. -/
theorem WellFormed.fits_of_lt_frontier {w : ℕ} {s : State} (h : WellFormed w s) {a : ℕ}
    (ha : a < s.frontier) : Fits w a :=
  h.frontier_fits.of_le ha.le

/-- Admissible operations preserve well-formedness. -/
theorem WellFormed.step {w : ℕ} {s : State} (h : WellFormed w s) {o : Op} (hv : valid w s o) :
    WellFormed w (Memory.step s o).1 := by
  cases o with
  | read => exact h
  | write a v =>
    refine ⟨h.frontier_fits, fun b => ?_⟩
    by_cases hb : b = a
    · subst hb
      simpa using hv.2
    · simpa [Function.update_of_ne hb] using h.mem_fits b
  | alloc k =>
    refine ⟨hv, fun b => ?_⟩
    simp only [step_alloc, clear]
    split
    · exact fits_zero w
    · exact h.mem_fits b
  | allocDirty k => exact ⟨hv, h.mem_fits⟩

/-- Admissible histories preserve well-formedness. -/
theorem WellFormed.run {w : ℕ} {s : State} (h : WellFormed w s) {os : List Op}
    (hv : (spec w).ValidHistory s os) : WellFormed w ((spec w).run s os).1 := by
  induction os generalizing s with
  | nil => exact h
  | cons o os ih => exact ih (h.step hv.1) hv.2

/-! ## The input convention -/

/-- The word RAM's input convention (`Cslib.WordRAM.Data.init`) as a memory state: the input
length at address `0`, the input words at addresses `1, …, n`, and everything up to the input
allocated. -/
def State.init (input : List ℕ) : State :=
  ⟨(Data.init (r := 0) input).mem, input.length + 1⟩

/-- The input convention is well formed when the input and its frontier fit a word. -/
theorem wellFormed_init {w : ℕ} {input : List ℕ} (hin : InputFits w input)
    (hf : Fits w (input.length + 1)) : WellFormed w (State.init input) := by
  refine ⟨hf, fun a => ?_⟩
  change Fits w (if a = 0 then input.length else input.getD (a - 1) 0)
  split
  · exact hin.1
  · rw [List.getD_eq_getElem?_getD]
    cases hi : input[a - 1]? with
    | none => exact fits_zero w
    | some v => exact hin.2 v (List.mem_of_getElem? hi)

end Cslib.DataStructure.Memory
