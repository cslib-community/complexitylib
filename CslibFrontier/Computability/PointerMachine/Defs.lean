/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Logic.Function.Basic

/-!
# Pointer machines

The pointer machine of [Tarjan1979], §2: finitely many registers and an expandable pool of
records with identical fields. Registers and fields hold either pointers or data. Memory is
reached only by following a pointer held in a register; no instruction computes on pointers.

## Main definitions

This file contains the whole model and no proofs:

* `Model`: the data and the operations and predicates allowed on them.
* `Layout`: the number of registers and of fields per record.
* `State`, `State.Valid`: registers and records, and the states that make sense.
* `Instr`, `Instr.effect`, `Instr.next`: the instructions and their meaning.
* `step`, `Runs`, `Executes`: execution, charging one unit per instruction.

Space is `State.heap.length`, the number of records.

## Differences from the source

* Labels start at zero. Running past the last instruction is not a successful halt.
* The source halts on using an undefined register or field. Here new pointer fields are null
  and data operations/predicates are total, including on `undefined`. Source-faithful programs
  must initialize before reading; no transfer theorem is proved.
* Equality of data is a predicate the `Model` may supply, not a separate instruction.
* Pointers are positions in the list of records, but no instruction takes or returns a position.

Invariants are in `Basic`, data invariants in `Data` and `Renaming`, and symbols in `Symbols`.

## References

[Tarjan1977], §2, and [Tarjan1979], §2. The total semantics here relax the source’s
undefined-value traps; see the differences above.
-/

public section

namespace Cslib.PointerMachine

/-- The data of a pointer machine and the primitives allowed on them. -/
structure Model where
  /-- Data values. -/
  Value : Type
  /-- The content of every data field of a new record. -/
  undefined : Value
  /-- Names of binary operations. A constant is an operation that ignores its operands. -/
  Op : Type
  /-- Names of binary predicates. -/
  Test : Type
  /-- The meaning of each operation. -/
  evalOp : Op → Value → Value → Value
  /-- The meaning of each predicate. -/
  evalTest : Test → Value → Value → Bool

/-- The fixed numbers of registers and of fields per record. -/
structure Layout where
  /-- Number of pointer registers. -/
  ptrRegs : ℕ
  /-- Number of data registers. -/
  dataRegs : ℕ
  /-- Number of pointer fields in each record. -/
  ptrFields : ℕ
  /-- Number of data fields in each record. -/
  dataFields : ℕ

/-- A pointer is null (`none`) or specifies a record by its position in the heap. -/
abbrev Pointer := Option ℕ

/-- A record. -/
structure Record (M : Model) (L : Layout) where
  /-- Pointer fields. -/
  ptr : Fin L.ptrFields → Pointer
  /-- Data fields. -/
  data : Fin L.dataFields → M.Value

variable {M : Model} {L : Layout}

/-- A machine state. -/
structure State (M : Model) (L : Layout) where
  /-- Label of the next instruction. -/
  pc : ℕ
  /-- Pointer registers. -/
  ptr : Fin L.ptrRegs → Pointer
  /-- Data registers. -/
  data : Fin L.dataRegs → M.Value
  /-- All records, in order of creation. -/
  heap : List (Record M L)

/-- A state is valid if every nonnull pointer in a register or in a record specifies a record.
States are meant to be valid, and execution keeps them so (`Runs.valid` in `Basic`). In other
states a pointer that specifies no record acts like null until a later `create` gives it one. -/
@[expose] def State.Valid (x : State M L) : Prop :=
  (∀ r a, x.ptr r = some a → a < x.heap.length) ∧
  ∀ n ∈ x.heap, ∀ f a, n.ptr f = some a → a < x.heap.length

/-- Instructions. Below, `r` and `base` are pointer registers, `s` is a data register and `f` is
a field; `f(base)` is field `f` of the record specified by `base`. As in the source, a load or
store does nothing when `base` is null. -/
inductive Instr (M : Model) (L : Layout) where
  /-- `r ← null`. -/
  | null (r : Fin L.ptrRegs)
  /-- `r ← r'`. -/
  | movePtr (r r' : Fin L.ptrRegs)
  /-- `s ← s'`. -/
  | moveData (s s' : Fin L.dataRegs)
  /-- `r ← f(base)`. -/
  | loadPtr (r : Fin L.ptrRegs) (f : Fin L.ptrFields) (base : Fin L.ptrRegs)
  /-- `s ← f(base)`. -/
  | loadData (s : Fin L.dataRegs) (f : Fin L.dataFields) (base : Fin L.ptrRegs)
  /-- `f(base) ← r`. -/
  | storePtr (f : Fin L.ptrFields) (base : Fin L.ptrRegs) (r : Fin L.ptrRegs)
  /-- `f(base) ← s`. -/
  | storeData (f : Fin L.dataFields) (base : Fin L.ptrRegs) (s : Fin L.dataRegs)
  /-- `s ← s₁ o s₂`. -/
  | op (o : M.Op) (s s₁ s₂ : Fin L.dataRegs)
  /-- Create a record and place a pointer to it in `r`. -/
  | create (r : Fin L.ptrRegs)
  /-- Go to `label`. -/
  | goto (label : ℕ)
  /-- If `r₁ = r₂`, go to `label`. -/
  | ifPtrEq (r₁ r₂ : Fin L.ptrRegs) (label : ℕ)
  /-- If `p(s₁, s₂)`, go to `label`. -/
  | ifTest (p : M.Test) (s₁ s₂ : Fin L.dataRegs) (label : ℕ)
  /-- Cease execution. -/
  | halt

/-- A new record: null pointers and undefined data. -/
@[expose] def Record.blank : Record M L := ⟨fun _ => none, fun _ => M.undefined⟩

namespace State

/-- Place a pointer in register `r`. -/
@[expose] def setPtr (x : State M L) (r : Fin L.ptrRegs) (p : Pointer) : State M L :=
  { x with ptr := Function.update x.ptr r p }

/-- Place a datum in register `s`. -/
@[expose] def setData (x : State M L) (s : Fin L.dataRegs) (v : M.Value) : State M L :=
  { x with data := Function.update x.data s v }

/-- The record specified by the contents of `r`, if any. -/
@[expose] def deref (x : State M L) (r : Fin L.ptrRegs) : Option (Record M L) :=
  (x.ptr r).bind (x.heap[·]?)

/-- Change the record specified by the contents of `r`, if any. -/
@[expose] def modify (x : State M L) (r : Fin L.ptrRegs)
    (g : Record M L → Record M L) : State M L :=
  match x.ptr r with
  | none => x
  | some a => { x with heap := x.heap.modify a g }

end State

/-- The effect of an instruction on registers and records. -/
@[expose] def Instr.effect (x : State M L) : Instr M L → State M L
  | .null r => x.setPtr r none
  | .movePtr r r' => x.setPtr r (x.ptr r')
  | .moveData s s' => x.setData s (x.data s')
  | .loadPtr r f base => (x.deref base).elim x fun n => x.setPtr r (n.ptr f)
  | .loadData s f base => (x.deref base).elim x fun n => x.setData s (n.data f)
  | .storePtr f base r =>
    x.modify base fun n => { n with ptr := Function.update n.ptr f (x.ptr r) }
  | .storeData f base s =>
    x.modify base fun n => { n with data := Function.update n.data f (x.data s) }
  | .op o s s₁ s₂ => x.setData s (M.evalOp o (x.data s₁) (x.data s₂))
  | .create r => { x.setPtr r (some x.heap.length) with heap := x.heap ++ [.blank] }
  | .goto _ | .ifPtrEq .. | .ifTest .. | .halt => x

/-- The label of the instruction executed after this one. -/
@[expose] def Instr.next (x : State M L) : Instr M L → ℕ
  | .goto label => label
  | .ifPtrEq r₁ r₂ label => if x.ptr r₁ = x.ptr r₂ then label else x.pc + 1
  | .ifTest p s₁ s₂ label => if M.evalTest p (x.data s₁) (x.data s₂) then label else x.pc + 1
  | _ => x.pc + 1

/-- Execute one instruction. There is no step from a `halt` or from outside the program. -/
@[expose] def step (code : List (Instr M L)) (x : State M L) : Option (State M L) :=
  match code[x.pc]? with
  | none | some .halt => none
  | some i => some { i.effect x with pc := i.next x }

/-- `Runs code x y n`: the program takes `x` to `y` by executing `n` instructions. -/
abbrev Runs (code : List (Instr M L)) :=
  Relation.RelatesInSteps (fun x y => step code x = some y)

/-- `Executes code x y time`: the program takes `x` to `y` and halts there, having executed
`time` instructions including the `halt`. -/
@[expose] def Executes (code : List (Instr M L)) (x y : State M L) (time : ℕ) : Prop :=
  ∃ n, Runs code x y n ∧ code[y.pc]? = some .halt ∧ time = n + 1

end Cslib.PointerMachine
