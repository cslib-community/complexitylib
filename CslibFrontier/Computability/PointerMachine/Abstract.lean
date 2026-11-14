/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Reference
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# A typed pointer machine

A fixed `Model` chooses finitely many data sorts and binary primitives; a fixed `Layout`
chooses finitely many registers and fields per record. A program is a finite list of `Instr`.
Pointers are null or opaque record identities, separate from data. Only copy, one-edge access,
and allocation can supply a record pointer: there is no address arithmetic or data conversion.

`none` means undefined. Null memory accesses do nothing; allocation initializes all fields to
undefined. Undefined operands and unallocated dereferences fault. Each instruction, including
allocation and final halt, costs one unit; `State.size` counts all allocated records.

This file contains the actual definitions, without their correctness proofs (see `Basic`).
`Reference` supplies only opaque identities and the allocator's membership/fresh-name operations.
The source is [Tarjan1979], §2, pp. 111–112. Typed data sorts, zero-based labels, and explicit
faults are formalization conventions. Data primitives have abstract unit cost, not bit cost.
Union-find assumptions and RAM/SMM/KUM equivalences are separate questions.
-/

public section

namespace Cslib.PointerMachine

/-- Null or a record reference; `none` in a storage slot separately denotes undefined. -/
inductive Pointer where
  /-- Null reference. -/ | null
  /-- Reference to an allocated record. -/ | node (id : NodeId)
  deriving DecidableEq

/-- Fixed typed data primitives: their interpretations receive only data operands. -/
structure Model (k : ℕ) where
  /-- Carrier of each data sort. -/ Value : Fin k → Type
  /-- Equality tests on each data sort. -/ [decValue : ∀ t, DecidableEq (Value t)]
  /-- Binary operation symbols, indexed by input sorts and output sort. -/
  Op : Fin k → Fin k → Fin k → Type
  /-- Binary predicate symbols, indexed by input sorts. -/ Test : Fin k → Fin k → Type
  /-- Fixed partial operation interpretation. -/
  evalOp : {a b c : Fin k} → Op a b c → Value a → Value b → Option (Value c)
  /-- Fixed partial predicate interpretation. -/
  evalTest : {a b : Fin k} → Test a b → Value a → Value b → Option Bool

attribute [instance] Model.decValue

/-- Fixed register and record sizes, independent of input size; `k = 0` permits pure machines. -/
structure Layout (k : ℕ) where
  /-- Number of reference registers. -/ ptrRegs : ℕ
  /-- Number of reference fields per record. -/ ptrFields : ℕ
  /-- Number of data registers of each sort. -/ dataRegs : Fin k → ℕ
  /-- Number of data fields of each sort per record. -/ dataFields : Fin k → ℕ

variable {k : ℕ}

/-- A fixed-format record. `none` in either bank means undefined. -/
structure Node (M : Model k) (L : Layout k) where
  /-- Reference fields. -/ ptr : Fin L.ptrFields → Option Pointer
  /-- Typed data fields. -/ data : (t : Fin k) → Fin (L.dataFields t) → Option (M.Value t)

/-- Registers and heap; only identities below `size` are allocated. -/
structure State (M : Model k) (L : Layout k) where
  /-- Zero-based control label. -/ pc : ℕ
  /-- Reference registers. -/ ptr : Fin L.ptrRegs → Option Pointer
  /-- Typed data registers. -/ data : (t : Fin k) → Fin (L.dataRegs t) → Option (M.Value t)
  /-- Total allocated records, including input records; no implicit reclamation. -/ size : ℕ
  /-- Semantic storage, accessed by instructions only through references. -/
  heap : NodeId → Node M L

variable {M : Model k} {L : Layout k}

/-- Allocated identities; the numeric representation is not part of instruction syntax. -/
@[expose] def State.Allocated (x : State M L) (a : NodeId) : Prop := a.Below x.size

/-- The next fresh identity. Accessible to semantic proofs, not to data operations. -/
@[expose] def State.fresh (x : State M L) : NodeId := NodeId.ofIndex x.size

/-- Valid inputs: every defined nonnull pointer names an allocated record. -/
@[expose] def State.Valid (x : State M L) : Prop :=
  (∀ i a, x.ptr i = some (.node a) → x.Allocated a) ∧
  (∀ a, x.Allocated a → ∀ f b, (x.heap a).ptr f = some (.node b) → x.Allocated b)

/-- A record whose fields are all undefined, as created by allocation. -/
@[expose] def Node.empty : Node M L := ⟨fun _ => none, fun _ _ => none⟩

/-- An empty graph with undefined registers. Inputs are supplied by a separate initial state. -/
@[expose] def State.empty : State M L :=
  ⟨0, fun _ => none, fun _ _ => none, 0, fun _ => .empty⟩

/-- Replace a register of its declared data sort. -/
@[expose] def State.setData (x : State M L) {t : Fin k}
    (dst : Fin (L.dataRegs t)) (v : M.Value t) : State M L :=
  { x with data := Function.update x.data t (Function.update (x.data t) dst (some v)) }

/-- Replace a field of its declared data sort. -/
@[expose] def Node.setData (x : Node M L) {t : Fin k}
    (f : Fin (L.dataFields t)) (v : M.Value t) : Node M L :=
  { x with data := Function.update x.data t (Function.update (x.data t) f (some v)) }

/-- Instruction syntax. Data operands and destinations must have their declared sorts.
There are no literal references, symbol literals, or implicit conversions. -/
inductive Instr (M : Model k) (L : Layout k) where
  /-- Write a defined null pointer. -/ | null (dst : Fin L.ptrRegs)
  /-- Copy a defined pointer register. -/ | copyPtr (dst src : Fin L.ptrRegs)
  /-- Read one reference field; null base is a no-op. -/
  | loadPtr (dst base : Fin L.ptrRegs) (field : Fin L.ptrFields)
  /-- Write one reference field; null base is a no-op. -/
  | storePtr (base : Fin L.ptrRegs) (field : Fin L.ptrFields) (src : Fin L.ptrRegs)
  /-- Copy a datum without changing its sort. -/
  | copyData {t : Fin k} (dst src : Fin (L.dataRegs t))
  /-- Read one data field of the destination's sort; null base is a no-op. -/
  | loadData {t : Fin k} (dst : Fin (L.dataRegs t)) (base : Fin L.ptrRegs)
      (field : Fin (L.dataFields t))
  /-- Write one data field of the source's sort; null base is a no-op. -/
  | storeData {t : Fin k} (base : Fin L.ptrRegs) (field : Fin (L.dataFields t))
      (src : Fin (L.dataRegs t))
  /-- Fresh record with undefined fields. -/ | alloc (dst : Fin L.ptrRegs)
  /-- Apply a symbol from the fixed data basis. -/
  | op {a b c : Fin k} (f : M.Op a b c) (dst : Fin (L.dataRegs c))
      (left : Fin (L.dataRegs a)) (right : Fin (L.dataRegs b))
  /-- Equality of defined references, including null. -/ | ptrEq (a b : Fin L.ptrRegs) (target : ℕ)
  /-- Equality of defined data of the same sort. -/
  | dataEq {t : Fin k} (a b : Fin (L.dataRegs t)) (target : ℕ)
  /-- Apply a predicate from the fixed data basis. -/
  | test {a b : Fin k} (f : M.Test a b) (left : Fin (L.dataRegs a))
      (right : Fin (L.dataRegs b)) (target : ℕ)
  /-- Unconditional jump. -/ | jump (target : ℕ)
  /-- Successful termination; retain the state as output. -/ | halt

/-- Continuing execution, explicit halt, or an invalid/undefined operation. -/
inductive Outcome (M : Model k) (L : Layout k) where
  /-- A continuing state. -/ | next (state : State M L)
  /-- Explicit halt. -/ | halt
  /-- Undefined operand, failed primitive, invalid reference, or invalid control. -/ | fault

/-- Resolve a reference register. Outer `none` means invalid/undefined; `some none` means null. -/
@[expose] def State.address (x : State M L) (i : Fin L.ptrRegs) : Option (Option NodeId) :=
  match x.ptr i with
  | none => none
  | some .null => some none
  | some (.node a) => if a.Below x.size then some (some a) else none

/-- Resolve the base before the memory action; null is a no-op. This is interpreter plumbing. -/
@[expose] def State.access (x : State M L) (base : Fin L.ptrRegs)
    (action : NodeId → Option (State M L)) : Option (State M L) := do
  let a ← x.address base
  match a with
  | none => some x
  | some a => action a

/-- Instruction transition; `step` handles halt separately. -/
@[expose] def Instr.eval (i : Instr M L) (x : State M L) : Option (State M L) :=
  let y := { x with pc := x.pc + 1 }
  match i with
  | .null dst => some { y with ptr := Function.update x.ptr dst (some .null) }
  | .copyPtr dst src => do
    let v ← x.ptr src
    pure { y with ptr := Function.update x.ptr dst (some v) }
  | .loadPtr dst base f => y.access base fun a => do
    let v ← (x.heap a).ptr f
    pure { y with ptr := Function.update x.ptr dst (some v) }
  | .storePtr base f src => y.access base fun a => do let v ← x.ptr src; pure { y with
      heap := Function.update x.heap a
        { x.heap a with ptr := Function.update (x.heap a).ptr f (some v) } }
  | .copyData dst src => do let v ← x.data _ src; pure (y.setData dst v)
  | .loadData dst base f => y.access base fun a => do
    let v ← (x.heap a).data _ f
    pure (y.setData dst v)
  | .storeData base f src => y.access base fun a => do
    let v ← x.data _ src
    pure { y with heap := Function.update x.heap a ((x.heap a).setData f v) }
  | .alloc dst => some { y with
      ptr := Function.update x.ptr dst (some (.node x.fresh))
      size := x.size + 1
      heap := Function.update x.heap x.fresh .empty }
  | .op f dst a b => do
    let va ← x.data _ a
    let vb ← x.data _ b
    let v ← M.evalOp f va vb
    pure (y.setData dst v)
  | .ptrEq a b t => do
    let va ← x.ptr a
    let vb ← x.ptr b
    pure { x with pc := if va = vb then t else x.pc + 1 }
  | .dataEq a b t => do
    let va ← x.data _ a
    let vb ← x.data _ b
    pure { x with pc := if va = vb then t else x.pc + 1 }
  | .test f a b t => do
    let va ← x.data _ a
    let vb ← x.data _ b
    let result ← M.evalTest f va vb
    pure { x with pc := if result then t else x.pc + 1 }
  | .jump t => some { x with pc := t }
  | .halt => none

/-- One instruction; falling off the finite code is a fault, not successful halt. -/
@[expose] def step (code : List (Instr M L)) (x : State M L) : Outcome M L :=
  match code[x.pc]? with
  | none => .fault
  | some .halt => .halt
  | some i => match i.eval x with
    | none => .fault
    | some y => .next y

/-- Exact number of continuing instructions, using CSLib's execution relation. -/
abbrev Runs (code : List (Instr M L)) :=
  Relation.RelatesInSteps (fun x y => step code x = .next y)

/-- Successful execution, charging the final halt. Input preparation is separate. -/
@[expose] def Executes (code : List (Instr M L)) (x y : State M L) (time : ℕ) : Prop :=
  ∃ n, Runs code x y n ∧ step code y = .halt ∧ time = n + 1

end Cslib.PointerMachine
