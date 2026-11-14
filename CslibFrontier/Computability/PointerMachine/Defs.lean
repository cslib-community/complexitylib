/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Typed allocating pointer machines

The data sorts and their binary operations are parameters; references are not data.
Finite layouts assign a sort to every data register and field. Operation symbols belong to a
fixed model, not to individual instruction callbacks. Each instruction costs one unit, including
allocation and halt. This is an abstract operation count, not a bit-cost assertion.

The source is [Tarjan1979], section 2, pp. 111–112. Null loads/stores do nothing; newly allocated
fields are undefined. Undefined operands, invalid control, and unallocated dereferences fault here,
separately from explicit halt. Zero-based code labels, typed data layouts, and explicit faults
are formalization conventions. The journal does not fully specify undefined-use behavior.
No deletion, union-find separation, or RAM/SMM/KUM simulation is built into the machine.

## Main definitions

* `Model`, `Layout`: typed data operations and fixed register/record formats.
* `NodeId`, `Pointer`, `Node`, `State`: references, typed storage, and machine states.
* `Instr`, `step`, `Runs`, `Executes`: instruction semantics and exact instruction counts.
-/

public section

namespace Cslib.PointerMachine

/-- A record identity. Its numerical representation is private to the allocator.
There are no arithmetic instances or machine instructions converting identities to data. -/
-- `structureInType` constructs public projection names and cannot resolve this private field.
-- The field stores a natural number, so this identity type is not propositional.
@[nolint structureInType]
structure NodeId where
  private mk ::
  private index : ℕ
  deriving DecidableEq

namespace NodeId
/-- Semantic allocation name, not a machine data operation. -/
def ofIndex (n : ℕ) : NodeId := ⟨n⟩
/-- Whether an identity is in the allocated prefix. -/
def Below (a : NodeId) (n : ℕ) : Prop := a.index < n
/-- Computable decision procedure for the allocator's membership predicate. -/
def decBelow (a : NodeId) (n : ℕ) : Decidable (a.Below n) :=
  inferInstanceAs (Decidable (a.index < n))
instance (a : NodeId) (n : ℕ) : Decidable (a.Below n) := decBelow a n
/-- Allocation labels are distinct. -/
theorem ofIndex_injective : Function.Injective ofIndex := by
  intro a b h
  exact congrArg NodeId.index h
/-- Characterize allocated allocation labels. -/
@[simp] theorem below_ofIndex (a n : ℕ) : (ofIndex a).Below n ↔ a < n := Iff.rfl
/-- Every identity has an allocator label; programs cannot obtain this label. -/
theorem exists_index (a : NodeId) : ∃ n, ofIndex n = a := ⟨a.index, rfl⟩
/-- Extending the allocated prefix adds exactly the fresh identity. -/
theorem below_succ (a : NodeId) (n : ℕ) :
    a.Below (n + 1) ↔ a.Below n ∨ a = ofIndex n := by
  cases a
  simp [Below, ofIndex]; omega
end NodeId

/-- A defined pointer is either null or a reference to a record. Undefined is represented
separately by `none` in a register or field. -/
inductive Pointer where
  /-- Null reference. -/
  | null
  /-- Reference to an allocated record. -/
  | node (id : NodeId)
  deriving DecidableEq

/-- Data sorts and a fixed typed primitive basis. The interpretations see data operands only:
neither references, memory, control, nor allocation state are supplied. Binary primitives
follow Tarjan's instruction format. Mathematical interpretations need not be computable. -/
structure Model (k : ℕ) where
  /-- Carrier of each data sort. -/
  Value : Fin k → Type
  /-- Equality tests on each data sort. -/
  [decValue : ∀ t, DecidableEq (Value t)]
  /-- Binary operation symbols, indexed by input sorts and output sort. -/
  Op : Fin k → Fin k → Fin k → Type
  /-- Binary predicate symbols, indexed by input sorts. -/
  Test : Fin k → Fin k → Type
  /-- Fixed partial operation interpretation. -/
  evalOp : {a b c : Fin k} → Op a b c → Value a → Value b → Option (Value c)
  /-- Fixed partial predicate interpretation. -/
  evalTest : {a b : Fin k} → Test a b → Value a → Value b → Option Bool

attribute [instance] Model.decValue

/-- A finite register file and a uniform fixed-format record layout. Counts are fixed for a
program, independently of input size. A zero-sort layout permits pure pointer machines. -/
structure Layout (k : ℕ) where
  /-- Number of reference registers. -/
  ptrRegs : ℕ
  /-- Number of reference fields per record. -/
  ptrFields : ℕ
  /-- Number of data registers of each sort. -/
  dataRegs : Fin k → ℕ
  /-- Number of data fields of each sort per record. -/
  dataFields : Fin k → ℕ

variable {k : ℕ}

/-- A fixed-format record. `none` in either bank means undefined. -/
structure Node (M : Model k) (L : Layout k) where
  /-- Reference fields. -/
  ptr : Fin L.ptrFields → Option Pointer
  /-- Typed data fields. -/
  data : (t : Fin k) → Fin (L.dataFields t) → Option (M.Value t)

/-- State of a machine. Only record identities below the allocation frontier are allocated.
Entries outside that prefix are inaccessible and overwritten on allocation. -/
structure State (M : Model k) (L : Layout k) where
  /-- Zero-based control label. -/
  pc : ℕ
  /-- Reference registers. -/
  ptr : Fin L.ptrRegs → Option Pointer
  /-- Typed data registers. -/
  data : (t : Fin k) → Fin (L.dataRegs t) → Option (M.Value t)
  /-- Total allocated records, including input records; no implicit reclamation. -/
  size : ℕ
  /-- Semantic storage, accessed by instructions only through references. -/
  heap : NodeId → Node M L

variable {M : Model k} {L : Layout k}

/-- Allocated identities; the numeric representation is not part of instruction syntax. -/
@[expose] def State.Allocated (x : State M L) (a : NodeId) : Prop := a.Below x.size

/-- The next fresh identity. Accessible to semantic proofs, not to data operations. -/
@[expose] def State.fresh (x : State M L) : NodeId := NodeId.ofIndex x.size

/-- Every defined nonnull pointer in the register file and allocated heap names an allocated
record. Undefined fields, cycles, shared nodes, and unreachable allocated nodes are permitted. -/
@[expose] def State.Valid (x : State M L) : Prop :=
  (∀ i a, x.ptr i = some (.node a) → x.Allocated a) ∧
  (∀ a, x.Allocated a → ∀ f b, (x.heap a).ptr f = some (.node b) → x.Allocated b)

/-- A record whose fields are all undefined, as created by allocation. -/
@[expose] def Node.empty : Node M L := ⟨fun _ => none, fun _ _ => none⟩

/-- An empty graph with undefined registers. Inputs are supplied by a separate initial state. -/
@[expose] def State.empty : State M L :=
  ⟨0, fun _ => none, fun _ _ => none, 0, fun _ => .empty⟩

/-- Empty states satisfy allocated-pointer validity. -/
theorem State.empty_valid : (State.empty : State M L).Valid := by
  simp [State.Valid, State.empty, Node.empty]

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
  /-- Write a defined null pointer. -/
  | null (dst : Fin L.ptrRegs)
  /-- Copy a defined pointer register. -/
  | copyPtr (dst src : Fin L.ptrRegs)
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
  /-- Fresh record with undefined fields. -/
  | alloc (dst : Fin L.ptrRegs)
  /-- Apply a symbol from the fixed data basis. -/
  | op {a b c : Fin k} (f : M.Op a b c) (dst : Fin (L.dataRegs c))
      (left : Fin (L.dataRegs a)) (right : Fin (L.dataRegs b))
  /-- Equality of defined references, including null. -/
  | ptrEq (a b : Fin L.ptrRegs) (target : ℕ)
  /-- Equality of defined data of the same sort. -/
  | dataEq {t : Fin k} (a b : Fin (L.dataRegs t)) (target : ℕ)
  /-- Apply a predicate from the fixed data basis. -/
  | test {a b : Fin k} (f : M.Test a b) (left : Fin (L.dataRegs a))
      (right : Fin (L.dataRegs b)) (target : ℕ)
  /-- Unconditional jump. -/
  | jump (target : ℕ)
  /-- Successful termination; retain the state as output. -/
  | halt

/-- Continuing execution, explicit halt, or an invalid/undefined operation. -/
inductive Outcome (M : Model k) (L : Layout k) where
  /-- A continuing state. -/
  | next (state : State M L)
  /-- Explicit halt. -/
  | halt
  /-- Undefined operand, failed primitive, invalid reference, or invalid control. -/
  | fault

/-- Resolve a reference register. Outer `none` means invalid/undefined; `some none` means null. -/
@[expose] def State.address (x : State M L) (i : Fin L.ptrRegs) : Option (Option NodeId) :=
  match x.ptr i with
  | none => none
  | some .null => some none
  | some (.node a) => if a.Below x.size then some (some a) else none

/-- A memory instruction faults on invalid/undefined bases, does nothing on null, and otherwise
acts on exactly the record named by the base register. The callback is semantic plumbing,
not an instruction or a model parameter. -/
@[expose] def State.access (x : State M L) (base : Fin L.ptrRegs)
    (action : NodeId → Option (State M L)) : Option (State M L) := do
  let a ← x.address base
  match a with
  | none => some x
  | some a => action a

/-- Data/control transition. The program counter advances unless a jump is taken.
`halt` is handled by `step`; here it has no continuing transition. -/
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
  | .storePtr base f src => y.access base fun a => do
    let v ← x.ptr src
    pure { y with
      heap := Function.update x.heap a
        { x.heap a with ptr := Function.update (x.heap a).ptr f (some v) } }
  | .copyData dst src => do
    let v ← x.data _ src
    pure (y.setData dst v)
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

/-- A resolved nonnull address comes from the base register and is allocated. -/
theorem State.address_eq_some {x : State M L} {i : Fin L.ptrRegs} {a : NodeId} :
    x.address i = some (some a) ↔ x.ptr i = some (.node a) ∧ x.Allocated a := by
  simp only [State.address, State.Allocated]
  split <;> simp_all [and_comm]

/-- Instructions preserve validity for every data interpretation. -/
theorem Instr.eval_valid {i : Instr M L} {x y : State M L}
    (hx : x.Valid) (h : i.eval x = some y) : y.Valid := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals simp only [State.Valid, State.Allocated, State.setData, Node.setData] at hx ⊢
  all_goals try exact hx
  all_goals constructor
  all_goals first
    | (intro dst a ha
       try simp only [Function.update_apply] at ha
       try split_ifs at ha
       all_goals grind [State.address_eq_some, State.Allocated, State.fresh,
         NodeId.below_ofIndex, NodeId.below_succ])
    | (intro a ha f b hb
       try simp only [Function.update_apply] at hb
       try split_ifs at hb
       all_goals try simp only [Function.update_apply, Node.empty] at hb
       all_goals grind [State.address_eq_some, State.Allocated, State.fresh,
         NodeId.below_ofIndex, NodeId.below_succ])

/-- A continuing instruction allocates at most one record and never deallocates. -/
theorem Instr.eval_size {i : Instr M L} {x y : State M L}
    (h : i.eval x = some y) : x.size ≤ y.size ∧ y.size ≤ x.size + 1 := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals dsimp only [State.setData]
  all_goals exact ⟨by omega, by omega⟩

/-- Every resulting register pointer comes from a register, a single existing edge from a
register, or fresh allocation, independently of the data basis. -/
theorem Instr.eval_provenance {i : Instr M L} {x y : State M L}
    (h : i.eval x = some y) {dst : Fin L.ptrRegs} {a : NodeId}
    (ha : y.ptr dst = some (.node a)) :
    (∃ src, x.ptr src = some (.node a)) ∨
    (∃ base b f, x.ptr base = some (.node b) ∧ x.Allocated b ∧
      (x.heap b).ptr f = some (.node a)) ∨
    (a = x.fresh ∧ y.size = x.size + 1) := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals simp only [State.setData, Function.update_apply] at ha ⊢
  all_goals grind [State.address_eq_some, State.Allocated]

/-- The allocator returns a pointer outside the previous allocated pool. -/
theorem Instr.alloc_fresh {x y : State M L} {dst : Fin L.ptrRegs}
    (h : (Instr.alloc dst).eval x = some y) :
    y.ptr dst = some (.node x.fresh) ∧ ¬x.Allocated x.fresh := by
  simp only [Instr.eval, Option.some.injEq] at h
  subst y
  simp [Function.update_self, State.Allocated, State.fresh]

/-- A continuing program step is exactly evaluation of its current instruction. -/
theorem step_eq_next_iff {code : List (Instr M L)} {x y : State M L} :
    step code x = .next y ↔ ∃ i, code[x.pc]? = some i ∧ i.eval x = some y := by
  unfold step
  split
  · simp_all
  · simp_all [Instr.eval]
  · split <;> simp_all

/-- Program steps preserve allocated-pointer validity. -/
theorem step_valid {code : List (Instr M L)} {x y : State M L}
    (hx : x.Valid) (h : step code x = .next y) : y.Valid := by
  obtain ⟨i, _, hi⟩ := step_eq_next_iff.mp h
  exact i.eval_valid hx hi

/-- A program step allocates at most one record and never deallocates. -/
theorem step_size {code : List (Instr M L)} {x y : State M L}
    (h : step code x = .next y) : x.size ≤ y.size ∧ y.size ≤ x.size + 1 := by
  obtain ⟨i, _, hi⟩ := step_eq_next_iff.mp h
  exact i.eval_size hi

/-- All states of a run from a valid input have allocated pointers. -/
theorem Runs.valid {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) (hx : x.Valid) : y.Valid := by
  induction h with
  | refl => exact hx
  | tail _ _ _ _ hxy ih => exact step_valid ih hxy

/-- Space counts input records plus at most one new record per continuing instruction. -/
theorem Runs.size_le {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) : y.size ≤ x.size + n :=
  h.apply_le_apply_add State.size (fun _ _ hxy => (step_size hxy).2)

/-- Continuing execution is deterministic. -/
theorem step_deterministic {code : List (Instr M L)} {x y z : State M L}
    (hy : step code x = .next y) (hz : step code x = .next z) : y = z :=
  Outcome.next.inj (hy.symm.trans hz)

end Cslib.PointerMachine
