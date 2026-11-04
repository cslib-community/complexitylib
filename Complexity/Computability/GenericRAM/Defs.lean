/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Signature
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# RAMs with arbitrary data values

The control labels of a RAM are natural numbers; its memory addresses and data values need not be.
`Model` specifies operations and tests by signatures, a separate type of constant symbols,
admissible produced values, and an explicit partial interpretation of values as addresses.
Neither a real nor a field element is implicitly converted into an integer address.
The configuration parameter has no prescribed meaning in the core; an instance may use a
natural address-word width, or a singleton configuration type.

Operations, tests, constant interpretation and address extraction may fail. Constants and
operations check admissibility of their result; moves and halts have a separate configurable
validity check. Control labels are checked before instructions and after continuing steps.
A successful run costs one per instruction, including its final halt.
Interpretations are mathematical functions: executable instances require executable
interpretations. No bit-cost bound or simulation of real arithmetic by a Turing machine is claimed.

This factors the finite-register, indirect-memory semantics of `Cslib.WordRAM`, adapted from
[MIT–ULB CompGeom Group][Tromino2025]. `Cslib.WordRAM.Basis.genericModel` represents the word
semantics exactly in this core, and the word RAM's interpreter properties, such as
`Cslib.WordRAM.Executes.unique`, are the results below transported along that representation.

## Main definitions

* `Model`: data values, constant symbols, operation/test signatures and their semantics.
* `Op`, `Cond`, `Instr`, `Program`: data instructions, tests and flat programs.
* `Data`, `State`, `Outcome`: machine data, control state and step outcomes.
* `step`, `run`, `Executes`: single steps, fuel-bounded interpretation and exact halting cost.
* `Data.init`: an input convention with explicit default registers and initial memory.

## Main results

* `executes_iff_exists_run_eq`: the interpreter characterizes exact halting executions.
* `Executes.unique`: a halting output and its instruction count are unique.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.GenericRAM

universe u v a c

open Cslib.Circuits

/-- The data and primitive operations of a RAM. The parameter is an external
configuration, not an implicit conversion between values and addresses. -/
structure Model where
  /-- Values stored in registers and memory. -/
  Value : Type u
  /-- Memory addresses, distinct from natural control labels and from data values. -/
  Address : Type a
  /-- Addresses support functional updates. -/
  [decAddress : DecidableEq Address]
  /-- External machine configuration (for example a word width). -/
  Config : Type c
  /-- Literal symbols permitted in a finite program, separately from arbitrary data values. -/
  Const : Type v
  /-- The operation symbols and their arities. -/
  operations : Signature.{0}
  /-- The test symbols and their arities. -/
  tests : Signature.{0}
  /-- Interpret a constant symbol, possibly failing. -/
  constant : Config → Const → Option Value
  /-- Interpret an operation on its register arguments, possibly failing. -/
  evalOp : Config → (f : operations.Op) → (Fin (operations.Arity f) → Value) → Option Value
  /-- Interpret a test on its register arguments, possibly failing. -/
  evalTest : Config → (f : tests.Op) → (Fin (tests.Arity f) → Value) → Option Bool
  /-- Check a newly produced constant or operation result. -/
  admissible : Config → Value → Bool
  /-- Explicitly extract an address. Failure causes a load or store to fault. -/
  address : Config → Value → Option Address

  /-- Check existing values moved by copy/load/store or returned by halt. -/
  validMove : Config → Value → Bool
  /-- Check control labels before an instruction and after a continuing step. -/
  validPC : Config → ℕ → Bool

attribute [instance] Model.decAddress

variable {M : Model} {r : ℕ}

/-- Register contents and indirectly addressed memory. -/
@[ext]
structure Data (M : Model) (r : ℕ) where
  /-- The finite register file. -/
  regs : Fin r → M.Value
  /-- Memory uses the address type chosen by the model. -/
  mem : M.Address → M.Value

namespace Data

/-- Replace a register. -/
def set (x : Data M r) (i : Fin r) (v : M.Value) : Data M r :=
  ⟨Function.update x.regs i v, x.mem⟩

/-- Replace a memory cell. -/
def write (x : Data M r) (a : M.Address) (v : M.Value) : Data M r :=
  ⟨x.regs, Function.update x.mem a v⟩

/-- Store a produced value if it is admissible. -/
def put (k : M.Config) (x : Data M r) (i : Fin r) (v : M.Value) : Option (Data M r) :=
  if M.admissible k v then some (x.set i v) else none

/-- Initialize registers with an explicit default and memory with an explicit function.
Input layout and any length header are conventions supplied by the caller. -/
def init (default : M.Value) (memory : M.Address → M.Value) : Data M r :=
  ⟨fun _ => default, memory⟩

/-- Move an existing value when allowed by the model. -/
def move (k : M.Config) (x : Data M r) (i : Fin r) (v : M.Value) : Option (Data M r) :=
  if M.validMove k v then some (x.set i v) else none

end Data

/-- A test applied to named registers. -/
inductive Cond (M : Model) (r : ℕ) where
  /-- Apply a test symbol to its register arguments. -/
  | test (f : M.tests.Op) (args : Fin (M.tests.Arity f) → Fin r)

/-- A data instruction. Operations and constants are supplied by the model. -/
inductive Op (M : Model) (r : ℕ) where
  /-- Interpret a literal into a register. -/
  | const (d : Fin r) (c : M.Const)
  /-- Copy a register. -/
  | copy (d s : Fin r)
  /-- Apply a primitive operation. -/
  | alu (f : M.operations.Op) (d : Fin r) (args : Fin (M.operations.Arity f) → Fin r)
  /-- Read the address extracted from register `a`. -/
  | load (d a : Fin r)
  /-- Write to the address extracted from register `a`. -/
  | store (a s : Fin r)

/-- Flat instructions, with natural control labels. -/
inductive Instr (M : Model) (r : ℕ) where
  /-- Perform a data instruction and advance. -/
  | op (o : Op M r)
  /-- Jump to a label. -/
  | jump (target : ℕ)
  /-- Jump when the test returns true; advance on false; fault on test failure. -/
  | branch (c : Cond M r) (target : ℕ)
  /-- Return a register's value. -/
  | halt (i : Fin r)

/-- A finite instruction sequence. -/
abbrev Program (M : Model) (r : ℕ) := List (Instr M r)

/-- A natural control label and machine data. -/
@[ext]
structure State (M : Model) (r : ℕ) where
  /-- The next instruction index. -/
  pc : ℕ
  /-- Registers and memory. -/
  data : Data M r

/-- A step continues, halts with a data value, or faults. -/
inductive Outcome (M : Model) (r : ℕ) where
  /-- Continue in a state. -/
  | next (s : State M r)
  /-- Halt with an output value. -/
  | halt (v : M.Value)
  /-- Undefined instruction, primitive, test, address, or inadmissible result. -/
  | fault

/-- Evaluate a test; a failed test is distinct from false. -/
def Cond.eval (k : M.Config) : Cond M r → Data M r → Option Bool
  | .test f args, x => M.evalTest k f (x.regs ∘ args)

/-- Evaluate a data instruction. Loads/stores require explicit successful address extraction. -/
def Op.eval (k : M.Config) : Op M r → Data M r → Option (Data M r)
  | .const d c, x => (M.constant k c).bind (x.put k d)
  | .copy d s, x => x.move k d (x.regs s)
  | .alu f d args, x => (M.evalOp k f (x.regs ∘ args)).bind (x.put k d)
  | .load d a, x => (M.address k (x.regs a)).bind fun p => x.move k d (x.mem p)
  | .store a s, x => (M.address k (x.regs a)).bind fun p =>
      if M.validMove k (x.regs s) then some (x.write p (x.regs s)) else none

/-- Continue only if the destination control label is valid. -/
def Outcome.continue (k : M.Config) (s : State M r) : Outcome M r :=
  if M.validPC k s.pc then .next s else .fault

/-- Execute one instruction. Validate the current control label and every continuation label. -/
def step (k : M.Config) (p : Program M r) (s : State M r) : Outcome M r :=
  if M.validPC k s.pc then
    match p[s.pc]? with
    | none => .fault
    | some (.op o) =>
      match o.eval k s.data with
      | some x => .continue k ⟨s.pc + 1, x⟩
      | none => .fault
    | some (.jump t) => .continue k ⟨t, s.data⟩
    | some (.branch c t) =>
      match c.eval k s.data with
      | some b => .continue k ⟨if b then t else s.pc + 1, s.data⟩
      | none => .fault
    | some (.halt i) =>
      if M.validMove k (s.data.regs i) then .halt (s.data.regs i) else .fault
  else .fault

/-- A nonhalting, nonfaulting transition. -/
def Next (k : M.Config) (p : Program M r) (s t : State M r) : Prop := step k p s = .next t

/-- Exactly the stated number of nonhalting transitions. -/
abbrev Runs (k : M.Config) (p : Program M r) : State M r → State M r → ℕ → Prop :=
  Relation.RelatesInSteps (Next k p)

/-- A halting execution, counting the final halt as one instruction. -/
def Executes (k : M.Config) (p : Program M r) (s : State M r) (v : M.Value) (n : ℕ) : Prop :=
  ∃ t m, Runs k p s t m ∧ step k p t = .halt v ∧ n = m + 1

/-- Run with an instruction budget. `none` means a fault or exhausted fuel, never a halting
output. On success, retain the output and exact number of executed instructions. -/
def run (k : M.Config) (p : Program M r) : ℕ → State M r → Option (M.Value × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match step k p s with
    | .next t => (run k p fuel t).map fun vn => (vn.1, vn.2 + 1)
    | .halt v => some (v, 1)
    | .fault => none

section Executes

variable {w : M.Config} {p : Program M r} {s t u : State M r}
  {v v' : M.Value} {m n n' : ℕ}

theorem Executes.halt (h : step w p s = .halt v) : Executes w p s v 1 :=
  ⟨s, 0, .refl s, h, rfl⟩

theorem Executes.head (h : Next w p s t) (ht : Executes w p t v n) : Executes w p s v (n + 1) := by
  obtain ⟨u, m, hr, hu, rfl⟩ := ht
  exact ⟨u, m + 1, hr.head s t u m h, hu, rfl⟩

/-- A run followed by a halting run is a halting run. -/
theorem Executes.of_runs (h : Runs w p s t m) (ht : Executes w p t v n) :
    Executes w p s v (m + n) := by
  obtain ⟨u, k, hr, hu, rfl⟩ := ht
  exact ⟨u, m + k, h.trans hr, hu, by omega⟩

theorem Executes.pos (h : Executes w p s v n) : 0 < n := by
  obtain ⟨_, _, _, _, rfl⟩ := h
  omega

theorem run_succ :
    run w p (n + 1) s = match step w p s with
      | .next t => (run w p n t).map fun vn => (vn.1, vn.2 + 1)
      | .halt v => some (v, 1)
      | .fault => none := rfl

/-- The interpreter only finds halting runs. -/
theorem Executes.of_run {fuel : ℕ} (h : run w p fuel s = some (v, n)) : Executes w p s v n := by
  induction fuel generalizing s n with
  | zero => simp [run] at h
  | succ fuel ih =>
    rw [run_succ] at h
    split at h
    · next t ht =>
      obtain ⟨⟨v', k⟩, hk, hvn⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at hvn
      obtain ⟨rfl, rfl⟩ := hvn
      exact (ih hk).head ht
    · next v' hv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .halt hv
    · simp at h

/-- A halting run of `n` instructions is found by the interpreter with `n` steps of fuel. -/
theorem Executes.run_eq (h : Executes w p s v n) : run w p n s = some (v, n) := by
  obtain ⟨t, m, hr, ht, rfl⟩ := h
  induction hr using Relation.RelatesInSteps.head_induction_on with
  | hrefl => simp [run_succ, ht]
  | hhead hsc _ ih =>
    rw [run_succ, show step w p _ = .next _ from hsc]
    dsimp only
    rw [ih]
    rfl

/-- More fuel does not change a result of the interpreter. -/
theorem run_mono {fuel fuel' : ℕ} {vn : M.Value × ℕ} (h : run w p fuel s = some vn)
    (hle : fuel ≤ fuel') : run w p fuel' s = some vn := by
  induction fuel generalizing s fuel' vn with
  | zero => simp [run] at h
  | succ fuel ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel' = k + 1 := ⟨fuel' - 1, by omega⟩
    rw [run_succ] at h ⊢
    split at h
    · obtain ⟨vn', hk, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [ih hk (by omega)]
      rfl
    · exact h
    · simp at h

/-- The interpreter computes exactly the halting runs. -/
theorem executes_iff_exists_run_eq : Executes w p s v n ↔ ∃ fuel, run w p fuel s = some (v, n) :=
  ⟨fun h => ⟨n, h.run_eq⟩, fun ⟨_, h⟩ => .of_run h⟩

/-- A halting run is determined by the program, the configuration and the state: its output and its
number of instructions are unique. -/
theorem Executes.unique (h : Executes w p s v n) (h' : Executes w p s v' n') :
    v = v' ∧ n = n' := by
  have := (run_mono h.run_eq (le_max_left n n')).symm.trans (run_mono h'.run_eq (le_max_right n n'))
  simpa using this

/-- A state from which the step faults has no halting run. -/
theorem not_executes_of_fault (h : step w p s = .fault) : ¬Executes w p s v n := by
  intro he
  have hr := he.run_eq
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.pos.ne'
  simp [run_succ, h] at hr

end Executes

end Cslib.GenericRAM
