/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native
public import CslibFrontier.Computability.GenericRAM.SparseMemory.Basic

/-!
# Finite configurations for RAM simulation

A configuration stores a finite register tuple, a natural control label, an explicit default
value, and a distinct-key sparse memory. Its denotation is a generic RAM state. Denotation need
not be injective: recording a default-valued cell and omitting that cell have the same semantics.

Dispatch walks a fixed finite program, comparing the current label with fixed instruction
positions. Successor labels are fixed by those positions. This decomposition supports a native
machine for each fixed program without requiring a uniform interpreter for encoded programs.

## Main definitions

* `FiniteState`: finite configurations with a uniform, explicitly supplied memory default.
* `FiniteState.step`: one finite-state step, including every generic RAM check and fault.

## Main results

* `FiniteState.denote_step`: exact one-step refinement, including continuation, halt and fault.

## References

Uses the generic RAM semantics and Mathlib's association-list memory representation.
-/

@[expose] public section

namespace Cslib.GenericRAM

/-- Finite data from which a total RAM state is interpreted. -/
@[ext]
structure FiniteState (M : Model.{0, 0, 0, 0}) (r : ℕ) where
  /-- Current instruction label. -/
  pc : ℕ
  /-- Fixed finite register tuple. -/
  regs : Fin r → M.Value
  /-- Value returned by an absent memory binding. -/
  default : M.Value
  /-- Distinct stored addresses, including explicitly stored default-valued cells. -/
  memory : SparseMemory M.Address M.Value

namespace FiniteState

variable {M : Model.{0, 0, 0, 0}} {r : ℕ}

/-- Interpret sparse memory using the supplied default. This map is not required to be injective. -/
def denote (s : FiniteState M r) : State M r :=
  ⟨s.pc, s.regs, fun a => SparseMemory.read s.default a s.memory⟩

/-- Replace one register, preserving control and memory. -/
def set (s : FiniteState M r) (d : Fin r) (v : M.Value) : FiniteState M r :=
  { s with regs := Function.update s.regs d v }

/-- Replace one memory binding, preserving control, registers and the default. -/
def write (s : FiniteState M r) (a : M.Address) (v : M.Value) : FiniteState M r :=
  { s with memory := s.memory.insert a v }

@[simp] theorem denote_set (s : FiniteState M r) (d : Fin r) (v : M.Value) :
    (s.set d v).denote = ⟨s.pc, s.denote.data.set d v⟩ := rfl

@[simp] theorem denote_write (s : FiniteState M r) (a : M.Address) (v : M.Value) :
    (s.write a v).denote = ⟨s.pc, s.denote.data.write a v⟩ := by
  simp [write, denote, Data.write, SparseMemory.read_insert]

/-- Validate an existing value before moving it into a register. -/
def move (k : M.Config) (s : FiniteState M r) (d : Fin r) (v : M.Value) :
    Option (FiniteState M r) :=
  if M.validMove k v then some (s.set d v) else none

/-- Finite execution of a fixed data instruction. Checked producers include admissibility. -/
def evalOp (k : M.Config) (o : Op M r) (s : FiniteState M r) :
    Option (FiniteState M r) :=
  match o with
  | .const d c => (M.checkedConstant c k).map (s.set d)
  | .copy d src => s.move k d (s.regs src)
  | .alu f d args => (M.checkedOp f (k, s.regs ∘ args)).map (s.set d)
  | .load d a => do
      let p ← M.address k (s.regs a)
      s.move k d (SparseMemory.read s.default p s.memory)
  | .store a src => do
      let p ← M.address k (s.regs a)
      if M.validMove k (s.regs src) then some (s.write p (s.regs src)) else none

/-- Moving a value commutes with interpretation, including invalid moves. -/
theorem denote_move (k : M.Config) (s : FiniteState M r) (d : Fin r) (v : M.Value) :
    (s.move k d v).map (fun t => t.denote.data) = s.denote.data.move k d v := by
  unfold move Data.move
  split <;> rfl

/-- Finite data execution has exactly the generic data semantics, including failure. -/
theorem denote_evalOp (k : M.Config) (o : Op M r) (s : FiniteState M r) :
    (evalOp k o s).map (fun t => t.denote.data) = o.eval k s.denote.data := by
  cases o with
  | const d c =>
    rw [Model.eval_const_eq_map_checkedConstant]
    simp only [evalOp, Option.map_map]
    rfl
  | copy d src => exact denote_move k s d (s.regs src)
  | alu f d args =>
    rw [Model.eval_alu_eq_map_checkedOp]
    simp only [evalOp, Option.map_map]
    rfl
  | load d a =>
    change ((M.address k (s.regs a)).bind _).map _ =
      (M.address k (s.regs a)).bind _
    cases h : M.address k (s.regs a) with
    | none => rfl
    | some p => exact denote_move k s d (SparseMemory.read s.default p s.memory)
  | store a src =>
    change ((M.address k (s.regs a)).bind _).map _ =
      (M.address k (s.regs a)).bind _
    cases h : M.address k (s.regs a) with
    | none => rfl
    | some p =>
      simp only [Option.bind_some]
      by_cases hm : M.validMove k (s.regs src) = true
      · simpa only [show s.denote.data.regs = s.regs from rfl, hm, ite_true, Option.map_some]
          using congrArg (fun t => some t.data) (denote_write s p (s.regs src))
      · simp [show s.denote.data.regs = s.regs from rfl, hm]

/-- The three finite outcomes use ordinary option and sum encodings. -/
abbrev Result (M : Model.{0, 0, 0, 0}) (r : ℕ) := Option (FiniteState M r ⊕ M.Value)

/-- Interpret all three outcomes; `none` is a fault, not a halted state. -/
def denoteResult : Result M r → Outcome M r
  | none => .fault
  | some (.inl s) => .next s.denote
  | some (.inr v) => .halt v

/-- Check the continuation label before returning the updated configuration. -/
def resume (k : M.Config) (pc : ℕ) (s : FiniteState M r) : Result M r :=
  if M.validPC k pc then some (.inl { s with pc := pc }) else none

@[simp] theorem denote_resume (k : M.Config) (pc : ℕ) (s : FiniteState M r) :
    denoteResult (resume k pc s) = Outcome.continue k ⟨pc, s.denote.data⟩ := by
  unfold resume Outcome.continue
  split <;> rfl

/-- Execute a fixed instruction with a fixed ordinary successor label. -/
def evalInstr (k : M.Config) (nextPC : ℕ) (i : Instr M r) (s : FiniteState M r) :
    Result M r :=
  match i with
  | .op o => do
      let next ← evalOp k o s
      resume k nextPC next
  | .jump target => resume k target s
  | .branch (.test f args) target => do
      let b ← M.evalTest k f (s.regs ∘ args)
      resume k (if b then target else nextPC) s
  | .halt i => if M.validMove k (s.regs i) then some (.inr (s.regs i)) else none

/-- Search fixed instruction positions. The successor is fixed at the matching position. -/
def dispatch (k : M.Config) : Program M r → ℕ → FiniteState M r → Result M r
  | [], _, _ => none
  | i :: p, pc, s =>
    if s.pc = pc then evalInstr k (pc + 1) i s else dispatch k p (pc + 1) s

/-- A finite-state step checks the current label before fixed-program dispatch. -/
def step (k : M.Config) (p : Program M r) (s : FiniteState M r) : Result M r :=
  if M.validPC k s.pc then dispatch k p 0 s else none

/-- Dispatch agrees with indexed lookup wherever the current label is at or above the offset. -/
theorem dispatch_eq_getElem? (k : M.Config) (p : Program M r) (pc : ℕ)
    (s : FiniteState M r) (h : pc ≤ s.pc) :
    dispatch k p pc s = (do
      let i ← p[s.pc - pc]?
      evalInstr k (s.pc + 1) i s) := by
  induction p generalizing pc with
  | nil => simp [dispatch]
  | cons i p ih =>
    by_cases he : s.pc = pc
    · simp [dispatch, he]
    · have hn : s.pc - pc = (s.pc - (pc + 1)) + 1 := by omega
      simp only [dispatch, ite_eq_right he, hn, List.getElem?_cons_succ]
      exact ih (pc + 1) (by omega)

/-- Exact one-step refinement for arbitrary finite configurations, including all faults.
No validity premise on the memory default or the initial registers is hidden in the theorem. -/
theorem denote_step (k : M.Config) (p : Program M r) (s : FiniteState M r) :
    denoteResult (step k p s) = GenericRAM.step k p s.denote := by
  by_cases hc : M.validPC k s.pc = true
  · simp only [step, hc, ite_true, GenericRAM.step, show s.denote.pc = s.pc from rfl]
    rw [dispatch_eq_getElem? k p 0 s (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    cases hp : p[s.pc]? with
    | none => rfl
    | some i =>
      simp only [bind, Option.bind_some]
      cases i with
      | op o =>
        have h := denote_evalOp k o s
        cases he : evalOp k o s with
        | none =>
          simp only [he, Option.map_none] at h
          simp only [evalInstr, he, bind, Option.bind_none, denoteResult, ← h]
        | some t =>
          simp only [he, Option.map_some] at h
          simp only [evalInstr, he, bind, Option.bind_some, denote_resume, ← h]
      | jump t => exact denote_resume k t s
      | branch c t =>
        cases c with
        | test f args =>
          change denoteResult ((M.evalTest k f (s.regs ∘ args)).bind _) =
            match M.evalTest k f (s.regs ∘ args) with
            | some b => Outcome.continue k ⟨if b then t else s.pc + 1, s.denote.data⟩
            | none => Outcome.fault
          cases hb : M.evalTest k f (s.regs ∘ args) with
          | none => rfl
          | some b => exact denote_resume k (if b then t else s.pc + 1) s
      | halt i =>
        by_cases hm : M.validMove k (s.regs i) = true <;>
          simp [evalInstr, denoteResult, denote, hm]
  · simp [step, GenericRAM.step, denote, hc, denoteResult]

end FiniteState
end Cslib.GenericRAM
