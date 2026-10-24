/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Defs
public import Complexity.Computability.WordRAM.Defs

/-!
# Word RAMs as generic RAMs

Every word-RAM basis determines a `GenericRAM.Model`. Values, addresses, constants and the
configuration are natural numbers, with the configuration interpreted as word width. Operations
use the original basis; equality and unsigned comparison are the tests. Only constants and
operation results check word fit, exactly as in `WordRAM.Defs`; existing values and control labels
remain unchecked. Address extraction is the identity, including on arbitrary initial states.

The adapter preserves each step, including faults, and every fuel-bounded result and exact
instruction count. It does not impose new validity assumptions on existing WordRAM states.

## Main definitions

* `Basis.genericModel`: the generic model associated to a word-RAM operation basis.
* `Data.toGeneric`, `State.toGeneric`, `Cond.toGeneric`, `Op.toGeneric`, `Instr.toGeneric`,
  `Program.toGeneric`, `Outcome.toGeneric`: the exact representation adapter.

## Main results

* `step_toGeneric`: one step has the identical continuation, halt or fault.
* `run_toGeneric`, `executes_toGeneric_iff`: output and exact instruction counts agree.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]
-/

@[expose] public section

namespace Cslib.WordRAM

/-- Natural word values and addresses, with exactly the existing word-RAM checking policy.
The two test symbols are `false` for equality and `true` for unsigned comparison. -/
abbrev Basis.genericModel (B : Basis) : GenericRAM.Model where
  Value := ℕ
  Address := ℕ
  Config := ℕ
  Const := ℕ
  operations := B.toSignature
  tests := ⟨Bool, fun _ => 2⟩
  constant _ c := some c
  evalOp w f args := B.interp w f args
  evalTest _ f args := some (if f then decide (args 0 < args 1) else decide (args 0 = args 1))
  admissible w v := decide (Fits w v)
  address _ v := some v
  validMove _ _ := true
  validPC _ _ := true

variable {B : Basis} {r : ℕ}

/-- Identical registers and memory in the generic representation. -/
def Data.toGeneric (B : Basis) (x : Data r) : GenericRAM.Data B.genericModel r :=
  ⟨x.regs, x.mem⟩

/-- Identical control label, registers and memory in the generic representation. -/
def State.toGeneric (B : Basis) (s : State r) : GenericRAM.State B.genericModel r :=
  ⟨s.pc, s.data.toGeneric B⟩

/-- Translate an equality or comparison test. -/
def Cond.toGeneric (B : Basis) : Cond r → GenericRAM.Cond B.genericModel r
  | .eq i j => .test false ![i, j]
  | .lt i j => .test true ![i, j]

/-- Translate a data instruction without changing its registers or operation. -/
def Op.toGeneric : Op B r → GenericRAM.Op B.genericModel r
  | .const d v => .const d v
  | .copy d s => .copy d s
  | .alu f d args => .alu f d args
  | .load d a => .load d a
  | .store a s => .store a s

/-- Translate an instruction without changing its control labels. -/
def Instr.toGeneric : Instr B r → GenericRAM.Instr B.genericModel r
  | .op o => .op o.toGeneric
  | .jump t => .jump t
  | .branch c t => .branch (c.toGeneric B) t
  | .halt i => .halt i

/-- Instruction-for-instruction translation to the generic core. -/
def Program.toGeneric (p : Program B r) : GenericRAM.Program B.genericModel r :=
  p.map Instr.toGeneric

/-- Translation preserves the number of instructions. -/
theorem Program.length_toGeneric (p : Program B r) : p.toGeneric.length = p.length :=
  List.length_map _

/-- The original input convention is an explicit generic initialization, with no charged work. -/
theorem Data.toGeneric_init (B : Basis) (input : List ℕ) :
    (Data.init input : Data r).toGeneric B = GenericRAM.Data.init (M := B.genericModel) 0
      (fun a => if a = 0 then input.length else input.getD (a - 1) 0) := rfl

/-- Translate a step outcome without changing its meaning. -/
def Outcome.toGeneric (B : Basis) : Outcome r → GenericRAM.Outcome B.genericModel r
  | .next s => .next (s.toGeneric B)
  | .halt v => .halt v
  | .fault => .fault

/-- Data instructions preserve success and failure, even on unbounded initial data. -/
theorem Op.eval_toGeneric (o : Op B r) (w : ℕ) (x : Data r) :
    o.toGeneric.eval w (x.toGeneric B) = (o.eval w x).map (Data.toGeneric B) := by
  cases o with
  | alu f d args =>
    change (B.interp w f (x.regs ∘ args)).bind _ = ((B.interp w f (x.regs ∘ args)).bind _).map _
    cases B.interp w f (x.regs ∘ args) with
    | none => rfl
    | some v =>
      by_cases h : Fits w v <;> simp [Basis.genericModel, GenericRAM.Data.put, Data.put, h,
        Data.toGeneric, Data.set, GenericRAM.Data.set]
  | _ =>
    simp [Op.toGeneric, GenericRAM.Op.eval, Basis.genericModel, GenericRAM.Data.put,
      GenericRAM.Data.move, Op.eval, Data.put, Data.toGeneric, Data.set, Data.write,
      GenericRAM.Data.set, GenericRAM.Data.write]

/-- Tests have precisely the original truth value and never fail. -/
theorem Cond.eval_toGeneric (c : Cond r) (w : ℕ) (x : Data r) :
    (c.toGeneric B).eval w (x.toGeneric B) = some (decide (c.Holds x)) := by
  cases c <;> rfl

/-- **Exact step correspondence**, including faults and arbitrary initial states. -/
theorem step_toGeneric (w : ℕ) (p : Program B r) (s : State r) :
    GenericRAM.step w p.toGeneric (s.toGeneric B) = (step w p s).toGeneric B := by
  simp only [GenericRAM.step, State.toGeneric, Basis.genericModel,
    ↓reduceIte, Program.toGeneric, List.getElem?_map]
  cases hp : p[s.pc]? with
  | none => simp [step, hp, Outcome.toGeneric]
  | some i =>
    cases i with
    | op o =>
      simp only [Option.map_some, Instr.toGeneric, Op.eval_toGeneric]
      cases ho : o.eval w s.data <;>
        simp [step, hp, ho, GenericRAM.Outcome.continue, Basis.genericModel, Outcome.toGeneric,
          State.toGeneric]
    | jump t =>
      simp [Instr.toGeneric, step, hp, GenericRAM.Outcome.continue, Basis.genericModel,
        Outcome.toGeneric, State.toGeneric]
    | branch c t =>
      simp [Instr.toGeneric, Cond.eval_toGeneric, step, hp, GenericRAM.Outcome.continue,
        Basis.genericModel, Outcome.toGeneric, State.toGeneric]
    | halt i => simp [Instr.toGeneric, step, hp, Outcome.toGeneric, Data.toGeneric]

/-- The interpreter returns exactly the original output and instruction count at every fuel. -/
theorem run_toGeneric (w : ℕ) (p : Program B r) (fuel : ℕ) (s : State r) :
    GenericRAM.run w p.toGeneric fuel (s.toGeneric B) = run w p fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [GenericRAM.run_succ, step_toGeneric, run_succ]
    cases hs : step w p s <;> simp [Outcome.toGeneric, ih]

/-- Halting executions agree in both directions, with the exact same instruction count. -/
theorem executes_toGeneric_iff {w : ℕ} {p : Program B r} {s : State r} {v n : ℕ} :
    GenericRAM.Executes w p.toGeneric (s.toGeneric B) v n ↔ Executes w p s v n := by
  rw [GenericRAM.executes_iff_exists_run_eq, executes_iff_exists_run_eq]
  simp only [run_toGeneric]

end Cslib.WordRAM
