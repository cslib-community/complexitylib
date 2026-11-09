/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Interpreter.Step
import all CslibFrontier.Computability.WordRAM.Interpreter.Step
import all CslibFrontier.Computability.WordRAM.ProgramLiterals.Encoding
import all CslibFrontier.Computability.WordRAM.Defs
import all CslibFrontier.Computability.WordRAM.Basis
import all CslibFrontier.Computability.GenericRAM.Simulation.Finite
import all CslibFrontier.Computability.GenericRAM.Simulation.Run

/-!
# Exact refinement of the runtime encoded-program interpreter

Every encoded standard instruction and arbitrary finite state agrees with the
native finite RAM step, including faults, random instructions under deterministic
execution and overflow. No supplied trace, admissibility invariant or simulator
correctness conclusion is used. Programs themselves are runtime inputs.
-/

public section

namespace Cslib.WordRAM.Interpreter

open Cslib.GenericRAM Turing.MultiTapeTM

/-- All finite state fields, without semantic initialization or output observations. -/
def toTuple {r : ℕ} (s : FiniteState Basis.standard.genericModel r) : Tuple r :=
  (s.pc, s.regs, s.default, s.memory)
/-- Reconstruct the identical finite state. -/
def ofTuple {r : ℕ} (s : Tuple r) : FiniteState Basis.standard.genericModel r :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩
/-- Retype fault/continuing/halting outcomes without changing any encoded symbol. -/
def toResult {r : ℕ} (x : FiniteState.Result Basis.standard.genericModel r) : Result r :=
  x.map (Sum.map toTuple id)

/-- Runtime register reads agree with native finite indices. -/
theorem readReg_fin {r : ℕ} (s : Tuple r) (i : Fin r) : readReg s i.val = s.2.1 i := by
  simp [readReg, List.getD_eq_getElem?_getD, i.isLt]

/-- Runtime register updates agree with the actual native update. -/
theorem setReg_toTuple {r : ℕ} (s : FiniteState Basis.standard.genericModel r) (i : Fin r)
    (v : ℕ) : setReg (toTuple s) i.val v = toTuple (s.set i v) := by
  unfold setReg toTuple FiniteState.set
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext j
    by_cases h : j = i
    · subst j
      simp
    · have hv : j.val ≠ i.val := fun he => h (Fin.ext he)
      simp [h, hv]
  · rfl

/-- The runtime operation tag selects exactly the encoded checked operation. -/
theorem binaryDispatch_tag (f : BinOp) (w a b : ℕ) :
    binaryDispatch binaryOps (ProgramLiterals.binTag f) (w, a, b) =
      Basis.standard.genericModel.checkedOp (.bin f) (w, ![a, b]) := by
  cases f <;> simp [ProgramLiterals.binTag, binaryDispatch, binaryOps]

/-- Every instruction row executes with exactly the native instruction semantics. -/
theorem evalRow_record {r : ℕ} (w : ℕ) (i : Instr .standard r)
    (s : FiniteState Basis.standard.genericModel r) :
    evalRow ((w, ProgramLiterals.record i), toTuple s) =
      toResult (FiniteState.evalInstr w (s.pc + 1) i.toGeneric s) := by
  cases i with
  | op o =>
    cases o with
    | alu f d args =>
      cases f with
      | bin f =>
        have hargs : ![s.regs (args (0 : Fin 2)), s.regs (args (1 : Fin 2))] =
            s.regs ∘ args := by
          ext j
          fin_cases j <;> rfl
        have hvalues : ![(toTuple s).2.1 (args (0 : Fin 2)),
            (toTuple s).2.1 (args (1 : Fin 2))] = s.regs ∘ args := hargs
        simp only [evalRow, dispatch, handlers, ProgramLiterals.record, binary,
          binaryDispatch_tag, List.headD_cons, List.getD_cons_zero,
          List.getD_cons_succ, readReg_fin, hvalues, setReg_toTuple, next, toResult,
          FiniteState.evalInstr, FiniteState.evalOp, Instr.toGeneric, Op.toGeneric]
        cases Basis.standard.genericModel.checkedOp (.bin f) (w, s.regs ∘ args) with
        | none =>
          simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, one_ne_zero,
            Basis.genericModel, StandardOp.arity, Fin.isValue, Option.elim_none, Option.map_none,
            FiniteState.resume, Option.bind_eq_bind, Option.bind_none]
        | some v =>
          simp only [OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, one_ne_zero,
            Basis.genericModel, StandardOp.arity, Fin.isValue, Option.elim_some, Option.map_some,
            FiniteState.resume, Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
          rfl
      | width =>
        simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
          List.head?_cons, Option.getD_some, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte,
          Nat.add_one_sub_one, one_ne_zero, tsub_self, width, next, List.getD_eq_getElem?_getD,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Order.lt_two_iff,
          Std.le_refl, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero,
          setReg_toTuple, Basis.genericModel, StandardOp.arity, StandardOp.eval, Fin.isValue,
          BinOp.eval, toResult, FiniteState.evalInstr, Instr.toGeneric, Op.toGeneric,
          FiniteState.evalOp, Model.checkedOp, decide_eq_true_eq, Option.bind_eq_bind,
          Option.bind_some, fits_self, Option.map_some, FiniteState.resume, Option.some.injEq]
        rfl
    | const d v =>
      simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some, dispatch, ↓reduceIte, constant,
        List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.lt_add_one, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, next,
        Nat.one_lt_ofNat, setReg_toTuple, Basis.genericModel, StandardOp.arity, Fin.isValue,
        toResult, FiniteState.evalInstr, Instr.toGeneric, Op.toGeneric, FiniteState.evalOp,
        Model.checkedConstant, fits_iff, decide_eq_true_eq, Option.bind_eq_bind, Option.bind_some,
        Option.map_ite, FiniteState.resume, Option.map_bind, Function.comp_apply, Option.map_some]
      split <;> rfl
    | copy d src =>
      simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some, dispatch, one_ne_zero, ↓reduceIte, tsub_self, copy,
        next, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ,
        List.getElem_cons_zero, Nat.lt_add_one, readReg_fin, setReg_toTuple, Basis.genericModel,
        StandardOp.arity, Fin.isValue, toResult, FiniteState.evalInstr, Instr.toGeneric,
        Op.toGeneric, FiniteState.evalOp, FiniteState.move, FiniteState.resume,
        Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.some.injEq]
      rfl
    | load d a =>
      simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte,
        Nat.add_one_sub_one, one_ne_zero, tsub_self, load, next, List.getD_eq_getElem?_getD,
        List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.one_lt_ofNat,
        getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Nat.lt_add_one, readReg_fin,
        setReg_toTuple, Basis.genericModel, StandardOp.arity, Fin.isValue, toResult,
        FiniteState.evalInstr, Instr.toGeneric, Op.toGeneric, FiniteState.evalOp,
        FiniteState.move, Option.bind_eq_bind, Option.bind_some, FiniteState.resume,
        Option.map_some, Option.some.injEq]
      rfl
    | store a src =>
      simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some, toTuple, Basis.genericModel, StandardOp.arity,
        Fin.isValue, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, one_ne_zero,
        tsub_self, store, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ,
        List.getElem_cons_zero, readReg_fin, Nat.lt_add_one, toResult, FiniteState.evalInstr,
        Instr.toGeneric, Op.toGeneric, FiniteState.evalOp, FiniteState.write, Option.bind_eq_bind,
        Option.bind_some, FiniteState.resume, Option.map_some, Option.some.injEq]
      rfl
  | branch c t =>
    cases c with
    | eq i j =>
      simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some, toTuple, Basis.genericModel, StandardOp.arity,
        Fin.isValue, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, one_ne_zero,
        tsub_self, branchEq, next, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ,
        List.getElem_cons_zero, readReg_fin, Nat.reduceLT, Nat.lt_add_one, toResult,
        FiniteState.evalInstr, Instr.toGeneric, Cond.toGeneric, Bool.false_eq_true,
        Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        FiniteState.resume, Option.bind_eq_bind, Option.bind_some, decide_eq_true_eq,
        Option.map_some, Option.some.injEq]
      rfl
    | lt i j =>
      simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
        List.head?_cons, Option.getD_some, toTuple, Basis.genericModel, StandardOp.arity,
        Fin.isValue, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, one_ne_zero,
        tsub_self, branchLt, next, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil,
        zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ,
        List.getElem_cons_zero, readReg_fin, Nat.reduceLT, Nat.lt_add_one, toResult,
        FiniteState.evalInstr, Instr.toGeneric, Cond.toGeneric, Function.comp_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, FiniteState.resume,
        Option.bind_eq_bind, Option.bind_some, decide_eq_true_eq, Option.map_some,
        Option.some.injEq]
      rfl
  | jump t =>
    simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
      List.head?_cons, Option.getD_some, toTuple, Basis.genericModel, StandardOp.arity,
      Fin.isValue, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, one_ne_zero,
      tsub_self, jump, next, List.getD_eq_getElem?_getD, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Order.lt_two_iff, Std.le_refl, getElem?_pos,
      List.getElem_cons_succ, List.getElem_cons_zero, toResult, FiniteState.evalInstr,
      Instr.toGeneric, FiniteState.resume, Option.map_some, Option.some.injEq]
    rfl
  | halt i =>
    simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
      List.head?_cons, Option.getD_some, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte,
      Nat.add_one_sub_one, one_ne_zero, tsub_self, halt, List.getD_eq_getElem?_getD,
      List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Order.lt_two_iff, Std.le_refl,
      getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, readReg_fin, toResult,
      Basis.genericModel, StandardOp.arity, Fin.isValue, FiniteState.evalInstr, Instr.toGeneric,
      Option.map_some, Option.some.injEq]
    rfl
  | rand d src =>
    simp only [evalRow, handlers, ProgramLiterals.record, List.headD_eq_head?_getD,
      List.head?_cons, Option.getD_some, dispatch, OfNat.ofNat_ne_zero, ↓reduceIte,
      Nat.add_one_sub_one, one_ne_zero, toResult, Basis.genericModel, StandardOp.arity,
      Fin.isValue, FiniteState.evalInstr, Instr.toGeneric, Option.bind_eq_bind, Option.bind_none,
      Option.map_none]
/-- Exact fetch/execute refinement, uniform over the runtime program and every finite state. -/
theorem step_serialize {r : ℕ} (w : ℕ) (p : Program .standard r)
    (s : FiniteState Basis.standard.genericModel r) :
    step ((w, ProgramLiterals.serialize p), toTuple s) =
      toResult (FiniteState.step w p.toGeneric s) := by
  rw [FiniteState.step]
  change _ = toResult (FiniteState.dispatch w p.toGeneric 0 s)
  rw [FiniteState.dispatch_eq_getElem? w p.toGeneric 0 s (Nat.zero_le _)]
  by_cases h : s.pc < p.length
  · simpa [step, ProgramLiterals.serialize, toTuple, Program.toGeneric, h,
      List.getD_eq_getElem?_getD] using evalRow_record w p[s.pc] s
  · simp [step, ProgramLiterals.serialize, toTuple, Program.toGeneric, h,
      toResult]

end Cslib.WordRAM.Interpreter
