/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Algebraic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Concrete algebraic RAM runs: exact arithmetic, indirect memory, branches and faults. -/

@[expose] public section

open Cslib.GenericRAM

namespace GenericRAMAlgebraicTests

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (K : Type*) [Field K] [DecidableEq K] (less : K → K → Option Bool)

/-- Add two input field values, store/load the sum and branch on the loaded value. -/
def sumStore : Program (Algebraic.model K less) 5 :=
  [.op (.const 0 (.word 0)),
   .op (.alu .add 3 ![1, 2]),
   .op (.store 0 3),
   .op (.load 4 0),
   .branch (.test .eq ![3, 4]) 6,
   .halt 1,
   .halt 4]

/-- Inputs occupy two registers; the uninitialized cells contain bounded zero words. -/
def sumStart (a b : K) : State (Algebraic.model K less) 5 :=
  ⟨0, ⟨![.inl 0, .inr a, .inr b, .inl 0, .inl 0], fun _ => .inl 0⟩⟩

theorem sumStore_run (a b : K) :
    run 3 (sumStore K less) 6 (sumStart K less a b) = some (.inr (a + b), 6) := by
  simp! [run, step, sumStore, sumStart, Op.eval, Cond.eval, Outcome.continue,
    Algebraic.model, Algebraic.constant, Algebraic.evalOp, Algebraic.evalTest,
    Algebraic.admissible, Algebraic.address, Data.put, Data.move, Data.set, Data.write,
    Function.update, Function.comp_def, Fin.forall_fin_two, Algebraic.tests,
    Algebraic.operations, Algebraic.Operation.arity]

theorem sumStore_executes (a b : K) :
    Executes 3 (sumStore K less) (sumStart K less a b) (.inr (a + b)) 6 := by
  exact (executes_iff_exists_run_eq).2 ⟨6, sumStore_run K less a b⟩

theorem real_sumStore_executes (a b : ℝ) :
    Executes 3 (sumStore ℝ (fun a b => some (decide (a < b))))
      (sumStart ℝ (fun a b => some (decide (a < b))) a b) (.inr (a + b)) 6 :=
  sumStore_executes ℝ (fun a b => some (decide (a < b))) a b

-- Real semantics are noncomputable, but this is an actual symbolic instruction execution.
example : run 3 (sumStore ℝ (fun a b => some (decide (a < b)))) 6
    (sumStart ℝ (fun a b => some (decide (a < b))) 3 4) = some (.inr 7, 6) := by
  convert sumStore_run ℝ (fun a b => some (decide (a < b))) 3 4 using 1
  norm_num

-- The prime-field instance executes (including reduction modulo the characteristic), while too
-- little fuel does not claim success.
example :
    run 3 (sumStore (ZMod 5) (fun _ _ => none)) 6
      (sumStart (ZMod 5) (fun _ _ => none) 3 4) = some (.inr 2, 6) ∧
    run 3 (sumStore (ZMod 5) (fun _ _ => none)) 5
      (sumStart (ZMod 5) (fun _ _ => none) 3 4) = none := by
  decide

-- Rational syntax is available for reals, while a denominator that vanishes in the field faults
-- rather than interpreting inverse zero, and a field value (or out-of-range word) is never an
-- address.
example (q : ℚ) :
    Algebraic.real.constant 3 (.rational q) = some (.inr (q : ℝ)) ∧
    (Algebraic.primeField 5).constant 3 (.rational (mkRat 1 5)) = none ∧
    Algebraic.real.address 3 (.inr 0) = none ∧
    (Algebraic.primeField 5).address 3 (.inr 0) = none ∧
    (Algebraic.primeField 5).address 3 (.inl 8) = none :=
  ⟨by simp [Algebraic.real, Algebraic.model, Algebraic.constant, Rat.cast_def, q.den_ne_zero],
   by decide, rfl, rfl, by decide⟩

-- Zero divisors, mixed tags, underflow and overflow are actual primitive/instruction faults.
example :
    (Algebraic.primeField 5).evalOp 3 .div ![.inr 1, .inr 0] = none ∧
    (Algebraic.primeField 5).evalOp 3 .div ![.inr 4, .inr 2] = some (.inr 2) ∧
    (Algebraic.primeField 5).evalOp 3 .add ![.inl 1, .inr 2] = none ∧
    (Algebraic.primeField 5).evalOp 3 .wordSub ![.inl 1, .inl 2] = none ∧
    (Algebraic.primeField 5).evalOp 3 .toField ![.inl 8] = none ∧
    step 3 ([.op (.alu .wordAdd 0 ![0, 1])] : Program (Algebraic.primeField 5) 2)
      ⟨0, ⟨![.inl 7, .inl 1], fun _ => .inl 0⟩⟩ = .fault := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, rfl⟩
  have h : (4 : ZMod 5) / 2 = 2 := (div_eq_iff (by decide)).2 (by decide)
  change some (Sum.inr ((4 : ZMod 5) / 2)) = some (Sum.inr (2 : ZMod 5))
  rw [h]

-- Field order is present only in the real instance; finite fields offer equality.
example :
    Algebraic.real.evalTest 3 .lt ![.inr 2, .inr 3] = some true ∧
    (Algebraic.primeField 5).evalTest 3 .lt ![.inr 2, .inr 3] = none :=
  ⟨by
     simp! [Algebraic.real, Algebraic.model, Algebraic.evalTest, Algebraic.admissible,
       Fin.forall_fin_two, show (2 : ℝ) < 3 by norm_num],
   by decide⟩

/-- A real ordered branch skips a failing answer and returns the larger input. -/
noncomputable def orderedBranch : Program Algebraic.real 2 :=
  [.branch (.test .lt ![0, 1]) 2, .halt 0, .halt 1]

example : run 2 orderedBranch 2 ⟨0, ⟨![.inr 2, .inr 3], fun _ => .inl 0⟩⟩ =
    some (.inr 3, 2) := by
  simp! [run, step, orderedBranch, Cond.eval, Outcome.continue, Algebraic.real,
    Algebraic.model, Algebraic.evalTest, Algebraic.admissible, Function.comp_def,
    Fin.forall_fin_two, show (2 : ℝ) < 3 by norm_num]

-- Empty programs and out-of-range control labels fault even with available fuel.
example :
    step 3 ([] : Program (Algebraic.primeField 5) 1)
      ⟨0, Data.init (.inl 0) (fun _ => .inl 0)⟩ = .fault ∧
    step 0 ([.jump 1] : Program (Algebraic.primeField 5) 0)
      ⟨0, Data.init (.inl 0) (fun _ => .inl 0)⟩ = .fault ∧
    step 3 ([.halt 0] : Program (Algebraic.primeField 5) 1)
      ⟨0, Data.init (.inl 8) (fun _ => .inl 0)⟩ = .fault :=
  ⟨rfl, rfl, rfl⟩

end GenericRAMAlgebraicTests
