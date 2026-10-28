/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Signed
import Mathlib.Data.Fin.VecNotation

/-!
# Signed RAM regressions

The reference instruction step below directly follows the bounded RAM in
`LeanTrominoes/ComplexityAbstract.lean` at `6d5b36c1`, using the generic state's data layout.
It is test-only: the public signed machine uses the generic interpreter.
Concrete checks cover successful signed arithmetic, both sign branches, faults, and cost.
-/

namespace ComplexityTests.GenericRAMSigned

open Cslib.GenericRAM Cslib.GenericRAM.Signed

private def next {r : ℕ} (w : ℕ) (s : State model r) : Outcome model r :=
  if s.pc < 2 ^ w then .next s else .fault

private def write {r : ℕ} (w : ℕ) (s : State model r) (dst : Fin r) (v : ℤ) :
    Outcome model r :=
  if Fits w v then next w ⟨s.pc + 1, s.data.set dst v⟩ else .fault

/-- A direct, test-only transcription of the original instruction step. -/
private def referenceStep {r : ℕ} (w : ℕ) (p : Program model r) (s : State model r) :
    Outcome model r :=
  if s.pc ≥ 2 ^ w then .fault else
    match p[s.pc]? with
    | none => .fault
    | some (.op (.const d v)) => write w s d v
    | some (.op (.copy d i)) => write w s d (s.data.regs i)
    | some (.op (.alu f d args)) =>
      write w s d (f.eval (s.data.regs (args 0)) (s.data.regs (args 1)))
    | some (.op (.load d a)) =>
      if s.data.regs a < 0 ∨ s.data.regs a ≥ (2 ^ w : ℕ) then .fault
      else write w s d (s.data.mem (s.data.regs a).toNat)
    | some (.op (.store a i)) =>
      if s.data.regs a < 0 ∨ s.data.regs a ≥ (2 ^ w : ℕ) ∨ ¬Fits w (s.data.regs i)
      then .fault
      else next w ⟨s.pc + 1, s.data.write (s.data.regs a).toNat (s.data.regs i)⟩
    | some (.jump t) => next w ⟨t, s.data⟩
    | some (.branch (.test .eq args) t) =>
      next w ⟨if s.data.regs (args 0) = s.data.regs (args 1) then t else s.pc + 1, s.data⟩
    | some (.branch (.test .lt args) t) =>
      next w ⟨if s.data.regs (args 0) < s.data.regs (args 1) then t else s.pc + 1, s.data⟩
    | some (.halt i) => if Fits w (s.data.regs i) then .halt (s.data.regs i) else .fault

/-- Every instruction agrees with the source policy, even on unbounded initial stores. -/
theorem step_eq_reference {r : ℕ} (w : ℕ) (p : Program model r) (s : State model r) :
    step w p s = referenceStep w p s := by
  unfold step referenceStep
  by_cases hpc : s.pc < 2 ^ w
  · simp only [model, hpc, decide_true, ite_true, not_le.mpr hpc, ite_false]
    cases hp : p[s.pc]? with
    | none => rfl
    | some i =>
      cases i with
      | op o =>
        cases o <;>
          simp only [Op.eval, Data.put, Data.move, model, write, next, Outcome.continue,
            Option.bind_some, decide_eq_true_eq] <;> split_ifs <;> simp_all
        omega
      | jump t => simp [Outcome.continue, next, model]
      | branch c t =>
        cases c with
        | test f args => cases f <;> simp [Cond.eval, model, Test.eval, next, Outcome.continue]
      | halt i => simp
  · simp [model, hpc, Nat.le_of_not_gt hpc]

/-- A genuine subtraction below zero, followed by multiplication by a negative integer. -/
private def negativeProgram : Program model 2 :=
  [.op (.const 0 2), .op (.const 1 5), .op (.alu .sub 0 ![0, 1]),
    .op (.const 1 (-2)), .op (.alu .mul 0 ![0, 1]), .halt 0]

example :
    run (M := model) 4 negativeProgram 6 (initial []) = some (6, 6) ∧
    run (M := model) 4 negativeProgram 5 (initial []) = none :=
  ⟨rfl, rfl⟩

/-- The original sign program has two paths, each costing six including halt. -/
private def signProgram : Program model 2 :=
  [.op (.const 0 1), .op (.load 1 0), .op (.const 0 0), .branch (.test .lt ![1, 0]) 6,
    .op (.const 0 0), .halt 0, .op (.const 0 1), .halt 0]

example :
    (InputFits 4 [-3] ∧ InputFits 4 [0]) ∧
    run (M := model) 4 signProgram 6 (initial [-3]) = some (1, 6) ∧
    run (M := model) 4 signProgram 6 (initial [0]) = some (0, 6) :=
  ⟨by unfold InputFits; decide, rfl, rfl⟩

private def state (v : ℤ) (pc : ℕ := 0) : State model 1 :=
  ⟨pc, ⟨fun _ => v, fun _ => v⟩⟩

/-! Both signed boundaries, overflow, and Lean's total zero-divisor convention. -/
example :
    (Fits 4 (-8) ∧ Fits 4 7 ∧ ¬Fits 4 (-9) ∧ ¬Fits 4 8) ∧
    step (M := model) 4 [.op (.alu .add 0 ![0, 0])] (state 7) = .fault ∧
    step (M := model) 4 [.op (.const 0 (-9))] (state 0) = .fault ∧
    (Arithmetic.eval .div (-3) 0 = 0 ∧ Arithmetic.eval .mod (-3) 0 = -3) :=
  ⟨by decide, rfl, rfl, by decide⟩

/-! Copy, load, store, and halt reject invalid values, even in arbitrary supplied states. -/
example :
    step (M := model) 4 [.op (.copy 0 0)] (state 8) = .fault ∧
    step (M := model) (r := 1) 4 [.op (.load 0 0)] ⟨0, ⟨fun _ => 0, fun _ => 8⟩⟩ = .fault ∧
    step (M := model) 4 [.op (.store 0 1)] ⟨0, ⟨![0, 8], fun _ => 0⟩⟩ = .fault ∧
    step (M := model) 4 [.halt 0] (state 8) = .fault :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! Negative and oversized addresses, invalid current/next PCs, and zero width. -/
example :
    step (M := model) 4 [.op (.load 0 0)] (state (-1)) = .fault ∧
    step (M := model) 4 [.op (.store 0 0)] (state 16) = .fault ∧
    step (M := model) 4 [.jump 16] (state 0) = .fault ∧
    step (M := model) 4 (List.replicate 17 (.halt 0)) (state 0 16) = .fault ∧
    step (M := model) 1 [.jump 1, .op (.copy 0 0)] (state 0 1) = .fault ∧
    step (M := model) 0 [.halt 0] (state 0) = .fault ∧
    step (M := model) 0 [.jump 0] (state 0) = .next (state 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- info: 'ComplexityTests.GenericRAMSigned.step_eq_reference' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms step_eq_reference

end ComplexityTests.GenericRAMSigned
