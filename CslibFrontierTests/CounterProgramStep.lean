/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Block

/-!
# Stepping through counter programs with `cp_step`

Reads, assignments and comparisons of running configurations, shifted and oblivious instructions,
instructions read off a concrete program, and the diagnostics of failed steps.
-/

namespace CslibFrontierTests.CounterProgramStep

open Turing CounterProgram Expr

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

-- A read and an assignment; the bound after the assignment is not needed, and the step after the
-- assignment is closed by the hypothesis `hreach`.
example {b F : ℕ} (h₀ : P.instr b = .read (mul (const 2) (reg 0)) (b + 1) (b + 2) F)
    (h₁ : P.instr (b + 1) = .assign 0 (add (reg 0) (const 1)) b)
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) (hw : w[2 * regs.getD 0 0]? = some true)
    (hreach : P.Reaches w (P.Running B) (b, regs.set 0 (regs.getD 0 0 + 1)) (b + 2, regs)) :
    P.Reaches w (P.Running B) (b, regs) (b + 2, regs) := by
  cp_step [hw]
  cp_step

-- Two assignments: the bound on the registers after the first is proved from `hB` and a bound on
-- the written value.
example {b : ℕ} (h₀ : P.instr b = .assign 1 (const 3) (b + 1))
    (h₁ : P.instr (b + 1) = .assign 2 (reg 1) (b + 2)) (h3 : 3 ≤ B)
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Running B) (b, regs)
      (b + 2, (regs.set 1 3).set 2 ((regs.set 1 3).getD 1 0)) := by
  cp_step
  cp_step

-- A comparison decided by the value of a register, and a label written `c + 1 + 1`.
example {c : ℕ} (h₀ : P.instr (c + 1 + 1) = .lt (reg 0) (const 3) (c + 3) (c + 4))
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) (h0 : regs.getD 0 0 = 5) :
    P.Reaches w (P.Running B) (c + 2, regs) (c + 4, regs) := by
  cp_step [h0]

-- A comparison the lemmas do not decide: split on its condition and pass the case.
example {b : ℕ} (h₀ : P.instr b = .lt (reg 0) (const 3) (b + 1) (b + 1))
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Running B) (b, regs) (b + 1, regs) := by
  by_cases h : regs.getD 0 0 < 3
  · cp_step [h]
  · cp_step [h]

-- A concrete program: the instructions are read off by evaluation, and the bounds on a list of
-- registers written out are proved entry by entry.
example (hB : 3 ≤ B) :
    (⟨[.assign 0 (const 1) 1, .lt (reg 0) (const 2) 2 3], 1⟩ : CounterProgram).Reaches w
      (CounterProgram.Running ⟨[.assign 0 (const 1) 1, .lt (reg 0) (const 2) 2 3], 1⟩ B)
      (0, [0]) (2, [1]) := by
  cp_step [List.set_cons_zero]
  cp_step [List.getD_cons_zero]

-- A shifted assignment, above the choice in register `0`.
example {l next c : ℕ} (h : P.instr l = (Instr.assign 1 (reg 1) next).shift) (hc : c ≤ B)
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Oblivious B) (l, c :: regs) (next, c :: regs.set 1 (regs.getD 1 0)) := by
  cp_step

-- An oblivious assignment: `1 ≠ 0` and `(reg 2).readsChoice = false` are decided.
example {l next : ℕ} (h : P.instr l = .assign 1 (reg 2) next)
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Oblivious B) (l, regs) (next, regs.set 1 (regs.getD 2 0)) := by
  cp_step

-- An oblivious comparison of registers above the choice.
example {l yes no : ℕ} (h : P.instr l = .lt (reg 1) (add (reg 2) (const 1)) yes no)
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) (h12 : regs.getD 1 0 ≤ regs.getD 2 0) :
    P.Reaches w (P.Oblivious B) (l, regs) (yes, regs) := by
  cp_step [Nat.lt_succ_of_le h12]

/--
error: cp_step: no stepping rule applies to
  P.Reaches w (P.Running B) (b, regs) (b + 1, regs)
It needs a hypothesis `P.instr l = i` for the label `l`, or a program `P` whose instruction at `l` evaluates, an assignment, comparison or read `i` with its rule imported, and a label that is not a conditional.
-/
#guard_msgs in
example {b : ℕ} (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Running B) (b, regs) (b + 1, regs) := by
  cp_step

/--
error: cp_step: could not prove the side condition
  ∀ r ∈ regs, r ≤ B
of `Turing.CounterProgram.Reaches.assign`. Add it as a hypothesis.
-/
#guard_msgs in
example {b : ℕ} (h : P.instr b = .assign 0 (const 0) (b + 1)) (regs : List ℕ) :
    P.Reaches w (P.Running B) (b, regs) (b + 1, regs.set 0 0) := by
  cp_step

/--
error: cp_step: the label
  if regs.getD 0 0 < 3 then b + 1 else b + 2
is not decided. Split on its condition and pass the case to `cp_step` as a simp lemma.
-/
#guard_msgs in
example {b : ℕ} (h₀ : P.instr b = .lt (reg 0) (const 3) (b + 1) (b + 2))
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) :
    P.Reaches w (P.Running B) (b, regs) (b + 1, regs) := by
  cp_step
  cp_step

/--
error: cp_step: the goal is not a reachability goal `P.Reaches w Q s s'`
  1 = 1
-/
#guard_msgs in
example : 1 = 1 := by
  cp_step

end CslibFrontierTests.CounterProgramStep
