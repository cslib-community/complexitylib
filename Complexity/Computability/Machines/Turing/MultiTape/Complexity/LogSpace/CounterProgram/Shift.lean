/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.AllBranches
import Mathlib.Data.List.GetD

/-!
# Shifting counter programs above a choice register

A nondeterministic counter program reads its choice bit in register `0`. Deterministic code
written for registers `0, 1, …` runs unchanged inside such a program once each register `i` is
renamed to `i + 1`. `Expr.shift` and `Instr.shift` perform this renaming, keeping labels.
`padded b code` places `code` at label `b` of a standalone program, so that existing deterministic
correctness lemmas apply to it, and `Reaches.unpad` transfers their runs to the shifted copy placed
at the same label of another program, as oblivious runs that never read the choice.

## Main definitions

* `Turing.CounterProgram.Expr.shift`, `Turing.CounterProgram.Instr.shift`: register renaming.
* `Turing.CounterProgram.padded`: code placed at a label after halting padding.

## Main results

* `Turing.CounterProgram.Reaches.shift`: deterministic runs lift to shifted code.
* `Turing.CounterProgram.Reaches.unpad`: runs of padded code lift to its shifted placement.
-/

public section

namespace Turing

namespace CounterProgram

namespace Expr

/-- Rename every register `i` to `i + 1`. -/
@[expose] def shift : Expr → Expr
  | const k => const k
  | reg i => reg (i + 1)
  | add a b => add a.shift b.shift
  | sub a b => sub a.shift b.shift
  | bit a b => bit a.shift b.shift
  | mul a b => mul a.shift b.shift
  | div a b => div a.shift b.shift
  | mod a b => mod a.shift b.shift

@[simp] theorem eval_shift (e : Expr) (c : ℕ) (regs : List ℕ) :
    e.shift.eval (c :: regs) = e.eval regs := by
  induction e with
  | const k => rfl
  | reg i => simp [shift]
  | add a b iha ihb | sub a b iha ihb | bit a b iha ihb | mul a b iha ihb | div a b iha ihb
  | mod a b iha ihb => simp [shift, iha, ihb]

@[simp] theorem readsChoice_shift (e : Expr) : e.shift.readsChoice = false := by
  induction e with
  | const k => rfl
  | reg i => simp [shift, readsChoice]
  | add a b iha ihb | sub a b iha ihb | bit a b iha ihb | mul a b iha ihb | div a b iha ihb
  | mod a b iha ihb => simp [shift, readsChoice, iha, ihb]

end Expr

namespace Instr

/-- Rename every register `i` to `i + 1`, keeping the labels. -/
@[expose] def shift : Instr → Instr
  | assign i e next => assign (i + 1) e.shift next
  | lt a b yes no => lt a.shift b.shift yes no
  | read e onTrue onFalse onEnd => read e.shift onTrue onFalse onEnd
  | emit b next => emit b next
  | halt out => halt out

@[simp] theorem readsChoice_shift (i : Instr) : i.shift.readsChoice = false := by
  cases i <;> simp [shift, readsChoice]

theorem isStep_shift {i : Instr} (h : i.IsStep) : i.shift.IsStep := by
  cases i <;> exact h

theorem exec_shift (i : Instr) (l c : ℕ) (regs : List ℕ) (b : Option Bool) :
    i.shift.exec (l, c :: regs) b = ((i.exec (l, regs) b).1, c :: (i.exec (l, regs) b).2) := by
  cases i <;> simp [shift, exec]

theorem query_shift (i : Instr) (c : ℕ) (regs : List ℕ) :
    i.shift.query (c :: regs) = i.query regs := by
  cases i <;> simp [shift, query]

theorem halts_shift (i : Instr) : i.shift.halts = i.halts := by
  cases i <;> rfl

end Instr

variable {P Q : CounterProgram} {w : List Bool}

/-- A step of shifted code is the step of the original code, below a register `c`. -/
theorem step_shift {l : ℕ} {regs : List ℕ} (c : ℕ) (h : Q.instr l = (P.instr l).shift) :
    Q.step w (l, c :: regs) = ((P.step w (l, regs)).1, c :: (P.step w (l, regs)).2) := by
  simp only [step_eq, halted, exec, query, h, Instr.halts_shift, Instr.query_shift,
    Instr.exec_shift]
  by_cases hh : (P.instr l).halts = true <;> simp [hh]

/-- **Deterministic runs of code lift to its shift**, below a register `c` at most `B`. -/
theorem Reaches.shift {B c : ℕ} {s s' : Config} (hcB : c ≤ B)
    (hQ : ∀ l, (P.instr l).IsStep → Q.instr l = (P.instr l).shift)
    (h : P.Reaches w (P.Running B) s s') :
    Q.Reaches w (Q.Oblivious B) (s.1, c :: s.2) (s'.1, c :: s'.2) := by
  obtain ⟨t, rfl, ht⟩ := h
  induction t generalizing s with
  | zero => exact Reaches.refl _
  | succ t ih =>
    obtain ⟨hstep, hB⟩ := ht 0 (by omega)
    simp only [Function.iterate_zero, id] at hstep hB
    have hl := hQ s.1 hstep
    refine Reaches.head ⟨by rw [hl]; simp, by rw [hl]; exact Instr.isStep_shift hstep, ?_⟩ ?_
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hcB
      · exact hB r hr
    · rw [step_shift c hl]
      rw [Function.iterate_succ_apply]
      exact ih (fun t' ht' => by
        have := ht (t' + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)

/-- A list of instructions placed at the label `b`, after halts. -/
@[expose] def padded (b : ℕ) (l : List Instr) : CounterProgram where
  code := List.replicate b (.halt []) ++ l
  registers := 0

theorem codeAt_padded (b : ℕ) (l : List Instr) : (padded b l).CodeAt b l := by
  have := codeAt_of_code_eq (P := padded b l) (l := l) (pre := List.replicate b (.halt []))
    (post := []) (by simp [padded])
  simpa using this

theorem padded_instr_of_isStep {b : ℕ} {l : List Instr} (hQ : Q.CodeAt b (l.map Instr.shift))
    {i : ℕ} (hi : ((padded b l).instr i).IsStep) :
    Q.instr i = ((padded b l).instr i).shift := by
  have hlt : i < b + l.length := by
    by_contra hge
    rw [instr, List.getD_eq_default _ _ (by simp [padded]; omega)] at hi
    exact hi
  have hge : b ≤ i := by
    by_contra hlt'
    rw [instr, List.getD_eq_getElem _ _ (by simp [padded]; omega)] at hi
    simp only [padded, List.getElem_append_left (by simp; omega : i < (List.replicate b _).length),
      List.getElem_replicate] at hi
    exact hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hge
  rw [codeAt_padded b l j (by omega), hQ j (by simp; omega)]
  simp

/-- **Unpadding**: a deterministic run of code placed by `padded` is an oblivious run of its
shift placed in another program. -/
theorem Reaches.unpad {B c b : ℕ} {l : List Instr} {s s' : Config} (hcB : c ≤ B)
    (hQ : Q.CodeAt b (l.map Instr.shift))
    (h : (padded b l).Reaches w ((padded b l).Running B) s s') :
    Q.Reaches w (Q.Oblivious B) (s.1, c :: s.2) (s'.1, c :: s'.2) :=
  Reaches.shift hcB (fun _ hi => padded_instr_of_isStep hQ hi) h

end CounterProgram

end Turing
