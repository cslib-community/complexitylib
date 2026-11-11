/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Straight-line blocks of assignments

`assignsCode b r k e` assigns the value of `e i` to register `r + i` for each `i < k`, one
instruction each, starting at label `b`. When no expression reads a register being assigned, the
block writes every value as evaluated before the block, whatever the order of the assignments.

## Main definitions

* `Turing.CounterProgram.assignsCode`: the block of assignments.

## Main results

* `Turing.CounterProgram.reaches_assignsCode`: running the block.
-/

public section

namespace Turing

namespace CounterProgram

/-- Straight-line assignments of `e i` to register `r + i` for `i < k`, placed at label `b`. -/
@[expose] def assignsCode (b r k : ℕ) (e : ℕ → Expr) : List Instr :=
  (List.range k).map fun i => Instr.assign (r + i) (e i) (b + i + 1)

@[simp] theorem length_assignsCode (b r k : ℕ) (e : ℕ → Expr) :
    (assignsCode b r k e).length = k := by
  simp [assignsCode]

/-- **Running a block of assignments**, when no expression reads a register being assigned. -/
theorem reaches_assignsCode {P : CounterProgram} {w : List Bool} {B b r : ℕ} {e : ℕ → Expr} :
    ∀ {k : ℕ}, P.CodeAt b (assignsCode b r k e) → ∀ {regs : List ℕ}, r + k ≤ regs.length →
    (∀ i < k, ∀ regs' : List ℕ, (∀ j, (j < r ∨ r + k ≤ j) → regs'.getD j 0 = regs.getD j 0) →
      (e i).eval regs' = (e i).eval regs) →
    (∀ x ∈ regs, x ≤ B) → (∀ i < k, (e i).eval regs ≤ B) →
    ∃ regs', P.Reaches w (P.Running B) (b, regs) (b + k, regs') ∧
      regs'.length = regs.length ∧
      (∀ j, (j < r ∨ r + k ≤ j) → regs'.getD j 0 = regs.getD j 0) ∧
      (∀ i < k, regs'.getD (r + i) 0 = (e i).eval regs) ∧ ∀ x ∈ regs', x ≤ B
  | 0, _, regs, _, _, hB, _ =>
    ⟨regs, Reaches.refl _, rfl, fun _ _ => rfl, fun i hi => absurd hi (by omega), hB⟩
  | k + 1, hP, regs, hlen, he, hB, heB => by
    have hP' : P.CodeAt b (assignsCode b r k e ++ [Instr.assign (r + k) (e k) (b + k + 1)]) := by
      simpa [assignsCode, List.range_succ] using hP
    obtain ⟨regs₁, hr₁, hlen₁, hout₁, hin₁, hB₁⟩ := reaches_assignsCode (w := w)
      (codeAt_append.mp hP').1 (by omega)
      (fun i hi regs' h => he i (by omega) regs' fun j hj => h j (by omega)) hB
      (fun i hi => heB i (by omega))
    have hk : P.instr (b + k) = Instr.assign (r + k) (e k) (b + k + 1) := by
      simpa using (codeAt_append.mp hP').2 0 (by simp)
    have hek : (e k).eval regs₁ = (e k).eval regs :=
      he k (by omega) regs₁ fun j hj => hout₁ j (by omega)
    refine ⟨regs₁.set (r + k) ((e k).eval regs₁),
      hr₁.trans (Reaches.assign hk hB₁ ?_), ?_, ?_, ?_, ?_⟩
    · rw [show b + (k + 1) = b + k + 1 by omega]; exact Reaches.refl _
    · rw [List.length_set, hlen₁]
    · intro j hj
      rw [List.getD_set_ne (by omega), hout₁ j (by omega)]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [List.getD_set_ne (by omega), hin₁ i hi]
      · rw [List.getD_set_self (by omega), hek]
    · exact List.forall_mem_set_of_forall_mem hB₁ (hek ▸ heB k (by omega))

end CounterProgram

end Turing
