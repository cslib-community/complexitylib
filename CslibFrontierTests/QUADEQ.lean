/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.QUADEQ

/-! Checked clients of QUADEQ: verifier runs, the SAT reduction on concrete formulas, and the
NP-completeness theorem. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Logic.PL Cslib.Complexity

/-- `u₀ u₁ = 1`, `u₀ + u₁ = 0` (the latter as the diagonal monomials `u₀ u₀ + u₁ u₁`). -/
def bothOne : QuadSystem ℕ := [⟨[(0, 1)], true⟩, ⟨[(0, 0), (1, 1)], false⟩]

-- The certificate lists the values along the first occurrences 0, 1.
example : QUADEQ.verifier (bothOne, [true, true]) = true := by decide
example : QUADEQ.verifier (bothOne, [true, false]) = false := by decide

example : bothOne ∈ QUADEQ :=
  ⟨_, (QUADEQ.verifier_eq_true_iff bothOne [true, true]).1 (by decide)⟩

-- Repeated monomials cancel in pairs: `u₀ u₀ + u₀ u₀ = 1` is the inconsistent `0 = 1`.
example : [(⟨[(0, 0), (0, 0)], true⟩ : QuadEquation ℕ)] ∉ QUADEQ := by
  rintro ⟨a, h⟩
  have := h _ List.mem_cons_self
  simp only [QuadEquation.Holds, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
  revert this
  cases a 0 <;> decide

-- Labels are binary: a label of value `2 ^ 100` costs about a hundred bits, not `2 ^ 100`.
example : QUADEQ.verifier ([⟨[(2 ^ 100, 7)], true⟩], [true, true]) = true := by decide

/-! ### The reduction from SAT -/

-- The single clause `x₀`: auxiliary variables `z₀₀ ↦ 1`, `z₀₁ ↦ 3`, formula variable `x₀ ↦ 0`.
example : toQUADEQ [[(0, true)]] =
    [⟨[(1, 1)], true⟩, ⟨[(3, 3)], false⟩, ⟨[(3, 3), (1, 0), (1, 1)], false⟩] := by decide

-- `x₀ = 1` satisfies it, with `z₀₀ = 1` and `z₀₁ = 0`, read at first occurrences of 1, 3, 0.
example : QUADEQ.verifier (toQUADEQ [[(0, true)]],
    [true, false, false, false, false, false, false, true]) = true := by decide

example : toQUADEQ [[(0, true)]] ∈ QUADEQ :=
  (mem_QUADEQ_toQUADEQ_iff _).2 ⟨fun _ => true, rfl⟩

-- The empty clause is unsatisfiable, and so is its system.
example : toQUADEQ [[]] ∉ QUADEQ := by
  rw [mem_QUADEQ_toQUADEQ_iff]
  rintro ⟨σ, h⟩
  simp [CNF.eval] at h

-- `x₀ ∧ ¬x₀` is unsatisfiable, and so is its system.
example : toQUADEQ [[(0, true)], [(0, false)]] ∉ QUADEQ := by
  rw [mem_QUADEQ_toQUADEQ_iff]
  rintro ⟨σ, h⟩
  revert h
  simp only [CNF.eval, Clause.eval, Literal.eval, List.all_cons, List.any_cons, List.any_nil,
    List.all_nil]
  cases σ 0 <;> decide

/-! ### NP-completeness -/

example : NPComplete QUADEQ.encoding QUADEQ := QUADEQ_npComplete

example : PolyTimeReducible encCNF QUADEQ.encoding SAT QUADEQ := polyTimeReducible_SAT_QUADEQ
