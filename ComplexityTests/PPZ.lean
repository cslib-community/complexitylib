/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.PPZ

/-! PPZ for k-SAT: a uniquely satisfiable instance, a formula with several satisfying assignments,
critical clauses and random orders. -/

namespace ComplexityTests.PPZ

open Cslib.Logic.PL Cslib.Complexity.PPZ

/-- `x₀ ∧ (¬x₀ ∨ x₁)`: uniquely satisfied by `x₀ = x₁ = true`, with clauses of at most two
literals. -/
def φ : CNF (Fin 2) := [[(0, true)], [(0, false), (1, true)]]

theorem φ_sat : φ.eval (fun _ => true) = true := by decide

theorem φ_unique : ∀ τ, φ.eval τ = true → τ = fun _ => true := by
  intro τ h
  have h0 : τ 0 = true := by
    have := (CNF.eval_eq_true_iff τ φ).mp h [(0, true)] (by simp [φ])
    simpa [Clause.eval, Literal.eval] using this
  have h1 : τ 1 = true := by
    have := (CNF.eval_eq_true_iff τ φ).mp h [(0, false), (1, true)] (by simp [φ])
    simpa [Clause.eval, Literal.eval, h0] using this
  funext i
  fin_cases i <;> assumption

-- One PPZ round finds the solution with probability at least `2^{-(1 - 1/2) · 2} = 1/2`.
example : (2 : ℝ) ^ (-((1 - 1 / ((2 : ℕ) : ℝ)) * (2 : ℕ))) ≤
    ((round φ) fun x => some ((fun _ => true) x)).toReal :=
  round_success (by norm_num) φ_sat φ_unique (by decide)

/-- `x₀`: satisfied by two of the four assignments, with unit clauses only. -/
def ψ : CNF (Fin 2) := [[(0, true)]]

-- With unit clauses PPZ always finds a satisfying assignment: `2^{-(1 - 1/1) · 2} = 1`.
example : (1 : ℝ) ≤ ((round ψ).toOuterMeasure
    {τ | ∃ σ, ψ.eval σ = true ∧ τ = fun x => some (σ x)}).toReal :=
  calc
    (1 : ℝ) = 2 ^ (-((1 - 1 / ((1 : ℕ) : ℝ)) * (2 : ℕ))) := by norm_num
    _ ≤ _ := round_success_of_satisfiable le_rfl ⟨fun _ => true, by decide⟩ (by decide)

-- Each of three variables comes last in a third of the `3! = 6` orders.
example : (Finset.univ.filter fun π : Equiv.Perm (Fin 3) =>
    IsLast π Finset.univ (0 : Fin 3)).card * 3 = 6 := by
  have h := card_isLast_mul (n := 3) (S := Finset.univ) (Finset.mem_univ (0 : Fin 3))
  simpa [Nat.factorial] using h

/-! ### Prefixes of an order -/

/-- The order `x₂, x₀, x₁` of three variables. -/
def π₀ : Equiv.Perm (Fin 3) := Equiv.swap 0 2 * Equiv.swap 1 2

example : π₀ 0 = 2 ∧ π₀ 1 = 0 ∧ π₀ 2 = 1 := by decide

-- The first two steps process `x₂` and `x₀`, and step two adds `x₁`.
example : prefixSet π₀ 2 = {0, 2} := by decide
example : prefixSet π₀ 3 = insert 1 (prefixSet π₀ 2) := prefixSet_succ π₀ (by decide)

-- Swapping `x₁` into position one keeps position zero: the new order processes `x₂, x₁` first.
example : EqOnPrefix (Equiv.swap (π₀ 1) 1 * π₀) π₀ 1 ∧
    ¬EqOnPrefix (Equiv.swap (π₀ 1) 1 * π₀) π₀ 2 := by decide
example : prefixSet (Equiv.swap (π₀ ⟨1, by decide⟩) 1 * π₀) 2 = {1, 2} := by
  rw [prefixSet_swap (by decide) (by decide)]
  decide

end ComplexityTests.PPZ
