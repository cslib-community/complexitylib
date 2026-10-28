/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.TwoSAT.Completeness
import Complexity.Computability.Complexity.Problems.TwoSAT.Membership
import Complexity.Computability.Complexity.Problems.TwoSAT.Reduction

/-!
# 2SAT tests

The language `Cslib.Complexity.TwoSAT` is neither empty nor everything: `(x₀ ∨ x₁) ∧ ¬x₀` is in
it, while `x₀ ∧ ¬x₀`, a formula with the empty clause and one with a clause of three literals are
not. In the implication graph of `x₀ ∧ ¬x₀` the unit clauses give the arcs `¬x₀ → x₀` and
`x₀ → ¬x₀`, the cycle that `Cslib.Complexity.notMem_TwoSAT_iff` asks for. The decider of the
complement accepts `x₀ ∧ ¬x₀` and no branch accepts `(x₀ ∨ x₁) ∧ ¬x₀`
(`Cslib.Complexity.TwoSAT.accepts_decider_iff`).

The reduction from the complement of directed connectivity is pinned on two instances: the path
`0 → 1 → 2` from `0` to `2` gives an unsatisfiable formula, the single arc `1 → 0` from `0` to
`1` a satisfiable one.
-/

namespace ComplexityTests.TwoSAT

open Cslib Cslib.Complexity Cslib.Logic.PL

/-- `(x₀ ∨ x₁) ∧ ¬x₀`. -/
def sat : CNF ℕ := [[(0, true), (1, true)], [(0, false)]]

/-- `x₀ ∧ ¬x₀`. -/
def contradiction : CNF ℕ := [[(0, true)], [(0, false)]]

/-- `x₀ ∨ x₁ ∨ x₂`, a clause of three literals. -/
def wide : CNF ℕ := [[(0, true), (1, true), (2, true)]]

theorem sat_mem : sat ∈ TwoSAT :=
  ⟨by decide, fun v => v == 1, rfl⟩

theorem contradiction_notMem : contradiction ∉ TwoSAT := fun ⟨_, σ, hσ⟩ => by
  simp only [contradiction, CNF.eval_cons, Clause.eval_cons, Literal.eval_mk, Clause.eval_nil,
    Bool.or_false, CNF.eval_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hσ
  exact absurd (hσ.1.symm.trans hσ.2) (by decide)

-- A clause of three literals is too wide, satisfiable or not.
example : wide ∉ TwoSAT := fun ⟨hw, _⟩ => absurd (hw _ List.mem_cons_self) (by decide)

example : wide.Satisfiable := ⟨fun _ => true, rfl⟩

-- The empty clause.
example : ([[]] : CNF ℕ) ∉ TwoSAT :=
  fun ⟨_, h⟩ => CNF.not_satisfiable_of_nil_mem List.mem_cons_self h

-- The arcs of the implication graph of `x₀ ∧ ¬x₀`, one for each unit clause.
theorem arc_neg : contradiction.Implies (0, false) (0, true) :=
  ⟨[(0, true)], List.mem_cons_self, by decide, by decide, by decide⟩

theorem arc_pos : contradiction.Implies (0, true) (0, false) :=
  ⟨[(0, false)], by decide, by decide, by decide, by decide⟩

-- The binary clause `x₀ ∨ x₁` gives the arcs `¬x₀ → x₁` and `¬x₁ → x₀`, and no arc `x₀ → x₁`.
example : sat.Implies (0, false) (1, true) :=
  ⟨[(0, true), (1, true)], List.mem_cons_self, by decide, by decide, by decide⟩

example : sat.Implies (1, false) (0, true) :=
  ⟨[(0, true), (1, true)], List.mem_cons_self, by decide, by decide, by decide⟩

example : ¬ sat.Implies (0, true) (1, true) := by
  rintro ⟨c, hc, hneg, hℓ', -⟩
  simp only [sat, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> revert hneg hℓ' <;> decide

-- The cycle through `x₀` and `¬x₀` is the reason the contradiction is outside `TwoSAT`.
example : contradiction ∉ TwoSAT :=
  notMem_TwoSAT_iff.mpr (.inr (.inr ⟨0, .single arc_pos, .single arc_neg⟩))

-- The decider of the complement accepts the contradiction and rejects the satisfiable formula.
example : ∃ s, Turing.CounterProgram.Branches (P := TwoSAT.decider) (w := encCNF contradiction)
    TwoSAT.decider.init s ∧ TwoSAT.decider.instr s.1 = .accept :=
  TwoSAT.accepts_decider_iff.mpr contradiction_notMem

example : ¬ ∃ s, Turing.CounterProgram.Branches (P := TwoSAT.decider) (w := encCNF sat)
    TwoSAT.decider.init s ∧ TwoSAT.decider.instr s.1 = .accept :=
  fun h => TwoSAT.accepts_decider_iff.mp h sat_mem

/-! ### The reduction from the complement of directed connectivity -/

/-- The path `0 → 1 → 2`, from `0` to `2`. -/
def pathInstance : STCONInstance where
  n := 3
  adj a b := decide ((a : ℕ) + 1 = b)
  s := 0
  t := 2

/-- The single arc `1 → 0`, from `0` to `1`. -/
def backInstance : STCONInstance where
  n := 2
  adj a b := decide ((a : ℕ) = 1 ∧ (b : ℕ) = 0)
  s := 0
  t := 1

-- The formulas: `x_s`, `¬x_t`, and `¬x_u ∨ x_v` for each arc `u → v`.
example : TwoSAT.reachabilityFormula pathInstance =
    [[(0, true)], [(2, false)], [(0, false), (1, true)], [(1, false), (2, true)]] := by
  decide

example : TwoSAT.reachabilityFormula backInstance =
    [[(0, true)], [(1, false)], [(1, false), (0, true)]] := by
  decide

-- `2` is reachable from `0` along the path, so its formula is unsatisfiable.
example : TwoSAT.reachabilityFormula pathInstance ∉ TwoSAT :=
  fun h => (TwoSAT.reachabilityFormula_mem_TwoSAT_iff _).mp h
    ((Relation.ReflTransGen.single (show pathInstance.Adj ⟨0, by decide⟩ ⟨1, by decide⟩ from
      rfl)).tail (show pathInstance.Adj ⟨1, by decide⟩ ⟨2, by decide⟩ from rfl))

-- `1` is not reachable from `0` against the arc, and making only `0` true satisfies the formula.
example : TwoSAT.reachabilityFormula backInstance ∈ TwoSAT := by
  rw [show TwoSAT.reachabilityFormula backInstance =
    [[(0, true)], [(1, false)], [(1, false), (0, true)]] by decide]
  exact ⟨by decide, fun v => v == 0, rfl⟩

/-! ### Completeness -/

-- `TwoSATᶜ` reduces in logarithmic space to `TwoSAT` via `NL`-completeness.
example : LogSpaceReducible encCNF encCNF TwoSATᶜ TwoSAT :=
  TwoSAT.logSpaceComplete.2 encCNF TwoSATᶜ TwoSAT.compl_mem_NL

-- `TwoSAT` reduces in logarithmic space to `STCON`, and `STCON` reduces to `TwoSATᶜ`.
example : LogSpaceReducible encCNF encSTCON TwoSAT STCON :=
  STCON.logSpaceComplete.2 encCNF TwoSAT TwoSAT.mem_NL

example : LogSpaceReducible encSTCON encCNF STCON TwoSATᶜ := by
  simpa only [compl_compl] using TwoSAT.logSpaceReducible_compl_STCON.compl

end ComplexityTests.TwoSAT
