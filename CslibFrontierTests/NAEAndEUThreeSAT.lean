/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NAEThreeSAT

/-!
# NAE and exact-three distinct-variable SAT examples

These examples distinguish ordinary, exact-one and NAE semantics; exercise satisfiable and
unsatisfiable bounded-occurrence NAE instances; and check malformed-source rejection.
-/

public section

namespace Cslib.Tests.NAEAndEUThreeSAT

open Cslib.Logic.PL Cslib.Complexity

private def triple : CNF ℕ := [[(0, true), (1, true), (2, false)]]

example : triple ∈ EUThreeSAT :=
  ⟨by decide, fun _ => true, by decide⟩

example : triple ∈ NAEEUThreeSAT :=
  ⟨by decide, fun _ => true, by decide⟩

example : ¬CNF.IsExactThreeDistinct ([[(0, true), (0, false), (1, true)]] : CNF ℕ) := by
  decide

example : Clause.eval (fun _ : ℕ => true) [(0, true), (0, true), (1, true)] = true ∧
    Clause.evalOne (fun _ : ℕ => true) [(0, true), (0, true), (1, true)] = false ∧
    CNF.evalNAE (fun _ : ℕ => true) [[(0, true), (0, true), (1, true)]] = false := by
  decide

private def triangle : CNF ℕ :=
  [[(0, true), (1, true)], [(1, true), (2, true)], [(2, true), (0, true)]]

/-- The three binary disequalities cannot all hold. Each variable occurs only twice. -/
private theorem triangle_not_naeSatisfiable : ¬triangle.NAESatisfiable := by
  rintro ⟨σ, hσ⟩
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [triangle, CNF.evalNAE, CNF.eval, Clause.eval, Literal.eval, h0, h1, h2] at hσ

example : triangle ∉ NAEThreeSATThree := fun h => triangle_not_naeSatisfiable h.2.2

example : ([[(0, true), (1, false)]] : CNF ℕ) ∈ NAEThreeSATThree := by
  refine ⟨by decide, fun v => ?_, fun _ => true, by decide⟩
  by_cases h0 : v = 0
  · subst v; decide
  by_cases h1 : v = 1
  · subst v; decide
  simp [CNF.vars, Ne.symm h0, Ne.symm h1]

example : toEUThreeSAT ([[]] : CNF ℕ) = [[]] ∧
    toNAEEUThreeSAT [[(0, true), (0, true), (1, true)]] = [[]] ∧
    toEUThreeSAT [[(0, true), (1, true), (2, true), (3, true)]] = [[]] := by
  decide

example : toEUThreeSAT ([] : CNF ℕ) ∈ EUThreeSAT :=
  (mem_EUThreeSAT_toEUThreeSAT_iff _).mpr ⟨by simp, rfl, fun _ => false, rfl⟩

example : toNAEEUThreeSAT ([] : CNF ℕ) ∈ NAEEUThreeSAT :=
  (mem_NAEEUThreeSAT_toNAEEUThreeSAT_iff _).mpr ⟨by simp, rfl, fun _ => false, rfl⟩

example : toThreeSATThree triangle ∉ NAEThreeSATThree := by
  rw [mem_NAEThreeSATThree_toThreeSATThree_iff]
  exact fun h => triangle_not_naeSatisfiable h.2

example : NPComplete encCNF EUThreeSAT := EUThreeSAT_npComplete
example : NPComplete encCNF NAEEUThreeSAT := NAEEUThreeSAT_npComplete
example : NPComplete encCNF NAEThreeSAT := NAEThreeSAT_npComplete
example : NPComplete encCNF NAEThreeSATThree := NAEThreeSATThree_npComplete
example : EUThreeSATThree ∈ P encCNF := EUThreeSATThree.mem_P

/-- The bounded ordinary exact-distinct case has a satisfying assignment for every valid syntax. -/
theorem exact_distinct_three_occurrence_satisfiable
    (φ : CNF ℕ) (hw : φ.IsExactThreeDistinct) (ho : ∀ v, φ.vars.count v ≤ 3) :
    φ.Satisfiable := CNF.satisfiable_of_exactThreeDistinct_of_count_le_three hw ho

end Cslib.Tests.NAEAndEUThreeSAT
