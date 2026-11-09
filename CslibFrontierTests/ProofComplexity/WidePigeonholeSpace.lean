/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Resolution.WidePigeonholeSpace
import CslibFrontier.Logics.Propositional.Resolution.TreeLikeSpace

/-!
# Tests: clause space of the wide pigeonhole formula

`PHP^m_n` with `0 < n < m` needs clause space exactly `n + 2`, whatever the number of pigeons. With
two pigeons and one hole this is the bound `3` that every formula without the empty clause needs;
with many pigeons and few holes it is far below the number of clauses. With no holes the formula
contains the empty clause, so the hypothesis `0 < n` of the lower bound is needed. A DPLL tree of
rank `1` refutes `x ∧ ¬x` in clause space `3`.
-/

namespace CslibFrontierTests.ProofComplexity.WidePigeonholeSpace

open Cslib Cslib.Logic.PL

/-! ### Exact clause space -/

/-- Two pigeons and one hole: clause space exactly `3`. -/
example : (CNF.pigeonhole 2 1).RefutableInSpace 3 ∧ ¬ (CNF.pigeonhole 2 1).RefutableInSpace 2 :=
  ⟨CNF.refutableInSpace_pigeonhole (by norm_num),
    fun h => by have := CNF.add_two_le_of_refutableInSpace_pigeonhole Nat.one_pos h; omega⟩

/-- A thousand pigeons and five holes: clause space exactly `7`, independently of the number of
pigeons. -/
example (s : ℕ) : (CNF.pigeonhole 1000 5).RefutableInSpace s ↔ 7 ≤ s :=
  CNF.refutableInSpace_pigeonhole_iff (by norm_num) (by norm_num)

/-- The clause space does not grow with the number of pigeons. -/
example (m : ℕ) (hm : 3 < m) : (CNF.pigeonhole m 3).RefutableInSpace 5 ∧
    ¬ (CNF.pigeonhole m 3).RefutableInSpace 4 :=
  ⟨CNF.refutableInSpace_pigeonhole hm,
    fun h => by have := CNF.add_two_le_of_refutableInSpace_pigeonhole (by norm_num) h; omega⟩

/-! ### No holes -/

/-- With one pigeon and no holes, the pigeon clause is empty, so `PHP^1_0` is refutable in clause
space `1`: the lower bound needs a hole. -/
example : (CNF.pigeonhole 1 0).RefutableInSpace 1 := by
  have hnil : ([] : Clause (Fin 1 × Fin 0)) ∈ CNF.pigeonhole 1 0 :=
    CNF.mem_pigeonhole.2 (.inl ⟨0, by simp [CNF.pigeonClause]⟩)
  exact ⟨[.download []], {[]}, .stepL ⟨.download hnil, by simp⟩ .refl, Finset.mem_singleton_self _⟩

/-- Satisfiable pigeonhole formulas are refutable in no clause space, so the upper bound needs more
pigeons than holes. -/
example (s : ℕ) : ¬ (CNF.pigeonhole 2 2).RefutableInSpace s := fun h =>
  h.not_satisfiable (CNF.satisfiable_pigeonhole_iff.2 le_rfl)

/-! ### DPLL trees -/

/-- The tree querying `x`, with the clause `x` on the `false` branch and `¬x` on the `true` branch,
has rank `1` and refutes `x ∧ ¬x` in clause space `3`. -/
example : CNF.RefutableInSpace ([[((), true)], [((), false)]] : CNF Unit) 3 := by
  have ht : (DecisionTree.node () (.leaf [((), true)]) (.leaf [((), false)]) :
      DecisionTree Unit (Clause Unit)).FindsFalsifiedClause [[((), true)], [((), false)]] := by
    intro σ
    cases h : σ () <;> simp [DecisionTree.eval, h]
  simpa [DecisionTree.rank_node] using ht.refutableInSpace

end CslibFrontierTests.ProofComplexity.WidePigeonholeSpace
