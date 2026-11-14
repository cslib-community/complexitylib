/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.MaxCut.Simple

/-!
# Unweighted maximum cut: tests

Clients of `SimpleMaxCut_npComplete` (Arora–Barak 2007, Exercise 2 §15): cuts of a triangle and
a four-cycle counted through `SimpleMaxCut.card_interedges_eq_crossCount`, the reduction from
NAE EU3SAT on an NAE-satisfiable and an NAE-unsatisfiable formula, and its output size.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.SimpleMaxCut

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Headline results -/

example : NPComplete encSimpleMaxCut SimpleMaxCut := SimpleMaxCut_npComplete

example : SimpleMaxCut ∈ NP encSimpleMaxCut := SimpleMaxCut.mem_NP

example : PolyTimeReducible encCNF encSimpleMaxCut NAEEUThreeSAT SimpleMaxCut :=
  polyTimeReducible_NAEEUThreeSAT_SimpleMaxCut

/-! ### Cuts of small graphs -/

/-- The triangle on `0, 1, 2`. -/
def triangle : Graph := ⟨[0, 1, 2], [(0, 1), (1, 2), (0, 2)]⟩

/-- The cut of the triangle at `S` counts the triangle's edges with one endpoint in `S`. -/
theorem card_interedges_triangle (S : Finset ℕ) :
    (triangle.induced.interedges (S.subtype (· ∈ triangle.vertices))
      (S.subtype (· ∈ triangle.vertices))ᶜ).card =
      SimpleMaxCut.crossCount triangle.edges fun v => decide (v ∈ S) :=
  SimpleMaxCut.card_interedges_eq_crossCount triangle S (by decide) (by decide)

/-- Cutting off one vertex of the triangle cuts two edges. -/
example : (⟨triangle, 2⟩ : SimpleMaxCutInstance) ∈ SimpleMaxCut := by
  refine SimpleMaxCut.mem_SimpleMaxCut_iff.2 ⟨{0}, by decide, ?_⟩
  rw [card_interedges_triangle]
  decide

/-- No cut of the triangle has three edges. -/
example : (⟨triangle, 3⟩ : SimpleMaxCutInstance) ∉ SimpleMaxCut := by
  rintro h
  obtain ⟨S, -, hS⟩ := SimpleMaxCut.mem_SimpleMaxCut_iff.1 h
  rw [card_interedges_triangle] at hS
  revert hS
  simp only [SimpleMaxCut.crossCount, triangle, List.countP_cons, List.countP_nil]
  by_cases h0 : 0 ∈ S <;> by_cases h1 : 1 ∈ S <;> by_cases h2 : 2 ∈ S <;> simp [h0, h1, h2]

/-- The four-cycle is bipartite: the cut `{0, 2}` cuts all four edges. -/
example : (⟨⟨[0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)]⟩, 4⟩ : SimpleMaxCutInstance) ∈
    SimpleMaxCut := by
  refine SimpleMaxCut.mem_SimpleMaxCut_iff.2 ⟨{0, 2}, by decide, ?_⟩
  rw [SimpleMaxCut.card_interedges_eq_crossCount _ _ (by decide) (by decide)]
  decide

/-- The graph has no declared vertices, so no cut reaches `1`. -/
example : (⟨⟨[], []⟩, 1⟩ : SimpleMaxCutInstance) ∉ SimpleMaxCut :=
  empty_not_mem_SimpleMaxCut

/-! ### The reduction -/

/-- `x₀ ∨ x₁ ∨ x₂` is NAE-satisfied by setting only `x₀`. -/
example : toSimpleMaxCut [[(0, true), (1, true), (2, true)]] ∈ SimpleMaxCut :=
  (toSimpleMaxCut_mem_iff (by decide)).2 ⟨fun i => i == 0, by decide⟩

/-- The four sign patterns `+++`, `++-`, `+-+`, `-++` on `x₀, x₁, x₂` contain, for every
assignment, one that is all true or all false, so the formula is not NAE-satisfiable. -/
def naeUnsat : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, false), (1, true), (2, true)]]

example : toSimpleMaxCut naeUnsat ∉ SimpleMaxCut := by
  rw [toSimpleMaxCut_mem_iff (by decide)]
  rintro ⟨σ, hσ⟩
  revert hσ
  simp only [naeUnsat, CNF.evalNAE, CNF.eval, Clause.eval, Literal.eval, List.all_cons,
    List.any_cons, List.all_nil, List.any_nil]
  cases σ 0 <;> cases σ 1 <;> cases σ 2 <;> decide

/-- Four clauses give a graph of `72` edges. -/
example : (toSimpleMaxCut naeUnsat).graph.edges.length = 72 :=
  length_edges_toSimpleMaxCut naeUnsat

example : ComputableInPolyTime toSimpleMaxCut encCNF encSimpleMaxCut := by fun_prop

end CslibFrontierTests.SimpleMaxCut
