/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.IndependentSet
import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Tactic.PolyTime

/-!
# Karp reductions and NP-completeness tests

Concrete, boundary, and `fun_prop` checks for `ThreeSAT`, `IndependentSet`, and `Clique`.
-/

namespace ComplexityTests.KarpReductions

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Headline complexity class results -/

-- Each NP-completeness theorem witnesses both membership in `NP` and a polynomial-time
-- reduction from `SAT`.
example : ThreeSAT ∈ NP encCNF ∧
    PolyTimeReducible encCNF encCNF SAT ThreeSAT :=
  ⟨ThreeSAT_npComplete.1, ThreeSAT_npComplete.2 encCNF SAT SAT.mem_NP⟩

example : IndependentSet ∈ NP (encPair encGraph encNat) ∧
    PolyTimeReducible encCNF (encPair encGraph encNat) SAT IndependentSet :=
  ⟨IndependentSet_npComplete.1, IndependentSet_npComplete.2 encCNF SAT SAT.mem_NP⟩

example : Clique ∈ NP (encPair encGraph encNat) ∧
    PolyTimeReducible encCNF (encPair encGraph encNat) SAT Clique :=
  ⟨Clique_npComplete.1, Clique_npComplete.2 encCNF SAT SAT.mem_NP⟩

example : PolyTimeReducible encCNF (encPair encGraph encNat) SAT Clique :=
  polyTimeReducible_SAT_IndependentSet.trans polyTimeReducible_IndependentSet_Clique

-- Hardness chains along reductions with dot notation: the hardness statement is not specialized
-- to a type of instances before `.trans` is resolved.
example : NPHard (encPair encGraph encNat) Clique :=
  (CookLevin.SAT_npHard.trans polyTimeReducible_SAT_IndependentSet).trans
    polyTimeReducible_IndependentSet_Clique

/-! ### Compositional `fun_prop` synthesis -/

example : ComputableInPolyTime toThreeSAT encCNF encCNF := by fun_prop

example : ComputableInPolyTime ThreeSAT.verifier (encPair encCNF encBits) encBool := by
  fun_prop

example : ComputableInPolyTime SAT.toIndependentSet encCNF (encPair encGraph encNat) := by
  fun_prop

example : ComputableInPolyTime Graph.compl encGraph encGraph := by fun_prop

example : ComputableInPolyTime IndependentSet.verifier
    (encPair (encPair encGraph encNat) encBits) encBool := by
  fun_prop

example : ComputableInPolyTime Clique.verifier
    (encPair (encPair encGraph encNat) encBits) encBool := by
  fun_prop

example : ComputableInPolyTime
    (fun φ : CNF ℕ => let x := SAT.toIndependentSet φ; (x.1.compl, x.2))
    encCNF (encPair encGraph encNat) := by
  fun_prop

/-! ### `ThreeSAT` concrete and boundary tests -/

-- Empty formula (satisfiable 3-CNF) and empty clause (unsatisfiable 3-CNF).
example : ThreeSAT.verifier ([], []) = true := rfl
example : ThreeSAT.verifier ([[]], []) = false := rfl

-- A satisfiable 4-literal clause is rejected by ThreeSAT.verifier directly,
-- but accepted after `toThreeSAT` splits it into clauses of width 3.
private def clause4 : CNF ℕ := [[(0, true), (1, true), (2, true), (3, true)]]

example : SAT.verifier (clause4, [true, false, false, false]) = true := rfl
example : ThreeSAT.verifier (clause4, [true, false, false, false]) = false := rfl
example : toThreeSAT clause4 =
    [[(0, true), (2, true), (1, true)], [(1, false), (4, true), (6, true)]] := rfl
example : ThreeSAT.verifier (toThreeSAT clause4, [true, false, false, false, false]) = true := rfl

-- Sparse binary variable labels do not cause unary blowup in `toThreeSAT` or `ThreeSAT.verifier`.
example : ThreeSAT.verifier (toThreeSAT [[(2 ^ 80, true), (2 ^ 80 + 1, false)]], [true, false]) =
    true := by decide

/-! ### `IndependentSet` and `Clique` concrete and boundary tests -/

-- Empty graph: m = 0 is accepted, m > 0 is rejected.
example : IndependentSet.verifier ((([], []), 0), []) = true := rfl
example : IndependentSet.verifier ((([], []), 1), [true]) = false := rfl
example : Clique.verifier ((([], []), 0), []) = true := rfl
example : Clique.verifier ((([], []), 1), [true]) = false := rfl

-- Oversized binary target `m = 2 ^ 100` is rejected in binary without unary expansion.
example : IndependentSet.verifier ((([0, 1], []), 2 ^ 100), [true, true]) = false := by decide
example : Clique.verifier ((([0, 1], [(0, 1)]), 2 ^ 100), [true, true]) = false := by decide

-- Duplicate vertices in `G.1` are deduplicated at their first occurrence by `selectDistinct`,
-- so selecting two copies of vertex `0` cannot forge an independent set or clique of size 2.
example : selectDistinct [0, 0, 1] [true, true, false] = [0] := rfl
example : selectDistinct [0, 0, 1] [true, false, true] = [0, 1] := rfl
example : IndependentSet.verifier ((([0, 0, 1], []), 2), [true, true, false]) = false := rfl
example : IndependentSet.verifier ((([0, 0, 1], []), 2), [true, false, true]) = true := rfl

-- Edges with endpoints outside `G.1` and self-loops in `G.2` do not create adjacency on `G.1`.
example : IndependentSet.verifier
    ((([10, 20], [(10, 99), (99, 20), (10, 10)]), 2), [true, true]) = true := rfl

-- Sparse binary vertex labels in `IndependentSet`, `Graph.compl`, and `Clique`.
private def sparseGraph : Graph :=
  ([2 ^ 80, 2 ^ 80 + 1, 2 ^ 80 + 2], [(2 ^ 80, 2 ^ 80 + 1)])

example : IndependentSet.verifier ((sparseGraph, 2), [true, false, true]) = true := by decide
example : IndependentSet.verifier ((sparseGraph, 2), [true, true, false]) = false := by decide
example : Clique.verifier ((sparseGraph.compl, 2), [true, false, true]) = true := by decide
example : Clique.verifier ((sparseGraph.compl, 2), [true, true, false]) = false := by decide

-- Concrete `SAT.toIndependentSet` on satisfiable and unsatisfiable formulas.
private def satFormula : CNF ℕ := [[(0, true), (1, false)], [(0, false), (1, true)]]
private def unsatFormula : CNF ℕ := [[(0, true)], [(0, false)]]

example : SAT.toIndependentSet satFormula =
    (([0, 1, 2, 3],
      [(0, 1), (0, 2), (1, 0), (1, 3), (2, 0), (2, 3), (3, 1), (3, 2)]), 2) := rfl

-- Choosing the first literal `(0, true)` in clause 0 and the second literal `(1, true)` in clause 1
-- yields a valid independent set of size 2 (and a 2-clique in the complement).
example : IndependentSet.verifier (SAT.toIndependentSet satFormula, [true, false, false, true]) =
    true := rfl
example : Clique.verifier
    (((SAT.toIndependentSet satFormula).1.compl, (SAT.toIndependentSet satFormula).2),
      [true, false, false, true]) = true := rfl

-- Conflicting occurrences `[[(0, true)], [(0, false)]]` produce an edge between the two vertices.
example : SAT.toIndependentSet unsatFormula = (([0, 2], [(0, 2), (2, 0)]), 2) := rfl
example : IndependentSet.verifier (SAT.toIndependentSet unsatFormula, [true, true]) = false := rfl

end ComplexityTests.KarpReductions
