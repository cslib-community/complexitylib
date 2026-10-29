/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.GraphProblems

/-!
# Tests: exponential lower bounds for graph problems

The reduction with variable edges on concrete formulas: its target and size against the linear
bound, its edges against those of Karp's reduction on a formula with many complementary
occurrences, and its correctness on satisfiable and unsatisfiable formulas, including a formula
with no clauses and one with an empty clause; the sparse diamond reduction: its size against
Sipser's construction on a formula with many occurrences of one variable, and its correctness for
directed paths, directed cycles and undirected cycles on satisfiable and unsatisfiable formulas,
including the formula with no clauses and the empty clause; the size of the 3-coloring reduction;
the non-vacuity of the subexponential time predicate; the lower bound for the number of distinct
vertices of a clique instance, by changing the measure; and the axioms of the headline theorems.
-/

namespace ComplexityTests.FineGrained.GraphProblems

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ ¬x₀) ∧ x₂`. -/
private def φ₁ : CNF ℕ := [[(0, true), (1, false)], [(1, true), (0, false)], [(2, true)]]

/-- `x₀ ∧ ¬x₀`. -/
private def φ₂ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- `x₀ ∧ ¬x₀ ∧ x₀ ∧ ¬x₀ ∧ ⋯`, with `8` clauses. -/
private def ψ : CNF ℕ := (List.range 8).map fun i => [(0, decide (i % 2 = 0))]

/-! ### The reduction with variable edges -/

/-- Three variables and three clauses: the target is `3 + 3`. -/
example : (SAT.toSparseIndependentSet φ₁).2 = 6 := by decide

/-- `2 n + L = 6 + 5` vertices and `n + Σ |c| ^ 2 + L = 3 + 9 + 5` edges. -/
example : (SAT.toSparseIndependentSet φ₁).1.1.length = 11 ∧
    (SAT.toSparseIndependentSet φ₁).1.2.length = 17 := by decide

example : (SAT.toSparseIndependentSet φ₁).1.1.length + (SAT.toSparseIndependentSet φ₁).1.2.length ≤
    (2 * 2 + 5 * 2) * φ₁.length :=
  SAT.length_toSparseIndependentSet_le (by decide)

/-- Karp's reduction joins every positive occurrence of `x₀` in `ψ` to every negative one, in both
directions; the reduction with variable edges has `1 + 8 + 8` edges. -/
example : (SAT.toIndependentSet ψ).1.2.length = 32 ∧
    (SAT.toSparseIndependentSet ψ).1.2.length = 17 := by decide

example : SAT.toSparseIndependentSet φ₁ ∈ IndependentSet :=
  (SAT.toSparseIndependentSet_mem_iff φ₁).2 ⟨fun _ => true, by decide⟩

example : SAT.toSparseIndependentSet φ₂ ∉ IndependentSet := fun h => by
  obtain ⟨σ, hσ⟩ := (SAT.toSparseIndependentSet_mem_iff φ₂).1 h
  cases h : σ 0 <;> simp [φ₂, h] at hσ

/-- The formula with no clauses asks for the empty independent set; the empty clause has no
vertex to choose. -/
example : SAT.toSparseIndependentSet [] ∈ IndependentSet :=
  (SAT.toSparseIndependentSet_mem_iff []).2 ⟨fun _ => true, rfl⟩

example : SAT.toSparseIndependentSet [[]] ∉ IndependentSet := fun h => by
  obtain ⟨σ, hσ⟩ := (SAT.toSparseIndependentSet_mem_iff [[]]).1 h
  simp at hσ

/-! ### The sparse diamond reduction -/

/-- One diamond for the single variable of `ψ`, with a slot for each of its `8` occurrences:
`2` tops, `3 * 8 + 3` row nodes and `8` clause nodes. Sipser's construction has a diamond for each
occurrence, each with a pair of nodes for each clause: `9` tops, `8 * 27` row nodes and `8` clause
nodes. -/
example : (SAT.sparseDiamondGraph ψ).1.length = 37 ∧ (SAT.toDirHamPath ψ).1.1.length = 233 := by
  decide +kernel

example : (SAT.sparseDiamondGraph φ₁).1.length + (SAT.sparseDiamondGraph φ₁).2.length ≤
    (23 * 2 + 1) * φ₁.length + 1 :=
  SAT.length_sparseDiamondGraph_le (by decide)

example : SAT.toSparseDirHamPath φ₁ ∈ DirHamPath :=
  (SAT.toSparseDirHamPath_mem_iff φ₁).2 ⟨fun _ => true, by decide⟩

example : SAT.toSparseDirHamPath φ₂ ∉ DirHamPath := fun h => by
  obtain ⟨σ, hσ⟩ := (SAT.toSparseDirHamPath_mem_iff φ₂).1 h
  cases h : σ 0 <;> simp [φ₂, h] at hσ

example : SAT.toSparseDirHamCycle φ₁ ∈ DirHamCycle :=
  (SAT.toSparseDirHamCycle_mem_iff φ₁).2 ⟨fun _ => true, by decide⟩

example : SAT.toSparseHamCycle φ₁ ∈ HamCycle :=
  (SAT.toSparseHamCycle_mem_iff φ₁).2 ⟨fun _ => true, by decide⟩

example : SAT.toSparseHamCycle φ₂ ∉ HamCycle := fun h => by
  obtain ⟨σ, hσ⟩ := (SAT.toSparseHamCycle_mem_iff φ₂).1 h
  cases h : σ 0 <;> simp [φ₂, h] at hσ

/-- The formula with no clauses gives the graph of a single top, which a path visits without arcs;
the empty clause gives a clause node that no detour reaches. -/
example : SAT.toSparseDirHamPath [] = (([Diamond.topNode 0], []), Diamond.topNode 0,
    Diamond.topNode 0) := by decide

example : SAT.toSparseDirHamCycle [[]] ∉ DirHamCycle := fun h => by
  obtain ⟨σ, hσ⟩ := (SAT.toSparseDirHamCycle_mem_iff [[]]).1 h
  simp at hσ

/-! ### The 3-coloring reduction -/

example : (SAT.toThreeColoring φ₁).1.length + (SAT.toThreeColoring φ₁).2.length ≤
    (24 * 2 + 12) * φ₁.length + 9 :=
  SAT.length_toThreeColoring_le (by decide)

/-! ### Non-vacuity -/

/-- The subexponential time predicate holds for a trivial problem. -/
example : DecidableInSubexpTime (∅ : Set Graph) encGraph fun G => G.1.length + G.2.length :=
  fun δ hδ => DecidableInExpTime.of_computableInO (ComputableInO.const false)
    (by simp) 1 1 fun G => by
    have h₁ : (1 : ℝ) ≤ 2 ^ (δ * ((G.1.length + G.2.length : ℕ) : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have h₀ : (0 : ℝ) ≤ (encGraph G).length := Nat.cast_nonneg _
    simp only [Nat.cast_one, pow_one, one_mul]
    nlinarith

/-- Under `ETH`, clique is not decidable in time `2 ^ o(n)` for `n` distinct vertices either, and
3SAT is not decidable in subexponential time in the number of clauses. -/
example (h : ETH) :
    ¬DecidableInSubexpTime Clique (encPair encGraph encNat) (fun x => x.1.1.toFinset.card) ∧
    ¬DecidableInSubexpTime ThreeSAT encCNF List.length :=
  ⟨fun h' => h.not_decidableInSubexpTime_Clique (h'.mono_measure (c := 1) fun x => by
    have := x.1.1.toFinset_card_le
    omega),
   h.not_decidableInSubexpTime_of_reduction (f := id) ComputableInPolyTime.id'
    (fun φ hφ => ⟨fun h => h.2, fun h' => ⟨hφ, h'⟩⟩) (k := 1) fun φ _ => by simp⟩

/-! ### Axioms -/

/-- info: 'Cslib.Complexity.SAT.toDirHamPath_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SAT.toDirHamPath_eq

end ComplexityTests.FineGrained.GraphProblems
