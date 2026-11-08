/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.WHierarchy.Clique.Graph

/-!
# Tests: the graph of a circuit of weft one

The short lists over a list, what a bracket knows about a position, consistency of brackets, and
cliques of a graph given by a Boolean adjacency, evaluated by `decide`. Then the correctness of
the graph construction on small instances: the graph of the fixed yes-instance of `WCS 1 1` has a
clique of the size and that of the fixed no-instance has none, and the graph of the conjunction of
three inputs has a clique of the size for weight `3` and none for weight `2`.
-/

namespace ComplexityTests.WHierarchyClique

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean WCS WCS.ToClique

/-! ### Short lists -/

example : [0, 1].listsUpTo 2 = [[], [0], [0, 0], [0, 1], [1], [1, 0], [1, 1]] := by decide

example : ([0, 1].listsUpTo 2).length = 7 ∧ (List.range 3).listsUpTo 0 = [[]] := by decide

/-! ### Brackets -/

-- The selected positions are `1 < 3` (`kk = 2`), and the bracket names the first one. It knows
-- that `1` is selected and that `0` is not (it is before the first selected position), and does
-- not know `2`.
example : know 2 [(0, 1)] 1 = some true ∧ know 2 [(0, 1)] 0 = some false ∧
    know 2 [(0, 1)] 2 = none := by decide

-- Naming both selected positions shows that `2`, between them, and `4`, after the last, are not
-- selected.
example : know 2 [(0, 1), (1, 3)] 2 = some false ∧ know 2 [(0, 1), (1, 3)] 4 = some false := by
  decide

-- With no selected position, no position is selected.
example : know 0 [] 5 = some false := by decide

-- Brackets agreeing on the order of indices and positions are consistent; brackets naming two
-- positions for one index, or out of order, are not.
example : consistent [(0, 1)] [(1, 3)] = true ∧ consistent [(0, 1)] [(0, 2)] = false ∧
    consistent [(0, 3)] [(1, 1)] = false := by decide

/-! ### Graphs from a Boolean adjacency -/

-- Three pairwise distinct vertices, adjacent when distinct: a triangle.
example : ((Graph.ofAdj [0, 1, 2] fun a b => a != b), 3) ∈ Clique := by
  rw [Graph.mem_Clique_ofAdj_iff_entries (fun v => by simp)]
  exact ⟨{0, 1, 2}, by decide, by decide, by decide⟩

-- Adjacent only when both are even: the largest clique has two vertices.
example : ((Graph.ofAdj [0, 1, 2] fun a b => a != b && a % 2 == 0 && b % 2 == 0), 3) ∉ Clique := by
  rw [Graph.mem_Clique_ofAdj_iff_entries (fun v => by simp)]
  rintro ⟨T, hT, hTv, hTadj⟩
  have hsub : T ⊆ {0, 1, 2} := fun v hv => by simpa using hTv v hv
  have h1 : (1 : ℕ) ∉ T := fun h1 => by
    obtain ⟨w, hw, hw1⟩ : ∃ w ∈ T, w ≠ 1 := by
      by_contra! h
      have : T ⊆ {1} := fun v hv => by simpa using h v hv
      have := Finset.card_le_card this
      simp at this
      omega
    have := hTadj 1 h1 w hw hw1.symm
    simp at this
  have : T ⊆ {0, 2} := fun v hv => by
    have := hsub hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    rcases this with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hv h1
    · exact Or.inr rfl
  have := Finset.card_le_card this
  simp at this
  omega

/-! ### Correctness on small instances -/

example : toClique (WCS.yesInstance 1) ∈ Clique :=
  (toClique_mem_Clique_iff _).2 (WCS.yesInstance_mem 1)

example : toClique (WCS.noInstance 1) ∉ Clique :=
  fun h => WCS.noInstance_not_mem 1 ((toClique_mem_Clique_iff _).1 h)

/-- The conjunction of three inputs, as a circuit of weft at most `1` and depth at most `1`. -/
def and3 : WeftCircuit 1 1 :=
  ⟨⟨3, ⟨Program.empty.gate ⟨.and 3, fun i => .input i⟩, fun _ => .gate 0⟩⟩, by decide⟩

-- The graph of the conjunction of three inputs has a clique of the size for weight `3`, and none
-- for weight `2`.
example : toClique (and3, 3) ∈ Clique :=
  (toClique_mem_Clique_iff _).2 ⟨fun _ => true, by decide, by decide⟩

example : toClique (and3, 2) ∉ Clique := by
  rw [toClique_mem_Clique_iff]
  rintro ⟨x, hk, hx⟩
  revert hk hx
  revert x
  unfold BitString.weight
  decide

-- The clique size: one certificate and one bracket for each list of at most `2 ^ (d + 1)`
-- indices.
example : size 0 3 1 = 4 ∧ size 0 3 5 = 22 := by decide

end ComplexityTests.WHierarchyClique
