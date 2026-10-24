/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Tactic.PolyTime

/-!
# Vertex-splitting reduction tests

Concrete, boundary, `fun_prop`, and axiom checks for `Graph.split` and the reductions from
directed to undirected Hamiltonian paths and cycles.
-/

namespace ComplexityTests.NPCompleteGraphs.Undirected

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Polynomial-time reductions -/

example : PolyTimeReducible (encPair encGraph (encPair encNat encNat))
    (encPair encGraph (encPair encNat encNat)) DirHamPath HamPath :=
  polyTimeReducible_DirHamPath_HamPath

example : PolyTimeReducible encGraph encGraph DirHamCycle HamCycle :=
  polyTimeReducible_DirHamCycle_HamCycle

example : ComputableInPolyTime Graph.split encGraph encGraph := by fun_prop

example : ComputableInPolyTime DirHamPath.toHamPath
    (encPair encGraph (encPair encNat encNat)) (encPair encGraph (encPair encNat encNat)) := by
  fun_prop

-- Certificates compose: splitting twice is polynomial-time.
example : ComputableInPolyTime (fun G : Graph => G.split.split) encGraph encGraph := by
  fun_prop

/-! ### The split graph -/

-- Gadget vertices are `Nat.pair` of the first-occurrence index and the position in the gadget.
example : Graph.split ([0, 1], [(0, 1)]) =
    ([0, 1, 4, 2, 3, 5], [(0, 1), (1, 4), (2, 3), (3, 5), (4, 2)]) := by decide

-- A self-loop `(v, v)` becomes the edge `out(v) - in(v)`: the split graph is a triangle.
example : Graph.split ([0], [(0, 0)]) = ([0, 1, 4], [(0, 1), (1, 4), (4, 0)]) := by decide

-- An arc to an undeclared vertex becomes an edge to the undeclared label `Nat.pair 1 0 = 2`.
example : Graph.split ([0], [(0, 7)]) = ([0, 1, 4], [(0, 1), (1, 4), (4, 2)]) := by decide
example : 2 ∉ (Graph.split ([0], [(0, 7)])).1 := by decide

-- Repeated vertex entries share the gadget of their first occurrence.
example : Graph.split ([5, 5], []) =
    ([0, 1, 4, 0, 1, 4], [(0, 1), (1, 4), (0, 1), (1, 4)]) := by decide

-- The labels of an undeclared vertex are never declared vertices of the split graph.
example : Graph.splitVertex ([0, 1], []) 9 0 ∉ (Graph.split ([0, 1], [])).1 := by decide

/-! ### Hamiltonian paths -/

private def path3 : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

private theorem path3_mem_DirHamPath : (path3, 0, 2) ∈ DirHamPath :=
  ⟨[0, 1, 2], by decide, fun _ => Iff.rfl, rfl, rfl, by decide⟩

example : (path3.split, path3.splitVertex 0 0, path3.splitVertex 2 2) ∈ HamPath :=
  (Graph.split_mem_HamPath_iff _ _ _).2 path3_mem_DirHamPath

example : DirHamPath.toHamPath (path3, 0, 2) ∈ HamPath :=
  (DirHamPath.toHamPath_mem_iff _).2 path3_mem_DirHamPath

-- The path cannot be traversed backwards: `2` has no outgoing arc.
example : (path3.split, path3.splitVertex 2 0, path3.splitVertex 0 2) ∉ HamPath := by
  rw [Graph.split_mem_HamPath_iff]
  rintro ⟨p, -, hcov, hs, -, hch⟩
  obtain ⟨l, rfl⟩ := List.head?_eq_some_iff.1 hs
  rcases l with _ | ⟨y, l⟩
  · simpa [path3] using (hcov 0).2 (by decide)
  · have := (List.isChain_cons_cons.1 hch).1
    simp [path3] at this

-- An undeclared start vertex makes both instances negative.
example : (path3.split, path3.splitVertex 7 0, path3.splitVertex 2 2) ∉ HamPath := by
  rw [Graph.split_mem_HamPath_iff]
  rintro ⟨p, -, hcov, hs, -⟩
  simpa [path3] using (hcov 7).1 (List.mem_of_head? hs)

-- `s = t` in a one-vertex graph: the path `in(0) - mid(0) - out(0)`.
example : (Graph.split ([0], []), Graph.splitVertex ([0], []) 0 0,
    Graph.splitVertex ([0], []) 0 2) ∈ HamPath :=
  (Graph.split_mem_HamPath_iff _ _ _).2 ⟨[0], by decide, fun _ => Iff.rfl, rfl, rfl, by decide⟩

/-! ### Hamiltonian cycles -/

/-- A declared vertex without outgoing arcs rules out a directed Hamiltonian cycle. -/
private theorem notMem_DirHamCycle_of_sink {G : Graph} {v : ℕ} (hv : v ∈ G.1)
    (hsink : ∀ w, (v, w) ∉ G.2) : G ∉ DirHamCycle := by
  rintro ⟨p, -, hcov, -, hch⟩
  obtain ⟨A, B, rfl⟩ := List.append_of_mem ((hcov v).2 hv)
  rw [Cycle.coe_eq_coe.2 (List.isRotated_append (l := A) (l' := v :: B)), List.cons_append,
    Cycle.chain_coe_cons, List.isChain_cons] at hch
  rcases hBA : B ++ A with _ | ⟨y, l⟩
  · exact hsink v (hch.1 v (by simp [hBA]))
  · exact hsink y (hch.1 y (by simp [hBA]))

private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

example : triangle ∈ DirHamCycle :=
  ⟨[0, 1, 2], by decide, fun _ => Iff.rfl, by decide, by
    rw [Cycle.chain_coe_cons]
    decide⟩

example : triangle.split ∈ HamCycle :=
  (Graph.split_mem_HamCycle_iff _).2 ⟨[0, 1, 2], by decide, fun _ => Iff.rfl, by decide, by
    rw [Cycle.chain_coe_cons]
    decide⟩

-- The directed path `0 → 1 → 2` has no Hamiltonian cycle, so neither has its split graph.
example : path3.split ∉ HamCycle := by
  rw [Graph.split_mem_HamCycle_iff]
  exact notMem_DirHamCycle_of_sink (v := 2) (by decide) (by simp [path3])

-- A directed 2-cycle: its split graph is a 6-cycle.
example : Graph.split ([0, 1], [(0, 1), (1, 0)]) ∈ HamCycle :=
  (Graph.split_mem_HamCycle_iff _).2 ⟨[0, 1], by decide, fun _ => Iff.rfl, by decide, by
    rw [Cycle.chain_coe_cons]
    decide⟩

-- A single arc between two vertices gives a path, not a cycle.
example : Graph.split ([0, 1], [(0, 1)]) ∉ HamCycle := by
  rw [Graph.split_mem_HamCycle_iff]
  exact notMem_DirHamCycle_of_sink (v := 1) (by decide) (by simp)

-- A single vertex is a directed Hamiltonian cycle exactly with a self-loop; the split graph is
-- then a triangle, and otherwise a path on three vertices.
example : Graph.split ([0], [(0, 0)]) ∈ HamCycle :=
  (Graph.split_mem_HamCycle_iff _).2
    ⟨[0], by decide, fun _ => Iff.rfl, by decide, (Cycle.chain_singleton _ _).2 (by decide)⟩

example : Graph.split ([0], []) ∉ HamCycle := by
  rw [Graph.split_mem_HamCycle_iff]
  exact notMem_DirHamCycle_of_sink (v := 0) (by decide) (by simp)

-- The empty graph has no Hamiltonian cycle.
example : Graph.split ([], []) ∉ HamCycle := by
  rw [Graph.split_mem_HamCycle_iff]
  rintro ⟨p, -, hcov, hne, -⟩
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil p hne
  simpa using (hcov v).1 hv

/-! ### Axiom checks for headline theorems -/

/--
info: 'Cslib.Complexity.Graph.split_mem_HamPath_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Graph.split_mem_HamPath_iff

/--
info: 'Cslib.Complexity.Graph.split_mem_HamCycle_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.Graph.split_mem_HamCycle_iff

/--
info: 'Cslib.Complexity.polyTimeReducible_DirHamPath_HamPath' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.polyTimeReducible_DirHamPath_HamPath

/--
info: 'Cslib.Complexity.polyTimeReducible_DirHamCycle_HamCycle' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.polyTimeReducible_DirHamCycle_HamCycle

end ComplexityTests.NPCompleteGraphs.Undirected
