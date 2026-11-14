/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.AnyEndpoints

/-! Clients of undirected Hamiltonian paths without given endpoints (`HamPathAny`) and of
Arora–Barak 2007, Exercise 2 §17: concrete members and non-members, the empty-graph convention,
the reduction from `HamPath` and `NP`-completeness. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

open Cslib.Complexity

/-- The path `0 - 1 - 2` is a Hamiltonian path, although its edges are listed as `(1, 0)` and
`(2, 1)`: the problem is undirected. -/
example : (⟨[0, 1, 2], [(1, 0), (2, 1)]⟩ : Graph) ∈ HamPathAny :=
  mem_HamPathAny_iff.2
    ⟨[0, 1, 2], by decide, by simp, by simp, by simp [Graph.toSimpleGraph_adj]⟩

/-- With designated endpoints, the same graph has a Hamiltonian path from `2` to `0`. -/
example : (⟨⟨[0, 1, 2], [(1, 0), (2, 1)]⟩, 2, 0⟩ : PathInstance) ∈ HamPath :=
  mem_HamPath_iff.2 ⟨[2, 1, 0], by decide, by simp; omega, rfl, rfl,
    by simp [Graph.toSimpleGraph_adj]⟩

/-- Empty-graph convention: a graph without declared vertices has no Hamiltonian path. -/
example : (⟨[], []⟩ : Graph) ∉ HamPathAny :=
  HamPathAny.notMem_of_vertices_eq_nil rfl

/-- A single vertex has a Hamiltonian path of length zero. -/
example : (⟨[7], []⟩ : Graph) ∈ HamPathAny :=
  HamPathAny.mem_of_vertices_eq_singleton rfl

/-- Two vertices without edges have no Hamiltonian path. A self-loop does not help: simple graphs
have no loops. -/
example : (⟨[0, 1], [(0, 0)]⟩ : Graph) ∉ HamPathAny := by
  rw [mem_HamPathAny_iff]
  rintro ⟨p, hnd, hcov, -, hch⟩
  match p, hnd, hcov, hch with
  | [], _, hcov, _ => simpa using (hcov 0).2 (by simp)
  | [a], _, hcov, _ =>
    have h0 := (hcov 0).2 (by simp)
    have h1 := (hcov 1).2 (by simp)
    simp only [List.mem_singleton] at h0 h1
    omega
  | _ :: _ :: _, _, _, hch =>
    simp only [List.isChain_cons_cons, Graph.toSimpleGraph_adj] at hch
    simp at hch
    omega

/-- The pendant-vertex reduction from designated endpoints. -/
example (x : PathInstance) : DirHamPath.toAny x ∈ HamPathAny ↔ x ∈ HamPath :=
  DirHamPath.toAny_mem_HamPathAny_iff x

example : PolyTimeReducible encPathInstance encGraph HamPath HamPathAny :=
  polyTimeReducible_HamPath_HamPathAny

example : HamPathAny ∈ NP encGraph := HamPathAny.mem_NP

example : NPComplete encGraph HamPathAny := HamPathAny_npComplete
