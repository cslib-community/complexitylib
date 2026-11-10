/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Empty cuts of disconnected graphs

A graph on a nonempty finite vertex set that is not connected has a vertex set `S` with
`1 ≤ |S|`, `2 |S| ≤ |V|` and no edge between `S` and its complement
(`SimpleGraph.exists_forall_not_adj_of_not_connected`): take the reachability class of a vertex
or its complement, whichever is smaller. This is the combinatorial step of the union bound over
cuts for the connectivity of random graphs.
-/

public section

open Finset
open scoped Finset

namespace SimpleGraph

variable {V : Type*}

/-- A graph on a nonempty finite vertex set that is not connected has a nonempty vertex set `S`
with at most half of the vertices and no edge between `S` and its complement. -/
theorem exists_forall_not_adj_of_not_connected [Fintype V] [Nonempty V]
    {G : SimpleGraph V} (hG : ¬G.Connected) :
    ∃ S : Finset V, 1 ≤ #S ∧ 2 * #S ≤ Fintype.card V ∧ ∀ u ∈ S, ∀ v ∉ S, ¬G.Adj u v := by
  classical
  rw [connected_iff] at hG
  simp only [‹Nonempty V›, and_true, Preconnected, not_forall] at hG
  obtain ⟨u, v, huv⟩ := hG
  set C : Finset V := {w | G.Reachable u w} with hC
  have hclosed : ∀ a b, G.Adj a b → (a ∈ C ↔ b ∈ C) := fun a b hab => by
    simp only [hC, mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.trans hab.reachable, fun h => h.trans hab.symm.reachable⟩
  have huC : u ∈ C := by simp [hC]
  have hvC : v ∉ C := by simpa [hC] using huv
  have hsum : #C + #Cᶜ = Fintype.card V := card_add_card_compl C
  by_cases h : 2 * #C ≤ Fintype.card V
  · refine ⟨C, card_pos.2 ⟨u, huC⟩, h, fun a ha b hb hab => hb ((hclosed a b hab).1 ha)⟩
  · refine ⟨Cᶜ, card_pos.2 ⟨v, mem_compl.2 hvC⟩, by omega, fun a ha b hb hab => ?_⟩
    rw [mem_compl] at ha hb
    rw [not_not] at hb
    exact ha ((hclosed a b hab).2 hb)

end SimpleGraph
