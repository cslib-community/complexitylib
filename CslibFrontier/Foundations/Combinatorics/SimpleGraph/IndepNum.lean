/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Clique.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Basic facts about the independence number

General facts about Mathlib's `SimpleGraph.indepNum` that are not yet in Mathlib: monotonicity
under embeddings, invariance under isomorphisms, and its range on finite vertex types. The
cardinality bounds come from the corresponding `cliqueNum` facts via `cliqueNum_compl`.

## Main results

* `SimpleGraph.Embedding.indepNum_le`: `α(G) ≤ α(H)` when `G` embeds into `H`.
* `SimpleGraph.Iso.indepNum_eq`: `α` is invariant under isomorphism.
* `SimpleGraph.indepNum_le_natCard`, `SimpleGraph.one_le_indepNum`,
  `SimpleGraph.indepNum_eq_zero_of_isEmpty`: `1 ≤ α(G) ≤ |V|` for nonempty finite `V`, and
  `α(G) = 0` for empty `V`.
-/

public section

open Finset

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The independence number is monotone under graph embeddings. -/
theorem Embedding.indepNum_le [Finite W] (f : G ↪g H) : G.indepNum ≤ H.indepNum := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hind : H.IsIndepSet (s.map f.toEmbedding) := by
    intro x hx y hy hxy
    simp only [coe_map, Set.mem_image, mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [RelEmbedding.coe_toEmbedding, f.map_adj_iff]
    exact hs.isIndepSet ha hb fun h => hxy (by rw [h])
  have h := hind.card_le_indepNum
  rwa [card_map, hs.card_eq] at h

/-- The independence number is invariant under graph isomorphisms. -/
theorem Iso.indepNum_eq [Finite V] [Finite W] (e : G ≃g H) : G.indepNum = H.indepNum :=
  le_antisymm e.toEmbedding.indepNum_le e.symm.toEmbedding.indepNum_le

theorem indepNum_le_natCard [Finite V] : G.indepNum ≤ Nat.card V := by
  rw [← cliqueNum_compl]
  exact Gᶜ.cliqueNum_le_natCard

theorem one_le_indepNum [Finite V] [Nonempty V] : 1 ≤ G.indepNum := by
  rw [← cliqueNum_compl]
  exact Nat.one_le_iff_ne_zero.2 Gᶜ.cliqueNum_ne_zero_of_finite

theorem indepNum_eq_zero_of_isEmpty [IsEmpty V] : G.indepNum = 0 := by
  rw [← cliqueNum_compl]
  exact Gᶜ.cliqueNum_of_isEmpty

end SimpleGraph
