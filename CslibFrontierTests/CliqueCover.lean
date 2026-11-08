/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.CliqueCover

/-!
# Clique cover: tests

Covers of small graphs by cliques on yes and no instances, Karp's reduction from
`ChromaticNumber`, the generic correspondence with colorings of the complement, and the headline
results.
-/

namespace CslibFrontierTests.CliqueCover

open Cslib.Complexity Turing.MultiTapeTM

private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

private def path3 : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

/-! ### Headline results -/

example : CliqueCover ∈ NP (encPair encGraph encNat) ∧
    NPHard (encPair encGraph encNat) CliqueCover ∧
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) ChromaticNumber
      CliqueCover ∧
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) CliqueCover
      ChromaticNumber :=
  ⟨CliqueCover_npComplete.1, CliqueCover_npComplete.2,
    polyTimeReducible_ChromaticNumber_CliqueCover, polyTimeReducible_CliqueCover_ChromaticNumber⟩

-- Clique cover with three cliques is already `NP`-hard.
example : PolyTimeReducible encGraph (encPair encGraph encNat) ThreeColoring CliqueCover :=
  (polyTimeReducible_KColoring_ChromaticNumber 3).trans
    polyTimeReducible_ChromaticNumber_CliqueCover

/-! ### Covers -/

-- The path `0 - 1 - 2` is covered by the cliques `{0, 1}` and `{2}`, but by no single clique.
example : (path3, 2) ∈ CliqueCover := by
  rw [Graph.mem_CliqueCover_iff_compl, mem_ChromaticNumber_iff, mem_KColoring_iff]
  refine ⟨fun v => if v = 2 then 1 else 0, by decide, fun u hu v hv huv => ?_⟩
  rw [← Graph.adjBool_eq_true_iff] at huv
  have hu' : u ∈ path3.1 := hu
  have hv' : v ∈ path3.1 := hv
  simp only [path3, List.mem_cons, List.not_mem_nil, or_false] at hu' hv'
  rcases hu' with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;> revert huv <;> decide

example : (path3, 1) ∉ CliqueCover := by
  rw [Graph.mem_CliqueCover_iff_compl, mem_ChromaticNumber_iff, mem_KColoring_iff]
  rintro ⟨c, hc, hadj⟩
  have h₀ := hc 0 (by decide)
  have h₂ := hc 2 (by decide)
  have h₀₂ := hadj 0 (by decide) 2 (by decide) ((Graph.adjBool_eq_true_iff _ _ _).1 (by decide))
  omega

-- Karp's reduction: the triangle is 3-colorable, so its complement is covered by 3 cliques.
example : (triangle.compl, 3) ∈ CliqueCover :=
  Graph.compl_mem_CliqueCover_iff.2 (by
    rw [mem_ChromaticNumber_iff, mem_KColoring_iff]
    exact ⟨id, by decide, fun u _ v _ huv => huv.ne⟩)

-- A graph without declared vertices is covered by no clique at all.
example : ((([] : List ℕ), [(0, 1)]), 0) ∈ CliqueCover :=
  ⟨∅, by simp, by simp, fun v => absurd v.2 (by simp)⟩

/-! ### Clique covers and colorings of the complement -/

-- The complete graph on `Fin 3` is one clique, and its complement is the empty graph.
example : (⊤ : SimpleGraph (Fin 3))ᶜ.Colorable 1 :=
  SimpleGraph.exists_cliqueCover_iff_colorable_compl.1
    ⟨{Finset.univ}, by simp, by simp [SimpleGraph.isClique_iff], by simp⟩

end CslibFrontierTests.CliqueCover
