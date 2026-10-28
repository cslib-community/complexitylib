/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Reachability.Reingold
import Complexity.Computability.Complexity.Classes.LogSpace.USTCON
import Complexity.Foundations.Combinatorics.Expander.LowerBound
import Complexity.Foundations.Data.List.Append

/-!
# Reingold's transformation tests

The concrete theorem `Cslib.Reachability.Reingold.reachable_iff_exists_walk` has no hypotheses
beyond decidability of adjacency; its two directions are exercised on the complete and the empty
graph on two vertices. The bundled hypotheses of the generic statements are discharged: the regular
rotation map of every simple graph has at least half self-loops at every vertex, the connected
component of a vertex is connected, the base graph has `λ ≤ 1 / 5`, and the depth and length
conditions hold for the concrete depth and walk length (inside the proof of the concrete theorem).
The complete graph with self-loops, of spectral expansion `0`, shows the hypothesis of
`Cslib.RotationMap.exists_neighbor_pow_eq` is satisfiable.

The language `Cslib.Complexity.USTCON` is neither empty nor everything: the edge on two vertices
connects its ends, and the empty graph on two vertices does not; `Cslib.Complexity.USTCON_mem_L`
places it in `L`, `Cslib.Complexity.USTCON_logSpaceComplete_SL` and
`Cslib.Complexity.USTCON_logSpaceComplete_L` establish its completeness for `SL` and `L`, and
`Cslib.Complexity.SL_eq_L` identifies `SL` with `L`. The encoding of the edge is pinned bit by bit:
the header `11 0 0 1 0`, then the matrix `0110`.
-/

namespace ComplexityTests.Reingold

open Cslib Cslib.RotationMap Cslib.Reachability.Reingold

-- On the complete graph on two vertices, the vertex `1` is reached from `0` by a short walk.
example : ∃ k : Fin (walkLength (Nat.clog 2 2)) → Label,
    (((graph (⊤ : SimpleGraph (Fin 2)) (Nat.clog 2 2)).pow (walkLength (Nat.clog 2 2))).neighbor
      (start 0 (Nat.clog 2 2)) k).root.1 = 1 :=
  (reachable_iff_exists_walk ⊤ 0 1).1 (SimpleGraph.Adj.reachable (by decide))

-- On the empty graph on two vertices, no walk from `0` ends over `1`.
example (k : Fin (walkLength 1) → Label) :
    (((graph (⊥ : SimpleGraph (Fin 2)) 1).pow (walkLength 1)).neighbor (start 0 1) k).root.1 ≠
      1 := by
  intro h
  have := (reachable_iff_exists_walk_of_le_two_pow ⊥ (by norm_num) 0 1).2 ⟨k, h⟩
  rw [SimpleGraph.reachable_bot] at this
  exact absurd this (by decide)

-- The hypotheses of the generic statements are satisfiable: the base graph has `λ ≤ 1 / 5`, so
-- one step of Reingold's transformation on the complete rotation map has spectral gap at least
-- `1 / 5`.
example :
    (1 / 5 : ℝ) ≤ 1 - (reingoldStep base baseEquiv (complete Label)).spectralExpansion := by
  have h := min_le_one_sub_spectralExpansion_reingoldStep base baseEquiv spectralExpansion_base_le
    (complete Label) (γ := 1) zero_le_one (by rw [spectralExpansion_complete, sub_zero])
  exact (by norm_num : (1 / 5 : ℝ) ≤ min (6 / 5 * 1) (1 / 5)).trans h

-- The regular rotation map of any simple graph has at least half self-loops at every vertex.
example : Fintype.card Label ≤ 2 * (input (⊤ : SimpleGraph (Fin 2))).edgeCount (0, 0) (0, 0) :=
  card_le_two_mul_edgeCount_input ⊤ (0, 0)

-- The connected component of a vertex satisfies the connectivity hypothesis of the spectral gap.
example : ((input (⊤ : SimpleGraph (Fin 2))).componentGraph (0, 0)).toSimpleGraph.Preconnected :=
  (input (⊤ : SimpleGraph (Fin 2))).preconnected_componentGraph (0, 0)

-- The walk hypothesis is satisfiable: in the complete graph with self-loops one step reaches
-- every vertex.
example (u v : Fin 3) : ∃ k : Fin 1 → Fin 3, ((complete (Fin 3)).pow 1).neighbor u k = v :=
  (complete (Fin 3)).exists_neighbor_pow_eq (by rw [spectralExpansion_complete]; norm_num) u v

/-- The edge on two vertices, from `0` to `1`. -/
def edgeInstance : Complexity.USTCONInstance where
  n := 2
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp
  s := 0
  t := 1

/-- The empty graph on two vertices, from `0` to `1`. -/
def emptyInstance : Complexity.USTCONInstance where
  n := 2
  adj _ _ := false
  symm _ _ := rfl
  loopless _ := rfl
  s := 0
  t := 1

-- The encoding of the edge: `1^2 0`, `1^0 0`, `1^1 0`, then the matrix row by row.
example :
    edgeInstance.encode = [true, true, false, false, true, false, false, true, true, false] := by
  decide

example : edgeInstance ∈ Complexity.USTCON :=
  SimpleGraph.Adj.reachable (by decide)

example : emptyInstance ∉ Complexity.USTCON := by
  intro h
  obtain ⟨p⟩ := h
  cases p with
  | cons hadj _ => exact absurd hadj (by simp [emptyInstance, Complexity.USTCONInstance.graph])

example : Complexity.USTCON ∈ Complexity.P Complexity.encUSTCON :=
  Complexity.L_subset_P Complexity.USTCON_mem_L

example : Complexity.USTCONᶜ ∈ Complexity.SL Complexity.encUSTCON :=
  Complexity.compl_mem_SL Complexity.USTCON_mem_SL

example : Complexity.USTCONᶜ ∈ Complexity.L Complexity.encUSTCON :=
  Complexity.SL_eq_L ▸ Complexity.compl_mem_SL Complexity.USTCON_mem_SL

example :
    Complexity.LogSpaceReducible Complexity.encUSTCON Complexity.encUSTCON
      Complexity.USTCONᶜ Complexity.USTCON :=
  Complexity.USTCON_logSpaceComplete_SL.2 Complexity.encUSTCON Complexity.USTCONᶜ
    (Complexity.compl_mem_SL Complexity.USTCON_mem_SL)

example : Complexity.PolyTimeComplete Complexity.L Complexity.encUSTCON Complexity.USTCON :=
  Complexity.USTCON_logSpaceComplete_L.polyTimeComplete

example {m : ℕ} {l : List Bool}
    (h : List.replicate m true ++ false :: l = [true, true, false, true]) :
    m = 2 ∧ l = [true] :=
  List.replicate_true_append_false_inj (m' := 2) (l' := [true]) h

end ComplexityTests.Reingold
