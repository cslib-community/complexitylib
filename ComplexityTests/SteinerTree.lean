/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SteinerTree.Graph
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Tactic.FinCases

/-!
# Worked examples of the MST heuristic for Steiner tree

These kernel-checked examples (using no `native_decide`) exercise
`Complexity.Algorithms.Lean.SteinerTree.Metric` and `Complexity.Algorithms.Lean.SteinerTree.Graph`.

1. **Steiner points help, and the sharp bound is tight.** Take a centre `0` at distance `1` from
   the terminals `1, 2, 3`, which are `2` apart. Kruskal's tree on the terminals costs `4`. The star
   through the Steiner point `0` costs `3`, and the optimum is exactly `3`. So
   `|R| · MST = 3 · 4 = 12 = 2 (|R| - 1) · OPT`, so `length_mul_edgeCost_steinerMST_le_steinerOpt`
   holds with equality.
2. **The triangle inequality is needed.** With the terminals `10` apart and still at distance `1`
   from the centre, the tree on the terminals costs `20 > 2 · 3`.
3. **Distinct terminals are needed.** With constant cost `5` and the terminal list `[1, 1]`, the
   heuristic pays `5` to join the two copies, while the optimum is `0`.
4. Edge cases: no terminals and one terminal give the empty tree.
5. **Graphs.** On the star graph `K_{1,3}` with unit weights, every Steiner subgraph for the leaves
   contains all three edges, so the optimum is `3`. For every shortest-walk oracle the heuristic
   returns exactly the star. On a triangle whose edge `0 - 1` weighs `10` and whose other edges
   weigh `1`, the heuristic never uses the heavy edge to join `0` and `1`, whatever shortest walks
   it is given.

`List.mergeSort` does not reduce in the kernel, so the sorted edge lists are pinned with
`simp [sortEdges_cons_cons]` first, as in `ComplexityTests/TSPChristofides.lean`.
-/

public section

namespace ComplexityTests.SteinerTree

open Cslib.Algorithms.Lean.SteinerTree Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.Lean.TSP
open SimpleGraph

/-! ### 1. A star metric: Steiner points help, and the sharp bound is tight -/

/-- A centre `0` at distance `1` from the leaves `1, 2, 3`, which are `2` apart. -/
def δStar (i j : Fin 4) : ℕ := if i = j then 0 else if i = 0 ∨ j = 0 then 1 else 2

theorem δStar_symm : ∀ x y, δStar x y = δStar y x := by decide

theorem δStar_tri : ∀ x y z, δStar x z ≤ δStar x y + δStar y z := by decide

theorem sortEdges_star : sortEdges (completeEdges (terminalCost δStar [1, 2, 3])) =
    [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 2, 0⟩, ⟨0, 1, 2⟩, ⟨0, 2, 2⟩, ⟨1, 0, 2⟩, ⟨1, 2, 2⟩, ⟨2, 0, 2⟩,
      ⟨2, 1, 2⟩] := by
  rw [show completeEdges (terminalCost δStar [1, 2, 3]) =
      [⟨0, 0, 0⟩, ⟨0, 1, 2⟩, ⟨0, 2, 2⟩, ⟨1, 0, 2⟩, ⟨1, 1, 0⟩, ⟨1, 2, 2⟩, ⟨2, 0, 2⟩, ⟨2, 1, 2⟩,
        ⟨2, 2, 0⟩] by decide +kernel]
  simp [sortEdges_cons_cons]

/-- Kruskal's tree on the terminals is the path `2 - 1 - 3`. -/
theorem steinerMST_star : steinerMST δStar [1, 2, 3] = [(1, 2), (1, 3)] := by
  rw [steinerMST, kruskalEdges, sortEdges_star]
  decide +kernel

theorem edgeCost_steinerMST_star : edgeCost δStar (steinerMST δStar [1, 2, 3]) = 4 := by
  rw [steinerMST_star]
  decide

/-- The star through the Steiner point `0` connects the terminals. -/
theorem connects_star : Connects [(0, 1), (0, 2), (0, 3)] ([1, 2, 3] : List (Fin 4)) := by
  have h : ∀ a ∈ ([1, 2, 3] : List (Fin 4)), Relation.EqvGen
      (fun x y => (x, y) ∈ ([(0, 1), (0, 2), (0, 3)] : List (Fin 4 × Fin 4))) a 0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> exact .symm _ _ (.rel _ _ (by decide))
  intro a ha b hb
  exact .trans _ _ _ (h a ha) (.symm _ _ (h b hb))

/-- The optimum is `3`: the star gives `≤ 3`, and the sharp bound gives `3 · 4 ≤ 4 · OPT`. -/
theorem steinerOpt_star : steinerOpt δStar [1, 2, 3] = 3 := by
  refine le_antisymm ((steinerOpt_le connects_star).trans_eq (by decide)) ?_
  have := length_mul_edgeCost_steinerMST_le_steinerOpt δStar_symm δStar_tri
    (R := [1, 2, 3]) (by decide)
  rw [edgeCost_steinerMST_star] at this
  change 3 * 4 ≤ 2 * (3 - 1) * _ at this
  omega

/-- The sharp bound `|R| · MST ≤ 2 (|R| - 1) · OPT` holds with equality. -/
example : [1, 2, 3].length * edgeCost δStar (steinerMST δStar [1, 2, 3]) =
    2 * ([1, 2, 3].length - 1) * steinerOpt δStar [1, 2, 3] := by
  rw [edgeCost_steinerMST_star, steinerOpt_star]
  rfl

/-! ### 2. Without the triangle inequality the bound fails -/

/-- The leaves are `10` apart but still at distance `1` from the centre. -/
def δFar (i j : Fin 4) : ℕ := if i = j then 0 else if i = 0 ∨ j = 0 then 1 else 10

example : ¬ ∀ x y z, δFar x z ≤ δFar x y + δFar y z := by decide

theorem steinerMST_far : steinerMST δFar [1, 2, 3] = [(1, 2), (1, 3)] := by
  have hs : sortEdges (completeEdges (terminalCost δFar [1, 2, 3])) =
      [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 2, 0⟩, ⟨0, 1, 10⟩, ⟨0, 2, 10⟩, ⟨1, 0, 10⟩, ⟨1, 2, 10⟩,
        ⟨2, 0, 10⟩, ⟨2, 1, 10⟩] := by
    rw [show completeEdges (terminalCost δFar [1, 2, 3]) =
        [⟨0, 0, 0⟩, ⟨0, 1, 10⟩, ⟨0, 2, 10⟩, ⟨1, 0, 10⟩, ⟨1, 1, 0⟩, ⟨1, 2, 10⟩, ⟨2, 0, 10⟩,
          ⟨2, 1, 10⟩, ⟨2, 2, 0⟩] by decide +kernel]
    simp [sortEdges_cons_cons]
  rw [steinerMST, kruskalEdges, hs]
  decide +kernel

/-- The tree on the terminals costs `20`, more than twice the star's `3`. -/
example : ¬ edgeCost δFar (steinerMST δFar [1, 2, 3]) ≤ 2 * steinerOpt δFar [1, 2, 3] := by
  have h := steinerOpt_le (δ := δFar) connects_star
  rw [steinerMST_far]
  change ¬ 20 ≤ _
  change _ ≤ 3 at h
  omega

/-! ### 3. Repeated terminals break the bound -/

/-- A constant cost: symmetric, with the triangle inequality, but nonzero on the diagonal. -/
def δFive (_ _ : Fin 4) : ℕ := 5

/-- With the terminal list `[1, 1]` the heuristic pays `5` to join the two copies of `1`, while the
empty edge list already connects them. -/
example : ¬ edgeCost δFive (steinerMST δFive [1, 1]) ≤ 2 * steinerOpt δFive [1, 1] := by
  have h : steinerOpt δFive [1, 1] = 0 := by
    refine Nat.le_zero.1 (steinerOpt_le (T := []) ?_)
    intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ha hb
    subst ha hb
    exact .refl _
  have hs : sortEdges (completeEdges (terminalCost δFive [1, 1])) =
      [⟨0, 0, 5⟩, ⟨0, 1, 5⟩, ⟨1, 0, 5⟩, ⟨1, 1, 5⟩] := by
    rw [show completeEdges (terminalCost δFive [1, 1]) =
        [⟨0, 0, 5⟩, ⟨0, 1, 5⟩, ⟨1, 0, 5⟩, ⟨1, 1, 5⟩] by decide +kernel]
    simp [sortEdges_cons_cons]
  rw [h, steinerMST, kruskalEdges, hs]
  decide +kernel

/-! ### 4. Edge cases -/

/-- No terminals: the empty tree. -/
example (δ : Fin 4 → Fin 4 → ℕ) : steinerMST δ [] = [] := by
  simp [steinerMST, kruskalEdges, completeEdges]

/-- One terminal: the empty tree, whatever the diagonal cost. -/
example (δ : Fin 4 → Fin 4 → ℕ) (a : Fin 4) : steinerMST δ [a] = [] := by
  have h := (kruskalEdges_isAcyclic (completeEdges (terminalCost δ [a]))).length_le_pred
    Nat.zero_lt_one
  rw [steinerMST, List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (Nat.le_of_succ_le_succ h))]
  rfl

/-! ### 5. Graphs -/

/-- The edges of the star `K_{1,3}` with centre `0`. -/
def starEdges : Finset (Sym2 (Fin 4)) := {s(0, 1), s(0, 2), s(0, 3)}

/-- The star graph `K_{1,3}`. -/
def starGraph : SimpleGraph (Fin 4) := fromEdgeSet (↑starEdges : Set (Sym2 (Fin 4)))

/-- Unit edge weights. -/
def unitWeight (_ : Sym2 (Fin 4)) : ℕ := 1

theorem edgeSet_starGraph : starGraph.edgeSet = (↑starEdges : Set (Sym2 (Fin 4))) := by
  rw [starGraph, edgeSet_fromEdgeSet]
  ext e
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  revert e
  decide

theorem reachable_star_zero (a : Fin 4) : starGraph.Reachable a 0 := by
  fin_cases a
  · exact .refl _
  all_goals exact (Adj.reachable (by rw [starGraph, fromEdgeSet_adj]; decide)).symm

theorem starGraph_preconnected : starGraph.Preconnected := fun a b =>
  (reachable_star_zero a).trans (reachable_star_zero b).symm

/-- The star graph has a shortest-walk oracle, so `IsShortestWalkOracle` is satisfiable here. -/
example : ∃ P, IsShortestWalkOracle unitWeight starGraph P :=
  exists_isShortestWalkOracle unitWeight starGraph_preconnected

theorem isSteinerSubgraph_star : IsSteinerSubgraph starGraph [1, 2, 3] starEdges := by
  refine ⟨edgeSet_starGraph.symm.subset, fun a _ b _ => ?_⟩
  rw [← starGraph]
  exact starGraph_preconnected a b

theorem eq_zero_of_mem_starEdges {i x : Fin 4} (hi : i ∈ [1, 2, 3]) (h : s(i, x) ∈ starEdges) :
    x = 0 := by
  revert i x
  decide

/-- In a Steiner subgraph of the star for the leaves, every leaf keeps its edge to the centre: a
walk from it to another leaf must start with that edge. -/
theorem mem_of_isSteinerSubgraph_star {F : Finset (Sym2 (Fin 4))}
    (hF : IsSteinerSubgraph starGraph [1, 2, 3] F) {i j : Fin 4} (hi : i ∈ [1, 2, 3])
    (hj : j ∈ [1, 2, 3]) (hij : i ≠ j) : s(0, i) ∈ F := by
  obtain ⟨p⟩ := hF.2 i hi j hj
  have hadj := p.adj_snd (Walk.not_nil_of_ne hij)
  rw [fromEdgeSet_adj] at hadj
  have hG : s(i, p.snd) ∈ starEdges := by
    rw [← Finset.mem_coe, ← edgeSet_starGraph]
    exact hF.1 hadj.1
  rw [Sym2.eq_swap, ← eq_zero_of_mem_starEdges hi hG]
  exact hadj.1

/-- Every Steiner subgraph of the star for the leaves contains the whole star. -/
theorem starEdges_subset {F : Finset (Sym2 (Fin 4))}
    (hF : IsSteinerSubgraph starGraph [1, 2, 3] F) : starEdges ⊆ F := by
  intro e he
  simp only [starEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact mem_of_isSteinerSubgraph_star hF (j := 2) (by decide) (by decide) (by decide)
  · exact mem_of_isSteinerSubgraph_star hF (j := 1) (by decide) (by decide) (by decide)
  · exact mem_of_isSteinerSubgraph_star hF (j := 1) (by decide) (by decide) (by decide)

theorem graphSteinerOpt_star : graphSteinerOpt starGraph unitWeight [1, 2, 3] = 3 := by
  refine le_antisymm ((graphSteinerOpt_le isSteinerSubgraph_star).trans_eq (by decide)) ?_
  obtain ⟨F, hF, hc⟩ := exists_isSteinerSubgraph_sum_eq_graphSteinerOpt (w := unitWeight)
    (fun u v => (starGraph_preconnected u v).some) [1, 2, 3]
  rw [← hc]
  calc 3 = starEdges.sum unitWeight := by decide
    _ ≤ F.sum unitWeight := Finset.sum_le_sum_of_subset (starEdges_subset hF)

/-- On the star the heuristic returns exactly the star, for any choice of walks. -/
theorem kmbEdges_star (P : ∀ u v : Fin 4, starGraph.Walk u v) :
    kmbEdges unitWeight P [1, 2, 3] = starEdges := by
  have hF := isSteinerSubgraph_kmbEdges (w := unitWeight) P [1, 2, 3]
  refine Finset.Subset.antisymm (fun e he => ?_) (starEdges_subset hF)
  rw [← Finset.mem_coe, ← edgeSet_starGraph]
  exact hF.1 he

/-- The guarantee on the star: `3 ≤ 2 · 3`. -/
example (P : ∀ u v : Fin 4, starGraph.Walk u v)
    (hP : IsShortestWalkOracle unitWeight starGraph P) :
    (kmbEdges unitWeight P [1, 2, 3]).sum unitWeight ≤ 2 * 3 := by
  have := sum_kmbEdges_le_two_mul_graphSteinerOpt hP (R := [1, 2, 3]) (by decide)
  rwa [graphSteinerOpt_star] at this

/-- A triangle whose edge `0 - 1` weighs `10` and whose other edges weigh `1`. -/
def triWeight (e : Sym2 (Fin 3)) : ℕ := if e = s(0, 1) then 10 else 1

/-- The detour through `2` joins `0` and `1`. -/
theorem isSteinerSubgraph_tri :
    IsSteinerSubgraph (⊤ : SimpleGraph (Fin 3)) [0, 1] {s(0, 2), s(2, 1)} := by
  have hadj : ∀ x y : Fin 3, s(x, y) ∈ ({s(0, 2), s(2, 1)} : Finset (Sym2 (Fin 3))) → x ≠ y →
      (fromEdgeSet (↑({s(0, 2), s(2, 1)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3)))).Adj
        x y :=
    fun x y h hne => (fromEdgeSet_adj _).2 ⟨h, hne⟩
  refine ⟨?_, fun a ha b hb => ?_⟩
  · intro e he
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at he
    rcases he with rfl | rfl <;> simp
  · have h02 := (hadj 0 2 (by decide) (by decide)).reachable
    have h21 := (hadj 2 1 (by decide) (by decide)).reachable
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact .refl _
    · exact h02.trans h21
    · exact (h02.trans h21).symm
    · exact .refl _

example : graphSteinerOpt (⊤ : SimpleGraph (Fin 3)) triWeight [0, 1] ≤ 2 :=
  (graphSteinerOpt_le isSteinerSubgraph_tri).trans_eq (by decide)

/-- Whatever shortest walks it is given, the heuristic does not use the heavy edge: its cost is at
most `2 · 2 = 4 < 10`. -/
example (P : ∀ u v : Fin 3, (⊤ : SimpleGraph (Fin 3)).Walk u v)
    (hP : IsShortestWalkOracle triWeight ⊤ P) : s(0, 1) ∉ kmbEdges triWeight P [0, 1] := by
  intro h
  have hle := sum_kmbEdges_le_two_mul hP (R := [0, 1]) (by decide) isSteinerSubgraph_tri
  have : triWeight s(0, 1) ≤ (kmbEdges triWeight P [0, 1]).sum triWeight :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) h
  have h10 : triWeight s(0, 1) = 10 := by decide
  have h2 : ({s(0, 2), s(2, 1)} : Finset (Sym2 (Fin 3))).sum triWeight = 2 := by decide
  omega

end ComplexityTests.SteinerTree
