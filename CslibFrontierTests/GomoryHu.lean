/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut

/-!
# Gomory–Hu tree tests

Exercise `Cslib.Algorithms.Lean.GomoryHu` on an explicit weighted graph on `Fin 4` with edges
`01:4`, `12:2`, `23:3`, `02:1`, `13:1`. Its minimum cut values are `λ(0, 1) = 5` and `λ = 4` for
every other pair, and the path `0 - 1 - 2 - 3` is a Gomory–Hu tree with sides `{0}`, `{0, 1}`,
`{0, 1, 2}`. The star centred at `1` is a spanning tree that is not a Gomory–Hu tree, and the path
is not a Gomory–Hu tree of a second graph with a heavy edge `02`.
-/

namespace CslibFrontierTests.GomoryHu

open Cslib.WeightedCut Cslib.Algorithms.Lean.GomoryHu
open SimpleGraph (edgeSide edgeSide_eq_of_forall_adj)

/-- The weighted graph on `Fin 4` with edges `01:4`, `12:2`, `23:3`, `02:1`, `13:1`. -/
private def W : Fin 4 → Fin 4 → ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => 4 | 1, 0 => 4
  | 1, 2 => 2 | 2, 1 => 2
  | 2, 3 => 3 | 3, 2 => 3
  | 0, 2 => 1 | 2, 0 => 1
  | 1, 3 => 1 | 3, 1 => 1
  | _, _ => 0

private theorem hW : IsMultigraph W := by
  unfold IsMultigraph
  decide

example : cutWeight W {0} = 5 := by decide
example : cutWeight W {0, 1} = 4 := by decide
example : cutWeight W {0, 1, 2} = 4 := by decide

/-! ### Minimum cuts -/

example : IsMinCutBetween (cutWeight W) 0 1 {0} := by
  unfold IsMinCutBetween
  decide

example : IsMinCutBetween (cutWeight W) 1 2 {0, 1} := by
  unfold IsMinCutBetween
  decide

example : IsMinCutBetween (cutWeight W) 2 3 {0, 1, 2} := by
  unfold IsMinCutBetween
  decide

/-- `{0, 1}` is a minimum `0`–`3` cut, so `λ(0, 3) = 4`. -/
example : minCutBetween W 0 3 = 4 := by
  have h : IsMinCutBetween (cutWeight W) 0 3 {0, 1} := by
    unfold IsMinCutBetween
    decide
  rw [← ((isMinCutBetween_cutWeight_iff W).mp h).2.2]
  decide

/-- The singleton `{0}` is not a minimum `0`–`3` cut. -/
example : ¬ IsMinCutBetween (cutWeight W) 0 3 {0} := by
  unfold IsMinCutBetween
  decide

/-! ### The path `0 - 1 - 2 - 3` is a Gomory–Hu tree -/

private theorem pathGraph_four_adj {u v : Fin 4} :
    (SimpleGraph.pathGraph 4).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val :=
  SimpleGraph.pathGraph_adj

/-- The side of `u` for the edge `uv` of the path `0 - 1 - 2 - 3`. -/
private def pathSide (u v : Fin 4) : Finset (Fin 4) :=
  if u < v then Finset.univ.filter (· ≤ u) else Finset.univ.filter (u ≤ ·)

private theorem edgeSide_pathGraph_four {u v : Fin 4} (huv : (SimpleGraph.pathGraph 4).Adj u v) :
    edgeSide (SimpleGraph.pathGraph 4) u v = pathSide u v := by
  refine edgeSide_eq_of_forall_adj (SimpleGraph.isTree_pathGraph_add_one 3) huv ?_ ?_ ?_
  · rw [pathGraph_four_adj] at huv
    revert u v
    decide
  · rw [pathGraph_four_adj] at huv
    revert u v
    decide
  · intro x y hxy
    rw [pathGraph_four_adj] at huv hxy
    revert u v x y
    decide

theorem isGomoryHuTree_pathGraph_four :
    IsGomoryHuTree (cutWeight W) (SimpleGraph.pathGraph 4) := by
  refine ⟨SimpleGraph.isTree_pathGraph_add_one 3, fun u v huv => ?_⟩
  rw [edgeSide_pathGraph_four huv]
  rw [pathGraph_four_adj] at huv
  revert u v
  unfold IsMinCutBetween
  decide

/-- The walk `0 - 1 - 2 - 3` in the path graph. -/
private def path03 : (SimpleGraph.pathGraph 4).Walk 0 3 :=
  .cons (v := 1) (pathGraph_four_adj.mpr (by decide)) <|
    .cons (v := 2) (pathGraph_four_adj.mpr (by decide)) <|
      .cons (pathGraph_four_adj.mpr (by decide)) .nil

/-- Flow-equivalence on the path: `λ(0, 3)` is the least of `λ(0, 1)`, `λ(1, 2)`, `λ(2, 3)`. -/
example : IsLeast ((fun d : (SimpleGraph.pathGraph 4).Dart => minCutBetween W d.fst d.snd) ''
    {d | d ∈ path03.darts}) (minCutBetween W 0 3) :=
  isGomoryHuTree_pathGraph_four.isLeast_minCutBetween (by decide)
    (SimpleGraph.Walk.IsPath.mk' (by decide))

/-- At most `4 - 1 = 3` distinct minimum cut values. -/
example : ((Finset.univ.offDiag : Finset (Fin 4 × Fin 4)).image
    fun p => minCutBetween W p.1 p.2).card ≤ 3 :=
  card_image_minCutBetween_le hW

/-- The triangle inequality, instantiated. -/
example : min (minCutBetween W 0 1) (minCutBetween W 1 3) ≤ minCutBetween W 0 3 :=
  min_le_minCutBetween W (by decide) 1

/-! ### Spanning trees that are not Gomory–Hu trees -/

/-- The star centred at `1`. -/
private def star : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun x _ => x = 1

/-- The star at `1` is not a Gomory–Hu tree of `W`: the side `{2}` of its edge `21` is not a
minimum `2`–`1` cut, since `cutWeight W {2} = 6` but `cutWeight W {2, 3} = 4`. -/
example : ¬ IsGomoryHuTree (cutWeight W) star := by
  intro hT
  have hadj : star.Adj 2 1 := by
    rw [star, SimpleGraph.fromRel_adj]
    decide
  have hside : edgeSide star 2 1 = {2} := by
    refine edgeSide_eq_of_forall_adj hT.isTree hadj (by decide) (by decide) ?_
    intro x y hxy
    rw [star, SimpleGraph.fromRel_adj] at hxy
    revert x y
    decide
  have h := hT.isMinCutBetween_edgeSide hadj
  rw [hside] at h
  revert h
  unfold IsMinCutBetween
  decide

/-- A graph with a heavy edge `02`: edges `01:1`, `02:5`, `12:1`, `23:1`. -/
private def W' : Fin 4 → Fin 4 → ℕ := fun u v =>
  match u.val, v.val with
  | 0, 1 => 1 | 1, 0 => 1
  | 0, 2 => 5 | 2, 0 => 5
  | 1, 2 => 1 | 2, 1 => 1
  | 2, 3 => 1 | 3, 2 => 1
  | _, _ => 0

/-- The path `0 - 1 - 2 - 3` is not a Gomory–Hu tree of `W'`: the side `{0}` of the edge `01`
weighs `6`, but `{0, 2, 3}` separates `0` from `1` with weight `2`. -/
example : ¬ IsGomoryHuTree (cutWeight W') (SimpleGraph.pathGraph 4) := by
  intro hT
  have hadj : (SimpleGraph.pathGraph 4).Adj 0 1 := by
    rw [pathGraph_four_adj]
    decide
  have h := hT.isMinCutBetween_edgeSide hadj
  rw [edgeSide_pathGraph_four hadj] at h
  revert h
  unfold IsMinCutBetween
  decide

/-! ### Edge cases -/

/-- The abstract theorem with values in `ℤ` rather than `ℕ`: the integer cut function of `W` is
symmetric and submodular, so it has a Gomory–Hu tree. -/
example : ∃ T : SimpleGraph (Fin 4), IsGomoryHuTree (fun X => (cutWeight W X : ℤ)) T :=
  exists_isGomoryHuTree (fun X => by simp only [cutWeight_compl' hW])
    (fun A B => by exact_mod_cast cutWeight_union_add_cutWeight_inter_le W A B)

/-- `λ(0, 1) = 5 > 4 = λ(1, 3)`, so the minimum is attained twice: `λ(0, 3) = λ(1, 3)`. -/
example : minCutBetween W 0 3 = minCutBetween W 3 1 := by
  rw [minCutBetween_comm hW 0 3]
  refine minCutBetween_eq_of_lt hW (by decide) ?_
  have h13 : IsMinCutBetween (cutWeight W) 1 0 {1, 2, 3} := by
    unfold IsMinCutBetween
    decide
  have h31 : IsMinCutBetween (cutWeight W) 3 1 {3} := by
    unfold IsMinCutBetween
    decide
  rw [← ((isMinCutBetween_cutWeight_iff W).mp h31).2.2,
    ← ((isMinCutBetween_cutWeight_iff W).mp h13).2.2]
  decide

/-- On a single vertex, the one-vertex tree is a Gomory–Hu tree of every set function. -/
example (f : Finset (Fin 1) → ℕ) : IsGomoryHuTree f (SimpleGraph.pathGraph 1) :=
  ⟨SimpleGraph.isTree_pathGraph_add_one 0, fun u v huv => absurd (Subsingleton.elim u v) huv.ne⟩

/-- `λ(s, s) = 0`. -/
example : minCutBetween W 2 2 = 0 := minCutBetween_self W 2

end CslibFrontierTests.GomoryHu
