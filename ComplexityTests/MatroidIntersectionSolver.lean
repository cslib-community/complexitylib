/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Matroid.Intersection.Konig
import Complexity.Algorithms.Lean.Query.Matroid.Intersection
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.Fintype.Fin

/-!
# Tests for the matroid intersection solver

Exercises:
1. Breadth-first search (`Cslib.Reachability.findWalk`): a shortest walk when a longer one also
   exists, and a separator when no walk exists.
2. Bipartite matching on the three-edge path `(1,0) — (0,0) — (0,1)`, with the middle edge
   listed first: the solver first matches `(0,0)`, then needs the three-vertex augmenting walk
   `(1,0) → (0,0) → (0,1)`, returns the maximum matching `{(1,0), (0,1)}` with the separator of
   all three edges (whose left endpoints `{0, 1}` cover the graph), and makes exactly
   `20 = 6 + 8 + 6` queries, as `countQueries_matroidIntersection` predicts.
3. Colourful forests: the graphic matroid of a triangle with a pendant edge, intersected with a
   colour partition matroid. The maximum colourful forest is a spanning tree with one edge of each
   colour. The solver first picks the red edge `0`, which lies in no maximum colourful forest, and
   later exchanges it for the other red edge `3`.
4. Universe polymorphism: the pure solver and its correctness theorem at `Type 1`.
-/

namespace ComplexityTests.MatroidIntersectionSolver

open Cslib.Algorithms.Lean.Matroid Cslib.Reachability Cslib.Query

/-! ## 1. Breadth-first search -/

/-- The path `0 → 1 → 2 → 3` with the extra arc `0 → 2`. -/
private def pathArc : Fin 4 → Fin 4 → Bool
  | 0, 1 => true
  | 1, 2 => true
  | 2, 3 => true
  | 0, 2 => true
  | _, _ => false

/-- From `0` to `3`, the search takes the shortcut `0 → 2`. -/
example : findWalk [0, 1, 2, 3] pathArc (· == 0) (· == 3) = .inl [0, 2, 3] := by decide

/-- The walk `[0, 1, 2, 3]` exists, but it is not shortest. -/
example : IsSrcTgtWalk [0, 1, 2, 3] pathArc (· == 0) (· == 3) [0, 1, 2, 3] ∧
    ¬ IsShortestSrcTgtWalk [0, 1, 2, 3] pathArc (· == 0) (· == 3) [0, 1, 2, 3] := by
  refine ⟨⟨List.cons_ne_nil _ _, rfl, rfl, by decide, by decide⟩, fun h => ?_⟩
  have := h.2 [0, 2, 3]
    (isShortestSrcTgtWalk_of_findWalk_eq_inl (V := [0, 1, 2, 3]) (by decide)).1
  simp at this

/-- From `2`, the target `0` is unreachable; the search returns the separator `{2, 3}`. -/
example : findWalk [0, 1, 2, 3] pathArc (· == 2) (· == 0) = .inr [2, 3] := by decide

example : IsSrcTgtSeparator [0, 1, 2, 3] pathArc (· == 2) (· == 0) [2, 3] :=
  isSrcTgtSeparator_of_findWalk_eq_inr (by decide)

/-! ## 2. Bipartite matching on a path -/

/-- The independence test of a unit-capacity partition matroid: `f` is injective on `S`. -/
private def injTest {α β : Type*} [DecidableEq β] (f : α → β) (S : Finset α) : Bool :=
  decide ((S.image f).card = S.card)

private theorem injTest_iff {α β : Type*} [DecidableEq β] (f : α → β)
    (S : Finset α) : injTest f S = true ↔ (unitPartitionMatroid f).Indep (S : Set α) := by
  rw [unitPartitionMatroid_indep_iff, injTest, decide_eq_true_eq, Finset.card_image_iff]

private abbrev E := Fin 2 × Fin 2

private abbrev path : List E := [(0, 0), (1, 0), (0, 1)]

/-- Phase 1 matches the first candidate `(0,0)`. Phase 2 finds the walk `(1,0) → (0,0) → (0,1)`
in the exchange digraph of `{(0,0)}` and augments to `{(1,0), (0,1)}`. Phase 3 finds no source,
so nothing is reachable and the separator is the whole edge set. -/
theorem path_run :
    maxCommonIndep (injTest Prod.fst) (injTest Prod.snd) path =
      ({(1, 0), (0, 1)}, {(0, 0), (1, 0), (0, 1)}) := by
  decide

/-- The solver's output is a maximum matching. -/
example : IsMaxCommonIndep (unitPartitionMatroid (Prod.fst : E → Fin 2))
    (unitPartitionMatroid Prod.snd) path.toFinset {(1, 0), (0, 1)} := by
  have h := (maxCommonIndep_spec (injTest_iff Prod.fst) (injTest_iff Prod.snd) path).1
  rwa [path_run] at h

/-- The two partition-matroid oracles. -/
private abbrev pathOracle : {ι : Type} → IndepPairQuery E ι → ι :=
  IndepPairQuery.pair (IndepQuery.oracleOf (injTest Prod.fst))
    (IndepQuery.oracleOf (injTest Prod.snd))

example : (matroidIntersection path).eval pathOracle =
    ({(1, 0), (0, 1)}, {(0, 0), (1, 0), (0, 1)}) := by
  rw [eval_matroidIntersection]
  exact path_run

/-- Three phases, from `|I| = 0, 1, 2`: `2·3·1 + 2·2·2 + 2·1·3 = 20` queries. -/
example : (matroidIntersection path).countQueries pathOracle = 20 := by decide

/-- The same count from `countQueries_matroidIntersection`. -/
example : (matroidIntersection path).countQueries pathOracle = 20 := by
  rw [countQueries_matroidIntersection (oracle := pathOracle) (M₁ := unitPartitionMatroid Prod.fst)
    (M₂ := unitPartitionMatroid Prod.snd) (injTest_iff Prod.fst) (injTest_iff Prod.snd),
    eval_matroidIntersection]
  decide

/-! ## 3. Colourful forests -/

/-- The forests of the graph on `{0, 1, 2, 3}` with edges `0:{0,1}`, `1:{1,2}`, `2:{0,2}` and
`3:{2,3}`: its only cycle is the triangle `{0, 1, 2}`. -/
private def forestTest (S : Finset (Fin 4)) : Bool :=
  !(decide ((0 : Fin 4) ∈ S) && decide ((1 : Fin 4) ∈ S) && decide ((2 : Fin 4) ∈ S))

private theorem forest_empty : forestTest ∅ = true := by decide

private theorem forest_hered :
    ∀ ⦃A B : Finset (Fin 4)⦄, forestTest B = true → A ⊆ B → forestTest A = true := by
  decide

private theorem forest_aug :
    ∀ ⦃I J : Finset (Fin 4)⦄, forestTest I = true → forestTest J = true → I.card < J.card →
      ∃ e ∈ J, e ∉ I ∧ forestTest (insert e I) = true := by
  decide

/-- The graphic matroid of the triangle with a pendant edge. -/
private noncomputable def forestMatroid : Matroid (Fin 4) :=
  (IndepMatroid.ofFinset Set.univ (fun S => forestTest S = true) forest_empty forest_hered
    forest_aug (fun _ _ => Set.subset_univ _)).matroid

private theorem forestTest_iff (S : Finset (Fin 4)) :
    forestTest S = true ↔ forestMatroid.Indep (S : Set (Fin 4)) := by
  simp [forestMatroid]

/-- Edge colours: edges `0` and `3` are red (`0`), edge `1` is green (`1`), edge `2` is blue
(`2`). -/
private def colour : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 0

/-- `{1, 2, 3}` is a maximum colourful forest. Starting from `∅`, the solver adds edges `0`, `1`,
then trades the red edge `0` for the red edge `3` while adding `2`, along the walk `3 → 0 → 2`. -/
theorem forest_run :
    maxCommonIndep forestTest (injTest colour) [0, 1, 2, 3] = ({1, 2, 3}, Finset.univ) := by
  decide

example : IsMaxCommonIndep forestMatroid (unitPartitionMatroid colour)
    ([0, 1, 2, 3] : List (Fin 4)).toFinset {1, 2, 3} := by
  have h := (maxCommonIndep_spec forestTest_iff (injTest_iff colour) [0, 1, 2, 3]).1
  rwa [forest_run] at h

/-- Four phases, from `|I| = 0, 1, 2, 3`: `8 + 12 + 12 + 8 = 40` queries. -/
example : (matroidIntersection ([0, 1, 2, 3] : List (Fin 4))).countQueries
    (IndepPairQuery.pair (IndepQuery.oracleOf forestTest)
      (IndepQuery.oracleOf (injTest colour))) = 40 := by
  decide

/-! ## 4. Universe polymorphism -/

example {α : Type 1} [DecidableEq α] {M₁ M₂ : Matroid α} {indep₁ indep₂ : Finset α → Bool}
    (h₁ : ∀ S, indep₁ S = true ↔ M₁.Indep (S : Set α))
    (h₂ : ∀ S, indep₂ S = true ↔ M₂.Indep (S : Set α)) (es : List α) :
    IsMaxCommonIndep M₁ M₂ es.toFinset (maxCommonIndep indep₁ indep₂ es).1 :=
  (maxCommonIndep_spec h₁ h₂ es).1

end ComplexityTests.MatroidIntersectionSolver
