/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.StoerWagner.Basic

/-!
# Stoer–Wagner minimum cut tests

Exercise maximum adjacency orderings and the Stoer–Wagner algorithm on small multigraphs, checked
against brute force over all vertex sets:

* a 4-cycle with weights `3, 1, 4, 2`, minimum cut `3`;
* the 8-vertex example graph of [StoerWagner1997], as reproduced in secondary sources, minimum
  cut `4`; maximum adjacency search from its vertex `2` (`1` here, 0-indexed) gives the ordering of
  the first phase of the worked example, ending with the cut of the phase `{1}` (`{0}` here) of
  weight `5`;
* an ordering that is not a maximum adjacency ordering, whose last vertex does not give a minimum
  cut between its last two vertices;
* a disconnected graph and the degenerate sizes `n = 0, 1, 2`.
-/

namespace ComplexityTests.StoerWagner

open Cslib.WeightedCut Cslib.Algorithms.Lean.StoerWagner

/-- The symmetric matrix with zero diagonal given by its entries above the diagonal. -/
private def sym {n : ℕ} (f : Fin n → Fin n → ℕ) : Fin n → Fin n → ℕ :=
  fun i j => if i < j then f i j else if j < i then f j i else 0

/-! ### A weighted 4-cycle -/

/-- The 4-cycle `0 - 1 - 2 - 3 - 0` with weights `3, 1, 4, 2`. -/
private def G4 : Fin 4 → Fin 4 → ℕ := sym fun i j =>
  match i.val, j.val with
  | 0, 1 => 3 | 1, 2 => 1 | 2, 3 => 4 | 0, 3 => 2 | _, _ => 0

private theorem isMultigraph_G4 : IsMultigraph G4 := by
  unfold IsMultigraph
  decide

example : (stoerWagner G4).weight = 3 := by decide

example : (stoerWagner G4).side = {2, 3} := by decide

/-- Brute force: every non-trivial cut of `G4` weighs at least `3`. -/
example : ∀ C : Finset (Fin 4), C.Nonempty → C ≠ Finset.univ → 3 ≤ cutWeight G4 C := by
  decide

example : minCut G4 = 3 :=
  (stoerWagner_spec (by decide) isMultigraph_G4).2.2.symm.trans (by decide)

/-! ### The example graph of Stoer and Wagner -/

/-- The 8-vertex example graph of [StoerWagner1997] (vertices `1, …, 8` there, `0, …, 7` here),
with the edge weights of its reproduction in secondary sources. -/
private def G8 : Fin 8 → Fin 8 → ℕ := sym fun i j =>
  match i.val + 1, j.val + 1 with
  | 1, 2 => 2 | 1, 5 => 3 | 2, 3 => 3 | 2, 5 => 2 | 2, 6 => 2 | 3, 4 => 4 | 3, 7 => 2
  | 4, 7 => 2 | 4, 8 => 2 | 5, 6 => 3 | 6, 7 => 1 | 7, 8 => 3 | _, _ => 0

private theorem isMultigraph_G8 : IsMultigraph G8 := by
  unfold IsMultigraph
  decide

example : (stoerWagner G8).weight = 4 := by decide

example : (stoerWagner G8).side = {2, 3, 6, 7} := by decide

/-- Brute force: every non-trivial cut of `G8` weighs at least `4`. -/
example : ∀ C : Finset (Fin 8), C.Nonempty → C ≠ Finset.univ → 4 ≤ cutWeight G8 C := by
  decide +kernel

example : minCut G8 = 4 :=
  (stoerWagner_spec (by decide) isMultigraph_G8).2.2.symm.trans (by decide)

/-- The ordering of the algorithm's first phase, by maximum adjacency search from vertex `0`. -/
example : maOrder G8 = [0, 4, 1, 5, 2, 3, 6, 7] := by decide

/-- Maximum adjacency search from vertex `1` (vertex `2` of [StoerWagner1997]) gives the ordering
`2, 3, 4, 7, 8, 6, 5, 1` of the first phase of the worked example. -/
example : maSearch G8 8 (fun _ => 0) [1, 0, 2, 3, 4, 5, 6, 7] = [1, 2, 3, 6, 7, 5, 4, 0] := by
  decide

example : IsMAOrdering G8 [1, 2, 3, 6, 7, 5, 4, 0] := by decide

/-- The cut of that phase is `{0}`, of weight `5`. -/
example : cutWeight G8 {0} = 5 := by decide

/-- The MA-ordering lemma for that ordering: `{0}` is a minimum cut separating `4` and `0`. -/
example (C : Finset (Fin 8)) (hC : 4 ∈ C ↔ 0 ∉ C) : cutWeight G8 {0} ≤ cutWeight G8 C :=
  cutWeight_singleton_le_of_isMAOrdering isMultigraph_G8 (p := [1, 2, 3, 6, 7, 5])
    (by decide) hC

/-- The same lemma as a value: the minimum `4`–`0` cut weight `λ(4, 0)` is `5`. -/
example : minCutBetween G8 4 0 = 5 :=
  (cutWeight_singleton_eq_minCutBetween_of_isMAOrdering isMultigraph_G8
    (p := [1, 2, 3, 6, 7, 5]) (by decide)).symm.trans (by decide)

/-- Brute force for the same statement, and it is tight: `{0}` is not heavier than needed. -/
example : ∀ C : Finset (Fin 8), (4 ∈ C ↔ 0 ∉ C) → 5 ≤ cutWeight G8 C := by
  decide +kernel

/-- The identity ordering is not a maximum adjacency ordering: after `0`, vertex `4` is attached
more strongly than vertex `1`. -/
example : ¬ IsMAOrdering G8 (List.finRange 8) := by decide

/-- Without the maximum adjacency property the lemma fails: this ordering ends with `2, 3`, but the
cut `{3, 6, 7}` separating `2` and `3` is lighter than `{3}`. -/
example : ¬ IsMAOrdering G8 [0, 1, 4, 5, 6, 7, 2, 3] ∧
    cutWeight G8 {3, 6, 7} < cutWeight G8 {3} := by
  decide

/-! ### The example of the Boost Graph Library -/

/-- The weighted graph of the Boost Graph Library example `stoer_wagner.cpp` (Boost 1.46.1,
https://www.boost.org/doc/libs/1_46_1/libs/graph/example/stoer_wagner.cpp), with its two parallel
edges `{3, 4}` of weights `0` and `4` merged. The example asserts minimum cut weight `7`. -/
private def boost : Fin 8 → Fin 8 → ℕ := sym fun i j =>
  match i.val, j.val with
  | 3, 4 => 4 | 3, 6 => 3 | 3, 5 => 1 | 0, 4 => 3 | 0, 1 => 1 | 0, 6 => 2 | 0, 7 => 6
  | 0, 5 => 1 | 0, 2 => 8 | 1, 4 => 1 | 1, 6 => 1 | 1, 5 => 80 | 6, 7 => 2 | 5, 7 => 1
  | 2, 5 => 1 | _, _ => 0

private theorem isMultigraph_boost : IsMultigraph boost := by
  unfold IsMultigraph
  decide

example : (stoerWagner boost).weight = 7 := by decide

example : cutWeight boost (stoerWagner boost).side = 7 := by decide

/-- Brute force: every non-trivial cut of `boost` weighs at least `7`. -/
example : ∀ C : Finset (Fin 8), C.Nonempty → C ≠ Finset.univ → 7 ≤ cutWeight boost C := by
  decide +kernel

example : minCut boost = 7 :=
  (stoerWagner_spec (by decide) isMultigraph_boost).2.2.symm.trans (by decide)

/-! ### Degenerate cases -/

/-- Two components `{0, 1}` and `{2, 3}`. -/
private def disconnected : Fin 4 → Fin 4 → ℕ := sym fun i j =>
  match i.val, j.val with
  | 0, 1 => 5 | 2, 3 => 7 | _, _ => 0

example : (stoerWagner disconnected).weight = 0 := by decide

example : cutWeight disconnected (stoerWagner disconnected).side = 0 := by decide

/-- A single edge of weight `6`. -/
private def edge : Fin 2 → Fin 2 → ℕ := sym fun _ _ => 6

example : stoerWagner edge = ⟨{1}, 6⟩ := by decide

example (W : Fin 1 → Fin 1 → ℕ) : stoerWagner W = ⟨∅, 0⟩ := rfl

example (W : Fin 0 → Fin 0 → ℕ) : stoerWagner W = ⟨∅, 0⟩ := rfl

/-! ### Cost -/

example : (stoerWagnerM G8).time ≤ 640 := time_stoerWagnerM_le G8

end ComplexityTests.StoerWagner
