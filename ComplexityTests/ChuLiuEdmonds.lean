/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Arborescence.ChuLiuEdmonds
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for the Chu–Liu/Edmonds algorithm

Exercise `Cslib.Algorithms.Lean.Arborescence.edmonds` on the digraph on `Fin 4` with arcs
`1→0:10`, `2→0:5`, `1→2:1`, `2→1:1`, `3→1:2`, `2→3:0`, `3→2:4`, rooted at `0`:

* the cheapest arcs are `1→2`, `2→3`, `3→1` (the selection `[0, 2, 3, 1]`), a `3`-cycle, so the
  algorithm contracts it;
* the result is the parent array `[0, 2, 0, 1]` (arcs `1→2`, `2→0`, `3→1`) of cost `8`, hence
  (by `edmonds_spec`) every spanning in-arborescence rooted at `0` costs at least `8`; the
  arborescence `[0, 0, 0, 1]` costs `17`;
* with costs shifted by `-20` in `ℤ` the result is the same tree, of cost `-52`;
* `edmondsOut` on the reversed digraph with reversed costs returns the same parent array;
* edge cases: a digraph with no in-arborescence rooted at `0` (the algorithm returns `none`), and
  a single vertex.
-/

namespace ComplexityTests.ChuLiuEdmonds

open Cslib.Algorithms.Lean.Arborescence

/-- The arcs of the test digraph. -/
private def arcs : List (Fin 4 × Fin 4) := [(1, 0), (2, 0), (1, 2), (2, 1), (3, 1), (2, 3), (3, 2)]

/-- The test digraph on `Fin 4`. -/
private def G : Digraph (Fin 4) where
  Adj u w := (u, w) ∈ arcs

private instance : DecidableRel G.Adj := fun u w => inferInstanceAs (Decidable ((u, w) ∈ arcs))

/-- The arc costs (`100` off the arcs). -/
private def cost : Fin 4 → Fin 4 → ℕ := fun u w =>
  match u.val, w.val with
  | 1, 0 => 10 | 2, 0 => 5 | 1, 2 => 1 | 2, 1 => 1 | 3, 1 => 2 | 2, 3 => 0 | 3, 2 => 4
  | _, _ => 100

/-- The optimal parent array `[0, 2, 0, 1]`. -/
private def opt : Fin 4 → Fin 4 := ![0, 2, 0, 1]

/-- The cheapest arcs out of the non-root vertices are `1→2`, `2→3` and `3→1`. -/
example : (List.finRange 4).map (cheapestParent (fun u w => decide (G.Adj u w)) cost 0) =
    [0, 2, 3, 1] := by
  decide

/-- They contain a cycle, so `edmonds` contracts. -/
example : findCycle 0 (cheapestParent (fun u w => decide (G.Adj u w)) cost 0) ≠ none := by
  decide

example : edmonds G cost 0 = some opt := by decide

example : parentCost cost 0 opt = 8 := by decide

/-- The output is a minimum-cost spanning in-arborescence: every spanning in-arborescence rooted
at `0` costs at least `8`. -/
example : IsInArborescenceParent G.Adj 0 opt ∧
    ∀ t, IsInArborescenceParent G.Adj 0 t → 8 ≤ parentCost cost 0 t := by
  obtain ⟨h, hmin⟩ := (edmonds_spec (G := G) (c := cost) (r := 0)).1 opt (by decide)
  exact ⟨h, fun t ht => (show parentCost cost 0 opt = 8 by decide) ▸ hmin t ht⟩

/-- A spanning in-arborescence of larger cost: the arcs `1→0`, `2→0`, `3→1`. -/
example : IsInArborescenceParent G.Adj 0 ![0, 0, 0, 1] ∧ parentCost cost 0 ![0, 0, 0, 1] = 17 :=
  ⟨⟨by decide, by decide, fun v => ⟨2, by revert v; decide⟩⟩, by decide⟩

/-- The digraph form: the digraph of the output is a spanning in-arborescence of `G` of arc
cost `8`. -/
example : (Digraph.parentDigraph 0 opt).IsInArborescence 0 ∧ Digraph.parentDigraph 0 opt ≤ G ∧
    arcCost (Digraph.parentDigraph 0 opt) cost = 8 := by
  obtain ⟨h1, h2, -⟩ := edmonds_optimal (G := G) (c := cost) (r := 0) (p := opt) (by decide)
  exact ⟨h1, h2, by rw [arcCost_parentDigraph]; decide⟩

/-- Negative costs: shifting every cost by `-20` gives the same tree, of cost `8 - 60`. -/
example : edmonds G (fun u w => (cost u w : ℤ) - 20) 0 = some opt := by decide

example : parentCost (fun u w => (cost u w : ℤ) - 20) 0 opt = -52 := by decide

/-- Out-arborescences: on the reversed digraph with reversed costs, `edmondsOut` returns the same
parent array. -/
private def Grev : Digraph (Fin 4) where
  Adj u w := G.Adj w u

private instance : DecidableRel Grev.Adj := fun u w => inferInstanceAs (Decidable (G.Adj w u))

example : edmondsOut Grev (fun u w => cost w u) 0 = some opt := by decide

/-- A digraph on `Fin 3` in which `0` is unreachable. -/
private def H : Digraph (Fin 3) where
  Adj u w := (u, w) ∈ ([(1, 2), (2, 1)] : List (Fin 3 × Fin 3))

private instance : DecidableRel H.Adj :=
  fun u w => inferInstanceAs (Decidable ((u, w) ∈ ([(1, 2), (2, 1)] : List (Fin 3 × Fin 3))))

example : edmonds H (fun _ _ => (1 : ℤ)) 0 = none := by decide

/-- Hence `H` has no spanning in-arborescence rooted at `0`. -/
example : ∀ t, ¬ IsInArborescenceParent H.Adj 0 t :=
  (edmonds_eq_none_iff (G := H) (c := fun _ _ => (1 : ℤ)) (r := 0)).mp (by decide)

/-- A single vertex: the empty arborescence. -/
example : edmonds (⊥ : Digraph (Fin 1)) (fun _ _ => (0 : ℕ)) 0 = some id := by decide

end ComplexityTests.ChuLiuEdmonds
