/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Init
public import Complexity.Algorithms.Lean.MaxFlow.BipartiteMatching

/-!
# Network Flow, Edmonds–Karp, and Bipartite Matching Tests

Kernel-checked examples and non-vacuity witnesses (without `native_decide`) exercising:

1. **CLRS 6-vertex network (CLRS 2nd ed., Figure 26.1(a), with antiparallel arcs `(1, 2)` and
   `(2, 1)`; compare [CLRS2009], Figures 26.1–26.2, pp. 710–711):** both `edmondsKarpDenseM` and
   sparse `edmondsKarpM` find a maximum flow of value `23` and minimum `s`-`t` cut `{0, 1, 2, 4}`
   of capacity `23`.
2. **Large-capacity diamond (`M = 10^9`), backward-arc cancellation, and simultaneous antiparallel
   flow:** `edmondsKarpDenseM` terminates in `2` shortest-path augmentations (`2 * 10^9` flow)
   independent of capacity magnitude; augmenting along `[0, 1, 2, 3]` followed by `bfsM` exercises
   residual backward-arc cancellation along `[0, 2, 1, 3]`; and `bothWaysFlow` exercises
   simultaneous forward push and reverse cancellation across an antiparallel pair carrying positive
   flow in both directions.
3. **Bipartite matching, König's Theorem, and `HasPerfectMatching`:** asymmetric `Fin 3 × Fin 4`
   matching/cover duality (`card = size = 2`), positive and negative `decidePerfectMatchingM`
   instances on `Fin 3 × Fin 3`, and universe-polymorphic `Type 1` instantiations.
4. **Positive and negative witnesses** for `Network.IsCut`, `Network.Flow`, `Flow.IsAugmentingPath`,
   `AdjValid`, `IsMatching`, `IsVertexCover`, and positive `Θ(n)` `bfsM` cost on edgeless graphs.
-/

public section

namespace ComplexityTests.MaxFlow

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow

/-! ### 1. CLRS 6-vertex network (max flow = min cut = 23) -/

/-- Six-vertex shipping network (`s = 0`, `t = 5`) retaining both antiparallel arcs `(1, 2) ↦ 10`
and `(2, 1) ↦ 4` from CLRS 2nd ed., Figure 26.1(a) (compare [CLRS2009], Figures 26.1–26.2,
pp. 710–711, which split the antiparallel pair while keeping maximum flow and minimum cut `23`). -/
def clrsNet : Network (Fin 6) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 16
    | 0, 2 => 13
    | 1, 2 => 10
    | 2, 1 => 4
    | 1, 3 => 12
    | 3, 2 => 9
    | 2, 4 => 14
    | 4, 3 => 7
    | 3, 5 => 20
    | 4, 5 => 4
    | _, _ => 0
  s := 0
  t := 5

/-- Sparse symmetric adjacency lists for `clrsNet`. -/
def clrsAdj : Fin 6 → List (Fin 6)
  | ⟨0, _⟩ => [1, 2]
  | ⟨1, _⟩ => [0, 2, 3]
  | ⟨2, _⟩ => [0, 1, 3, 4]
  | ⟨3, _⟩ => [1, 2, 4, 5]
  | ⟨4, _⟩ => [2, 3, 5]
  | ⟨5, _⟩ => [3, 4]

theorem clrsAdj_valid : AdjValid clrsNet clrsAdj := by decide

example : ¬ AdjValid clrsNet (fun _ => []) := by decide

example : (edmondsKarpDenseM clrsNet).ret.flow.value = 23 := by decide

example : (edmondsKarpDenseM clrsNet).ret.cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide

example : clrsNet.cutCapacity ({0, 1, 2, 4} : Finset (Fin 6)) = 23 := by decide

example : (edmondsKarpM clrsNet clrsAdj).ret.flow.value = 23 := by decide

example : (edmondsKarpM clrsNet clrsAdj).ret.cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide

example :
    (edmondsKarpM clrsNet clrsAdj).ret.flow.IsMaxFlow ∧
      clrsNet.IsMinCut (edmondsKarpM clrsNet clrsAdj).ret.cut := by
  obtain ⟨hmax, hmin, _⟩ := edmondsKarpM_correct clrsAdj_valid (by decide)
  exact ⟨hmax, hmin⟩

/-! ### 2. Capacity-independent `2`-augmentation diamond and backward-arc cancellation -/

/-- Ford–Fulkerson diamond network with `M = 10^9` outer capacities and unit cross arc `1 → 2`
([CLRS2009], Figure 26.6, p. 727). -/
def largeDiamondNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 1000000000
    | 0, 2 => 1000000000
    | 1, 2 => 1
    | 1, 3 => 1000000000
    | 2, 3 => 1000000000
    | _, _ => 0
  s := 0
  t := 3

example : (edmondsKarpDenseM largeDiamondNet).ret.augmentations = 2 := rfl

example : (edmondsKarpDenseM largeDiamondNet).ret.flow.value = 2000000000 := by decide

example : (edmondsKarpDenseM largeDiamondNet).ret.cut = ({0} : Finset (Fin 4)) := by decide

example : largeDiamondNet.cutCapacity ({0} : Finset (Fin 4)) = 2000000000 := by decide

/-- Unit diamond network exercising residual backward-arc cancellation after a zig-zag path. -/
def unitDiamondNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 2 => 1
    | 1, 3 => 1
    | 2, 3 => 1
    | _, _ => 0
  s := 0
  t := 3

theorem zigZag_augPath :
    (Network.Flow.zero unitDiamondNet).IsAugmentingPath [0, 1, 2, 3] := by
  decide

/-- After pushing `1` unit along `[0, 1, 2, 3]`, BFS discovers `[0, 2, 1, 3]` via backward residual
arc `2 → 1`. -/
def afterZigZag : unitDiamondNet.Flow :=
  (Network.Flow.zero unitDiamondNet).augmentByBottleneck [0, 1, 2, 3] zigZag_augPath

example : afterZigZag.value = 1 := by decide

example : afterZigZag.resCap 2 1 = 1 ∧ afterZigZag.resCap 1 2 = 0 := by decide

example :
    (bfsM unitDiamondNet (defaultAdj 4) afterZigZag).ret.augPath = some [0, 2, 1, 3] := rfl

/-- Four-vertex antiparallel network (`cap 1 2 = 3`, `cap 2 1 = 2`) testing simultaneous positive
flow in both directions (`f 1 2 = 2` and `f 2 1 = 1`). -/
def antiparallelNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 5
    | 0, 2 => 5
    | 1, 2 => 3
    | 2, 1 => 2
    | 1, 3 => 5
    | 2, 3 => 5
    | _, _ => 0
  s := 0
  t := 3

/-- Feasible flow on `antiparallelNet` carrying positive flow on both `(1, 2)` and `(2, 1)`. -/
def bothWaysFlow : antiparallelNet.Flow where
  toFun u v :=
    match u.1, v.1 with
    | 0, 1 => 2
    | 1, 2 => 2
    | 2, 1 => 1
    | 1, 3 => 1
    | 2, 3 => 1
    | _, _ => 0
  le_cap := by decide
  conserve := by decide

theorem bothWays_augPath : bothWaysFlow.IsAugmentingPath [0, 1, 2, 3] := by decide

def afterBothWays : antiparallelNet.Flow :=
  bothWaysFlow.augmentByBottleneck [0, 1, 2, 3] bothWays_augPath

example : bothWaysFlow 1 2 = 2 ∧ bothWaysFlow 2 1 = 1 ∧ bothWaysFlow.resCap 1 2 = 2 := by decide

example :
    afterBothWays 1 2 = 3 ∧ afterBothWays 2 1 = 0 ∧ afterBothWays.value = 4 := by decide

/-- Edgeless 4-vertex network verifying positive `Θ(n)` table/cut work in `bfsM`. -/
def edgelessNet : Network (Fin 4) where
  cap _ _ := 0
  s := 0
  t := 3

example : 4 ≤ (bfsM edgelessNet (fun _ => []) (Network.Flow.zero edgelessNet)).time := by decide

/-! ### 3. Bipartite matching, König's Theorem, and `HasPerfectMatching` -/

/-- Asymmetric `3 × 4` bipartite graph where left vertices `{0, 1, 2}` have neighborhood `{0, 1}`
on the right (`0` connects to `{0, 1}`; `1` and `2` connect only to `0`), so the maximum matching
and minimum vertex cover both have cardinality `2`. -/
def asymGraph : Fin 3 × Fin 4 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

example : (bipartiteMatchingM asymGraph).ret.matching.card = 2 := by decide

example : (bipartiteMatchingM asymGraph).ret.cover.size = 2 := by decide

example :
    IsMaxMatching asymGraph (bipartiteMatchingM asymGraph).ret.matching ∧
      IsMinVertexCover asymGraph (bipartiteMatchingM asymGraph).ret.cover := by
  obtain ⟨hmax, hmin, _⟩ := bipartiteMatchingM_correct asymGraph
  exact ⟨hmax, hmin⟩

/-- `3 × 3` bipartite graph with a unique perfect matching `(0, 1), (1, 2), (2, 0)`. -/
def perfGraph : Fin 3 × Fin 3 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨2, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

/-- `3 × 3` bipartite graph violating Hall's condition (`{1, 2}` only neighbors `{0}`). -/
def noPerfGraph : Fin 3 × Fin 3 → Bool
  | (⟨0, _⟩, ⟨0, _⟩) => true
  | (⟨0, _⟩, ⟨1, _⟩) => true
  | (⟨1, _⟩, ⟨0, _⟩) => true
  | (⟨2, _⟩, ⟨0, _⟩) => true
  | _ => false

theorem perfGraph_hasPerfectMatching :
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching perfGraph :=
  (decidePerfectMatchingM_eq_true_iff perfGraph).mp rfl

theorem noPerfGraph_not_hasPerfectMatching :
    ¬ Cslib.Circuits.BipartiteMatching.HasPerfectMatching noPerfGraph := by
  rw [← decidePerfectMatchingM_eq_true_iff noPerfGraph]
  decide

/-! ### 4. Positive/negative predicate witnesses and `Type 1` polymorphism -/

-- Positive and negative `IsCut` witnesses
example : unitDiamondNet.IsCut ({0, 1} : Finset (Fin 4)) := by decide
example : ¬ unitDiamondNet.IsCut ({1, 2} : Finset (Fin 4)) := by decide
example : ¬ unitDiamondNet.IsCut ({0, 3} : Finset (Fin 4)) := by decide

-- Non-zero `Network.Flow` witness (`afterZigZag`) and negative `IsAugmentingPath` witness
example : afterZigZag ≠ Network.Flow.zero unitDiamondNet := by
  intro h
  have hval : afterZigZag.value = (Network.Flow.zero unitDiamondNet).value :=
    congrArg Network.Flow.value h
  revert hval
  decide

example : ¬ afterZigZag.IsAugmentingPath [0, 1, 2, 3] := by decide

-- Positive and negative `IsMatching` witnesses
example : IsMatching asymGraph ({(0, 1), (1, 0)} : Finset (Fin 3 × Fin 4)) := by decide
example : ¬ IsMatching asymGraph ({(0, 0), (1, 0)} : Finset (Fin 3 × Fin 4)) := by decide
example : ¬ IsMatching asymGraph ({(2, 3)} : Finset (Fin 3 × Fin 4)) := by decide

-- Positive and negative `IsVertexCover` witnesses
example : IsVertexCover asymGraph ⟨{0}, {0}⟩ := by decide
example : ¬ IsVertexCover asymGraph ⟨{1, 2}, ∅⟩ := by decide

-- Universe-polymorphic `Type 1` check for Ford–Fulkerson and König's Theorem
theorem ulift_maxFlow_minCut :
    let N : Network (ULift.{1} (Fin 4)) :=
      unitDiamondNet.reindex Equiv.ulift.symm
    ∃ (f : N.Flow) (S : Finset (ULift.{1} (Fin 4))),
      f.IsMaxFlow ∧ N.IsMinCut S ∧ f.value = (N.cutCapacity S : ℤ) :=
  Network.exists_maxFlow_eq_minCut _ (by simp [Network.reindex, unitDiamondNet])

theorem ulift_koenig :
    let G : ULift.{1} (Fin 3) × ULift.{1} (Fin 4) → Bool := fun p => asymGraph (p.1.down, p.2.down)
    ∃ (M : Finset (ULift.{1} (Fin 3) × ULift.{1} (Fin 4)))
      (C : VertexCover (ULift.{1} (Fin 3)) (ULift.{1} (Fin 4))),
      IsMaxMatching G M ∧ IsMinVertexCover G C ∧ M.card = C.size :=
  exists_maxMatching_eq_minVertexCover _

end ComplexityTests.MaxFlow
