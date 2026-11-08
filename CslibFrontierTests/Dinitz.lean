/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.Dinitz

/-!
# Dinitz's Algorithm Tests

Kernel-checked examples (without `native_decide`) for level networks, blocking flows and
`dinitz`:

1. **CLRS 6-vertex network (as in `CslibFrontierTests.MaxFlow`; compare [CLRS2009], Figure 26.1):**
   breadth-first distances `[0, 1, 1, 2, 2, 3]` of the zero flow; dense and sparse `dinitz` both
   find a maximum flow of value `23` with minimum cut `{0, 1, 2, 4}` in `2` phases and `3`
   bottleneck pushes.
2. **Tight phase count:** a 4-vertex network on which `dinitz` needs `3 = |V| - 1` phases, so the
   bound `Network.IsDinitzRun.length_le` is attained.
3. **Reverse-flow cancellation:** an 8-vertex network on which the second phase cancels the first
   phase's flow on an arc.
4. **Blocking flows:** a unit-capacity network with a blocking flow that is not maximum, a
   non-blocking flow of the same network, and the level network dropping an arc inside a layer.
5. **Edge cases:** `N.s = N.t` (no phases, zero flow) and an unreachable sink (no phases, cut of the
   reachable vertices).
-/

public section

namespace ComplexityTests.Dinitz

open Cslib.Algorithms.Lean.MaxFlow
/-! ### CLRS network -/

/-- The CLRS 6-vertex network of `CslibFrontierTests.MaxFlow`, with antiparallel arcs `(1, 2)` and
`(2, 1)`. -/
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

example : (List.finRange 6).map (Network.Flow.zero clrsNet).bfsDist = [0, 1, 1, 2, 2, 3] := by
  decide

example : (dinitzDense clrsNet).flow.value = 23 := by decide

example : (dinitzDense clrsNet).cut = ({0, 1, 2, 4} : Finset (Fin 6)) := by decide

example : (dinitzDense clrsNet).phases = 2 := by decide

example : (dinitzDense clrsNet).augmentations = 3 := by decide

example : (dinitz clrsNet clrsAdj).flow.value = 23 := by decide

example : (dinitz clrsNet clrsAdj).phases = 2 := by decide

example :
    (dinitz clrsNet clrsAdj).flow.IsMaxFlow ∧
      clrsNet.IsMinCut (dinitz clrsNet clrsAdj).cut := by
  obtain ⟨hmax, hmin, _⟩ := dinitz_correct clrsAdj_valid (by decide)
  exact ⟨hmax, hmin⟩

/-- The phases of `dinitz` on the CLRS network form a run of two Dinitz phases from the zero
flow. -/
example : ∃ flows : ℕ → clrsNet.Flow, clrsNet.IsDinitzRun 2 flows ∧
    flows 0 = Network.Flow.zero clrsNet := by
  obtain ⟨flows, hrun, h0, _⟩ := dinitz_isDinitzRun clrsAdj_valid
  have hph : (dinitz clrsNet clrsAdj).phases = 2 := by decide
  rw [hph] at hrun
  exact ⟨flows, hrun, h0⟩

/-! ### A network attaining the phase bound -/

/-- Arcs `0 → 3`, `0 → 1` (capacity `2`), `1 → 3`, `1 → 2`, `2 → 3` (capacity `1`): the three
phases augment along paths of lengths `1`, `2` and `3`. -/
def tightNet : Network (Fin 4) where
  cap u v :=
    match u.1, v.1 with
    | 0, 3 => 1
    | 0, 1 => 2
    | 1, 3 => 1
    | 1, 2 => 1
    | 2, 3 => 1
    | _, _ => 0
  s := 0
  t := 3

example : (dinitzDense tightNet).phases = 3 := by decide

example : (dinitzDense tightNet).flow.value = 3 := by decide

example : (dinitzDense tightNet).phases = Fintype.card (Fin 4) - 1 := by decide

/-! ### Reverse-flow cancellation -/

/-- Unit arcs in which the second phase must cancel the first phase's flow on `1 → 3` through
its reverse residual arc. -/
def revNet : Network (Fin 8) where
  cap u v :=
    match u.1, v.1 with
    | 0, 1 => 1
    | 0, 2 => 1
    | 1, 3 => 1
    | 1, 4 => 1
    | 3, 7 => 1
    | 4, 6 => 1
    | 6, 7 => 1
    | 2, 5 => 1
    | 5, 3 => 1
    | _, _ => 0
  s := 0
  t := 7

example : (dinitzDense revNet).flow.value = 2 ∧ (dinitzDense revNet).phases = 2 ∧
    (dinitzDense revNet).flow 1 3 = 0 := by
  decide

/-! ### Blocking flows -/

/-- Unit arcs `0 → 1`, `0 → 2`, `1 → 2`, `1 → 3`, `2 → 3`, with `s = 0` and `t = 3`. -/
def unitNet : Network (Fin 4) where
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

/-- The flow along the path `0 → 1 → 2 → 3`. -/
def zigFlow : unitNet.Flow where
  toFun u v :=
    match u.1, v.1 with
    | 0, 1 => 1
    | 1, 2 => 1
    | 2, 3 => 1
    | _, _ => 0
  le_cap := by decide
  conserve := by decide

/-- `zigFlow` saturates `0 → 1` and `2 → 3`, so it is blocking, though it has value `1` and the
maximum flow value is `2`. -/
example : zigFlow.IsBlocking ∧ zigFlow.value = 1 ∧ (dinitzDense unitNet).flow.value = 2 := by
  decide

/-- The zero flow is not blocking. -/
example : ¬ (Network.Flow.zero unitNet).IsBlocking := by decide

/-- In the level network of the zero flow the arc `1 → 2` inside the second layer is dropped. -/
example : ((Network.Flow.zero unitNet).levelNet (Network.Flow.zero unitNet).bfsDist).cap 1 2 = 0 ∧
    ((Network.Flow.zero unitNet).levelNet (Network.Flow.zero unitNet).bfsDist).cap 1 3 = 1 := by
  decide

/-! ### Edge cases -/

/-- A network with `s = t`. -/
def loopNet : Network (Fin 2) where
  cap _ _ := 1
  s := 0
  t := 0

example : (dinitzDense loopNet).phases = 0 ∧ (dinitzDense loopNet).flow.value = 0 := by decide

/-- A network whose sink is unreachable. -/
def cutOffNet : Network (Fin 3) where
  cap u v := if u.1 = 0 ∧ v.1 = 1 then 5 else 0
  s := 0
  t := 2

example : (dinitzDense cutOffNet).phases = 0 ∧ (dinitzDense cutOffNet).flow.value = 0 ∧
    (dinitzDense cutOffNet).cut = ({0, 1} : Finset (Fin 3)) := by
  decide

end ComplexityTests.Dinitz
