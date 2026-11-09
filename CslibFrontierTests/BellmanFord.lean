/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.BellmanFord.Basic
public import Mathlib.Algebra.Order.Group.Int

/-!
# The Bellman–Ford algorithm: worked examples

Kernel-checked examples (no `native_decide`): a negative edge with no negative cycle (correct
distances, `⊤` for an unreachable vertex), a reachable negative cycle (`none`), a negative cycle
that is not reachable from the source (distances still returned), and exact tick counts.
-/

public section

namespace CslibFrontierTests.BellmanFord

open Cslib.Algorithms.Lean.BellmanFord

/-! ### A negative edge, no negative cycle -/

/-- `0 → 1` (weight `4`), `0 → 2` (`5`), `2 → 1` (`-3`); vertex `3` is unreachable. -/
def g : Fin 4 → List (Fin 4 × ℤ)
  | 0 => [(1, 4), (2, 5)]
  | 2 => [(1, -3)]
  | _ => []

example : (bellmanFord g (List.finRange 4) 0).map (fun d => (d 0, d 1, d 2, d 3)) =
    some (0, 2, 5, ⊤) := by decide +kernel

/-- The shortest walk to `1` goes through `2` and has weight `2`. -/
example : IsShortestDist g 0 1 2 := by
  obtain ⟨d, hd⟩ : ∃ d, bellmanFord g (List.finRange 4) 0 = some d ∧ d 1 = 2 :=
    ⟨_, rfl, by decide +kernel⟩
  exact hd.2 ▸ isShortestDist_of_bellmanFord_eq_some List.mem_finRange hd.1 1

/-- No walk reaches `3`. -/
example : IsShortestDist g 0 3 ⊤ := by
  obtain ⟨d, hd⟩ : ∃ d, bellmanFord g (List.finRange 4) 0 = some d ∧ d 3 = ⊤ :=
    ⟨_, rfl, by decide +kernel⟩
  exact hd.2 ▸ isShortestDist_of_bellmanFord_eq_some List.mem_finRange hd.1 3

example : ¬ NegCycleReachable g 0 := fun h =>
  absurd ((bellmanFord_eq_none_iff List.mem_finRange).2 h) (by decide +kernel)

/-- Four vertices and three edges: `4 + 4 (4 + 3) = 32` ticks. -/
example : (bellmanFordM g (List.finRange 4) 0).time = 32 := by
  rw [time_bellmanFordM]
  decide

example : (bellmanFordM g (List.finRange 4) 0).time = 32 := by decide +kernel

example : (bellmanFordM g (List.finRange 4) 0).time = 4 + 4 * (4 + ∑ v, (g v).length) :=
  time_bellmanFordM_of_nodup List.mem_finRange (List.nodup_finRange 4) g 0

/-! ### Negative cycles -/

/-- `0 → 1` (`1`), `1 → 2` (`-2`), `2 → 1` (`1`): the cycle `1 → 2 → 1` has weight `-1`. -/
def h : Fin 3 → List (Fin 3 × ℤ)
  | 0 => [(1, 1)]
  | 1 => [(2, -2)]
  | 2 => [(1, 1)]

example : bellmanFord h (List.finRange 3) 0 = none := by decide +kernel

example : NegCycleReachable h 0 :=
  (bellmanFord_eq_none_iff List.mem_finRange).1 (by decide +kernel)

/-- The same negative cycle, now unreachable from `0`: `0` has no outgoing edge, and its only edge
comes from the cycle. -/
def h' : Fin 3 → List (Fin 3 × ℤ)
  | 1 => [(2, -2), (0, 0)]
  | 2 => [(1, 1)]
  | _ => []

example : (bellmanFord h' (List.finRange 3) 0).map (fun d => (d 0, d 1, d 2)) =
    some (0, ⊤, ⊤) := by decide +kernel

example : ¬ NegCycleReachable h' 0 := fun hn =>
  absurd ((bellmanFord_eq_none_iff List.mem_finRange).2 hn) (by decide +kernel)

/-- A negative self-loop at the source. -/
example : NegCycleReachable (fun _ : Fin 1 => [((0 : Fin 1), (-1 : ℤ))]) 0 :=
  (bellmanFord_eq_none_iff List.mem_finRange).1 (by decide +kernel)

end CslibFrontierTests.BellmanFord
