/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingProgram
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalCost

/-!
# Concrete global layout of native Chan–He preprocessing

The prime bitmap follows the frontend. A seven-word-per-entry stack and a pointer table precede
all heavy and packed arrays. Reservations use the actual input length and actual computed fuel.

## Main definitions

* `arena`: complete finite memory layout, including every root's allocation reservation.

## Main results

* `arena_separated`: concrete stack, bitmap, table and heap reservations are disjoint.

The layout and resource estimates are original. They do not change the existing finite instances.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- All memory regions computed by the actual native forest controller. -/
def arena (κ n : ℕ) (retained : ℕ → ℕ) : Traversal.Arena :=
  let l := Frontend.layout κ n
  let U := (n + 2) ^ κ
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  let N := 2 * m ^ 2
  let stack := l.endpoint + m + 1
  let cap := 7 * (2 * F + 1)
  let table := stack + cap
  let outcap := l.count * 3 ^ (F + 1)
  let floor := table + outcap
  { n := n + 1, m := m, Λ := l.digits, U := 2 * U, N := N, fuel := F,
    primes := l.endpoint, stack := stack, capacity := cap, table := table,
    outputCapacity := outcap, floor := floor,
    ceiling := floor + l.count *
      (Traversal.Math.work F * Traversal.allocationSize (n + 1) m N),
    retained := retained }

/-- The actual reservations put the bitmap, bounded stack, pointer table and arrays in order. -/
theorem arena_separated (κ n : ℕ) (retained : ℕ → ℕ) : (arena κ n retained).Separated := by
  constructor
  · dsimp only [arena]
    omega
  · exact ⟨le_rfl, le_rfl, le_rfl⟩

/-- Every actual frontend payload precedes the reserved shared stack. -/
theorem arena_frontend_before (κ n : ℕ) (retained : ℕ → ℕ) :
    (Frontend.layout κ n).endpoint ≤ (arena κ n retained).stack := by
  dsimp only [arena]
  omega

/-- Full ternary work never exceeds the native controller's computed power reservation. -/
theorem work_le_power (f : ℕ) : Traversal.Math.work f ≤ 3 ^ (f + 1) := by
  have := Traversal.Math.work_eq f
  omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
