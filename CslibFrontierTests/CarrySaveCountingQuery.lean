/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Circuit.Boolean.CarrySave.CountingQuery

open Cslib Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery
open CarrySaveQuery.Counting BitString

-- Five predicate bits require eight padded leaves; exactly three bits are true.
private def predicate (j : ℕ) : Bool := decide (j % 2 = 0)

example : (equivFin 3 (count 5 3 predicate) : ℕ) = 3 := by
  rw [val_count]
  decide

-- Insufficient precision wraps around, rather than claiming the exact count.
example : (equivFin 1 (count 5 1 predicate) : ℕ) = 1 := by
  rw [val_count]
  decide

-- Low-bit queries still match the exact integer count when the whole count overflows.
example : count 5 2 (fun _ => true) 0 = true ∧ count 5 2 (fun _ => true) 1 = false := by
  constructor <;> rw [count_apply] <;> decide

example (p : ℕ → Bool) : (equivFin 3 (count 0 3 p) : ℕ) = 0 := by
  rw [val_count]
  simp

-- At a real leaf only the first output bit reads the predicate.
example (p : ℕ → Bool) : component (leafPair 5 3 p 2) false 0 = p 2 := by
  simp [component_leafPair]

example (p : ℕ → Bool) : component (leafPair 5 3 p 7) false 0 = false := by
  simp [component_leafPair]

example (p : ℕ → Bool) : component (leafPair 5 3 p 2) true 0 = false := by
  simp [component_leafPair]

example (p : ℕ → Bool) :
    (equivFin 4 (count 8 4 p) : ℕ) = ∑ j ∈ Finset.range 8, (p j).toNat :=
  val_count_eq 8 4 p (by decide)
