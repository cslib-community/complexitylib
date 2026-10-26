/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Data.List.Basic

/-! # The first-occurrence index fold

Pure transition and invariant shared by the direct list certificate and its legacy client.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.ListIndex
variable {α : Type*}

/-- Keep the first matching position, incrementing only while no match has appeared. -/
def idxStep [DecidableEq α] (v : α) (s : Bool × ℕ) (a : α) : Bool × ℕ :=
  if s.1 || decide (a = v) then (true, s.2) else (false, s.2 + 1)

/-- The original first-occurrence fold returns the starting count plus the first index. -/
theorem foldl_idxStep [DecidableEq α] (v : α) (l : List α) (s : Bool × ℕ) :
    (l.foldl (idxStep v) s).2 = s.2 + if s.1 then 0 else l.idxOf v := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    rcases s with ⟨b, n⟩
    cases b <;> by_cases ha : a = v <;>
      simp [idxStep, ha, Nat.add_comm, Nat.add_left_comm]

end Turing.MultiTapeTM.Internal.ListIndex
