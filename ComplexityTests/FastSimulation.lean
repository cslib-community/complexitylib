/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.FastSimulation
import Complexity.Computability.Complexity.Classes.Constructible.Log

/-! # Nondeterministic and probabilistic time in time `2 ^ O(T / √log T)`: checked instances

The class containments at the clock `T n = (n + 1) ^ 2 + 1`, which is time-constructible and at
least `max n 2`. -/

namespace ComplexityTests.FastSimulation

open Cslib.Complexity Cslib.Complexity.CountingSimulation Turing.MultiTapeTM

/-- The clock `(n + 1) ^ 2 + 1` is time-constructible. -/
theorem timeConstructible_succ_sq_add_one : TimeConstructible fun n => (n + 1) ^ 2 + 1 :=
  timeConstructible_succ_sq.comp_of_computableInPolyTime (g := fun m => m + 1)
    (ComputableInPolyTime.binary_add.comp
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 1)))
    fun _ => Nat.le_succ _

/-- The clock `(n + 1) ^ 2 + 1` is at least `max n 2`. -/
theorem max_le_succ_sq_add_one (n : ℕ) : max n 2 ≤ (n + 1) ^ 2 + 1 :=
  max_le (by nlinarith) (by have := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n); omega)

example {α : Type} {enc : α ↪ List Bool} :
    NTIME enc (fun n => (n + 1) ^ 2 + 1) ⊆ ⋃ C, DTIME enc fun n =>
      2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  NTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

example {α : Type} {enc : α ↪ List Bool} :
    BPTIME enc (fun n => (n + 1) ^ 2 + 1) ⊆ ⋃ C, DTIME enc fun n =>
      2 ^ (C * ((n + 1) ^ 2 + 1) / Nat.sqrt (Nat.log 2 ((n + 1) ^ 2 + 1))) :=
  BPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two timeConstructible_succ_sq_add_one
    max_le_succ_sq_add_one

-- One machine within both bounds, for strict-majority time.
example {α : Type} {enc : α ↪ List Bool} {L : Set α}
    (hL : L ∈ PPTIME enc fun n => (n + 1) ^ 2 + 1) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * (((enc a).length + 1) ^ 2 + 1) /
        Nat.sqrt (Nat.log 2 (((enc a).length + 1) ^ 2 + 1))))
      (fun a => (((enc a).length + 1) ^ 2 + 1) ^ d) :=
  exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_PPTIME
    timeConstructible_succ_sq_add_one max_le_succ_sq_add_one hL

end ComplexityTests.FastSimulation
