/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.Containments

/-! Checks for the conditional containments of the counting simulation (#1833).

The hypothesis `NetworkFamilies` asks for a network family for the accept count of every
finite-state fair-coin machine, with polynomial-time networks. It has no toy instance, since a
polynomial-time family with trivial networks would count accepting choice strings in polynomial
time; it is the obligation of the block-counting step. The structure `NetworkFamily` itself is
instantiated in `ComplexityTests/CountingSimulation.lean`. Here the containments are applied to a
concrete time-constructible bound, discharging `max n 2 ≤ T n`, and combined with the existing
inclusion `BPTIME ⊆ PPTIME`. -/

namespace ComplexityTests.CountingSimulationContainments

open Turing.MultiTapeTM Cslib.Complexity Cslib.Complexity.CountingSimulation

variable {N : Type} {encN : N ↪ List Bool} {value : N → ℕ} {Admissible : ℕ → ℕ → N → Prop}
  {α : Type} {enc : α ↪ List Bool}

private theorem max_le_two_pow_two_pow (n : ℕ) : max n 2 ≤ 2 ^ 2 ^ n :=
  max_le (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num)
    Nat.lt_two_pow_self.le))
    (calc 2 = 2 ^ 2 ^ 0 := by norm_num
      _ ≤ 2 ^ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.zero_le n)))

/-- With `T n = 2 ^ 2 ^ n`, nondeterministic time is in `DTIME (2 ^ (C * 2 ^ 2 ^ n / 2 ^ (n / 2)))`
for some `C`, under the interfaces: `√⌊log₂ (2 ^ 2 ^ n)⌋ = √(2 ^ n)`. -/
example (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) :
    NTIME enc (fun n => 2 ^ 2 ^ n) ⊆
      ⋃ C, DTIME enc fun n => 2 ^ (C * 2 ^ 2 ^ n / Nat.sqrt (2 ^ n)) := by
  intro L hL
  simpa only [Nat.log_pow (Nat.one_lt_two)] using
    NTIME_subset_iUnion_DTIME hnet A timeConstructible_two_pow_two_pow max_le_two_pow_two_pow hL

/-- Bounded-error time reaches the same bound through `PPTIME`, as well as directly. -/
example (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) {L : Set α}
    (hL : L ∈ BPTIME enc fun n => 2 ^ 2 ^ n) :
    L ∈ ⋃ C, DTIME enc fun n => 2 ^ (C * 2 ^ 2 ^ n / Nat.sqrt (Nat.log 2 (2 ^ 2 ^ n))) :=
  PPTIME_subset_iUnion_DTIME hnet A timeConstructible_two_pow_two_pow max_le_two_pow_two_pow
    (BPTIME_subset_PPTIME hL)

/-- The strong form keeps the polynomial space bound alongside the time bound. -/
example (hnet : NetworkFamilies encN value Admissible)
    (A : ContractionAlgorithm encN value Admissible) {L : Set α}
    (hL : L ∈ PPTIME enc fun n => 2 ^ 2 ^ n) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * 2 ^ 2 ^ (enc a).length / Nat.sqrt (2 ^ (enc a).length)))
      (fun a => (2 ^ 2 ^ (enc a).length) ^ d) := by
  simpa only [Nat.log_pow Nat.one_lt_two] using exists_decidableInTimeAndSpace_of_mem_PPTIME
    hnet A timeConstructible_two_pow_two_pow max_le_two_pow_two_pow hL

end ComplexityTests.CountingSimulationContainments
