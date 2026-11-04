/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
import Complexity.Computability.Complexity.Classes.Space.Basic

/-! Checks for the conditional containments of the counting simulation (#1833).

The hypothesis `NetworkFamilies` asks for a network family for the accept count of every
finite-state fair-coin machine, with polynomial-time networks. The block-counting construction
discharges it for explicit networks. The generic tests retain the two-interface API, while the
explicit-network tests need only the contraction algorithm. `NetworkFamily` is instantiated in
`ComplexityTests/CountingSimulation.lean`.

Here the containments use a concrete time-constructible bound, discharging `max n 2 ≤ T n`, and
combine with `BPTIME ⊆ PPTIME`. The explicit-network tests keep the simultaneous time/space
certificate and extract membership in `DSPACE` from the same machine. -/

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

/-! ### Explicit block networks: only the contraction hypothesis remains -/

open Cslib.Circuits.Frontier.ExplicitTensorNetwork

/-- The `NTIME` client uses the concrete block networks, simplifies the logarithm of the
clock, and keeps the space bound when passing to `DSPACE`. -/
example (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
    ExplicitAdmissible) {L : Set α} (hL : L ∈ NTIME enc fun n => 2 ^ 2 ^ n) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * 2 ^ 2 ^ (enc a).length / Nat.sqrt (2 ^ (enc a).length)))
      (fun a => (2 ^ 2 ^ (enc a).length) ^ d) ∧
      L ∈ DSPACE enc (fun n => (2 ^ 2 ^ n) ^ d) := by
  obtain ⟨C, d, h⟩ := exists_decidableInTimeAndSpace_of_mem_NTIME_of_contractionAlgorithm
    A timeConstructible_two_pow_two_pow max_le_two_pow_two_pow hL
  refine ⟨C, d, ?_, 1, 0,
    (fun n => 2 ^ (C * 2 ^ 2 ^ n / Nat.sqrt (Nat.log 2 (2 ^ 2 ^ n)))), ?_⟩
  · simpa only [Nat.log_pow Nat.one_lt_two] using h
  · exact ComputableInTimeAndSpace.mono h (fun _ => le_rfl)
      (fun _ => by rw [Nat.one_mul, Nat.add_zero])

/-- The `BPTIME` client uses the concrete block networks, simplifies the logarithm of the
clock, and keeps the space bound when passing to `DSPACE`. -/
example (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
    ExplicitAdmissible) {L : Set α} (hL : L ∈ BPTIME enc fun n => 2 ^ 2 ^ n) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * 2 ^ 2 ^ (enc a).length / Nat.sqrt (2 ^ (enc a).length)))
      (fun a => (2 ^ 2 ^ (enc a).length) ^ d) ∧
      L ∈ DSPACE enc (fun n => (2 ^ 2 ^ n) ^ d) := by
  obtain ⟨C, d, h⟩ := exists_decidableInTimeAndSpace_of_mem_BPTIME_of_contractionAlgorithm
    A timeConstructible_two_pow_two_pow max_le_two_pow_two_pow hL
  refine ⟨C, d, ?_, 1, 0,
    (fun n => 2 ^ (C * 2 ^ 2 ^ n / Nat.sqrt (Nat.log 2 (2 ^ 2 ^ n)))), ?_⟩
  · simpa only [Nat.log_pow Nat.one_lt_two] using h
  · exact ComputableInTimeAndSpace.mono h (fun _ => le_rfl)
      (fun _ => by rw [Nat.one_mul, Nat.add_zero])

/-- The `PPTIME` client uses the concrete block networks, simplifies the logarithm of the
clock, and keeps the space bound when passing to `DSPACE`. -/
example (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
    ExplicitAdmissible) {L : Set α} (hL : L ∈ PPTIME enc fun n => 2 ^ 2 ^ n) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * 2 ^ 2 ^ (enc a).length / Nat.sqrt (2 ^ (enc a).length)))
      (fun a => (2 ^ 2 ^ (enc a).length) ^ d) ∧
      L ∈ DSPACE enc (fun n => (2 ^ 2 ^ n) ^ d) := by
  obtain ⟨C, d, h⟩ := exists_decidableInTimeAndSpace_of_mem_PPTIME_of_contractionAlgorithm
    A timeConstructible_two_pow_two_pow max_le_two_pow_two_pow hL
  refine ⟨C, d, ?_, 1, 0,
    (fun n => 2 ^ (C * 2 ^ 2 ^ n / Nat.sqrt (Nat.log 2 (2 ^ 2 ^ n)))), ?_⟩
  · simpa only [Nat.log_pow Nat.one_lt_two] using h
  · exact ComputableInTimeAndSpace.mono h (fun _ => le_rfl)
      (fun _ => by rw [Nat.one_mul, Nat.add_zero])

end ComplexityTests.CountingSimulationContainments
