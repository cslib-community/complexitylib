/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastLeaves

/-!
# Nondeterministic and probabilistic time in time `2 ^ O(T / √log T)` and polynomial space

The class containments of `Cslib.Complexity.CountingSimulation.BlockNetworks`, with the contraction
algorithm of Theorem D.1 of [OpenAI2026ETH] (`CountingSimulation.fastContractionAlgorithm`) in place
of their hypothesis. These are the containments of #1833: for time-constructible `T` with
`max n 2 ≤ T n`, every problem in `NTIME[T]`, `BPTIME[T]` or `PPTIME[T]` is decided by one
deterministic machine in time `2 ^ (C T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`.

## Main results

* `Cslib.Complexity.CountingSimulation.NTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `BPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`,
  `PPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two`: the class containments.
* `exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_NTIME`,
  `exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_BPTIME`,
  `exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_PPTIME`: joint time and space.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {T : ℕ → ℕ}

/-- **Nondeterministic time `T` in time `2 ^ O(T / √log T)` and space `T ^ O(1)`.** -/
theorem exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_NTIME
    (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) {L : Set α} (hL : L ∈ NTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_NTIME_of_contractionAlgorithm fastContractionAlgorithm hT
    hTn hL

/-- **Bounded-error probabilistic time `T` in time `2 ^ O(T / √log T)` and space `T ^ O(1)`.** -/
theorem exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_BPTIME
    (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) {L : Set α} (hL : L ∈ BPTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_BPTIME_of_contractionAlgorithm fastContractionAlgorithm hT
    hTn hL

/-- **Strict-majority probabilistic time `T` in time `2 ^ O(T / √log T)` and space
`T ^ O(1)`.** -/
theorem exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_PPTIME
    (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n) {L : Set α} (hL : L ∈ PPTIME enc T) :
    ∃ C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
      (fun a => T (enc a).length ^ d) :=
  exists_decidableInTimeAndSpace_of_mem_PPTIME_of_contractionAlgorithm fastContractionAlgorithm hT
    hTn hL

/-- **`NTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem NTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    NTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  NTIME_subset_iUnion_DTIME_of_contractionAlgorithm fastContractionAlgorithm hT hTn

/-- **`BPTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem BPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    BPTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  BPTIME_subset_iUnion_DTIME_of_contractionAlgorithm fastContractionAlgorithm hT hTn

/-- **`PPTIME[T] ⊆ ⋃ C, DTIME[2 ^ (C T / √⌊log₂ T⌋)]`** for time-constructible `T` with
`max n 2 ≤ T n`. -/
theorem PPTIME_subset_iUnion_DTIME_two_pow_div_sqrt_log_two (hT : TimeConstructible T)
    (hTn : ∀ n, max n 2 ≤ T n) :
    PPTIME enc T ⊆ ⋃ C, DTIME enc fun n => 2 ^ (C * T n / Nat.sqrt (Nat.log 2 (T n))) :=
  PPTIME_subset_iUnion_DTIME_of_contractionAlgorithm fastContractionAlgorithm hT hTn

end Cslib.Complexity.CountingSimulation
