/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import Complexity.Computability.Complexity.Classes.Promise.PP

/-!
# Conditional deterministic completions of PromiseBPP

Every problem in `PromiseBPP` has a strict-majority completion in `PP`. Applying the counting
simulation to that completion gives one total deterministic machine that separates the yes- and
no-instances, with the counting simulation's joint time and workspace bounds. The contraction
algorithm for admissible explicit networks remains an explicit hypothesis.

The polynomial clock is `T n = (n + 1) ^ (k + 2) + 1`, for some `k` depending on the completion.
It is time-constructible and at least `max n 2`, including at `n = 0`. The simulation uses time
`2 ^ (C * T n / √⌊log₂ (T n)⌋)` and workspace `T n ^ d`. Outside the promise, the completion
may answer either way. This does not give a `BPP` completion, a gate-count bound, or a bound
subexponential in input length for every polynomial clock.

These are corollaries of the existing majority and counting interfaces, addressing the promise
extension of #1833. They do not discharge the contraction hypothesis or the unconditional
simulation objective.

## Main results

* `exists_decidableInTimeAndSpace_of_mem_PP_of_contractionAlgorithm`: the joint bounds for a
  problem in `PP`, at a polynomial clock meeting the simulation's hypotheses.
* `exists_completion_of_mem_PromiseBPP_of_contractionAlgorithm`: a deterministic completion of
  a `PromiseBPP` problem with the same joint bounds.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Turing.MultiTapeTM Cslib.Circuits.Frontier.ExplicitTensorNetwork

variable {α : Type} {enc : α ↪ List Bool}

/-- A problem in `PP` is decidable by one machine within the counting simulation's time and
polynomial-workspace bounds, at a polynomial clock, conditional on the contraction algorithm. -/
theorem exists_decidableInTimeAndSpace_of_mem_PP_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) {L : Set α} (hL : L ∈ PP enc) :
    ∃ k C d : ℕ, DecidableInTimeAndSpace L enc
      (fun a => 2 ^ (C * (((enc a).length + 1) ^ (k + 2) + 1) /
        Nat.sqrt (Nat.log 2 (((enc a).length + 1) ^ (k + 2) + 1))))
      (fun a => (((enc a).length + 1) ^ (k + 2) + 1) ^ d) := by
  obtain ⟨k, hk⟩ := mem_PP_iff_exists_mem_PPTIME.mp hL
  have hT := (timeConstructible_succ_pow (k := k + 2) (by omega)).succ
  have hbound (n : ℕ) : max n 2 ≤ (n + 1) ^ (k + 2) + 1 := by
    have := Nat.le_self_pow (by omega : k + 2 ≠ 0) (n + 1)
    omega
  have hclock (n : ℕ) : n ^ k ≤ (n + 1) ^ (k + 2) + 1 :=
    (Nat.pow_le_pow_left (Nat.le_succ n) k).trans
      ((Nat.pow_le_pow_right (by omega) (by omega)).trans (Nat.le_succ _))
  obtain ⟨C, d, h⟩ := exists_decidableInTimeAndSpace_of_mem_PPTIME_of_contractionAlgorithm
    A hT hbound (PPTIME_mono hclock hk)
  exact ⟨k, C, d, h⟩

/-- Every `PromiseBPP` problem has a total deterministic completion with simultaneous time
`2 ^ O(T / √(log T))` and workspace polynomial in the polynomial clock `T`, conditional on the
explicit contraction algorithm. No answer is prescribed outside the promise. -/
theorem exists_completion_of_mem_PromiseBPP_of_contractionAlgorithm
    (A : ContractionAlgorithm (encPair encNat encExplicitNetwork) (fun G => G.2.contraction)
      ExplicitAdmissible) {Q : PromiseProblem α} (hQ : Q ∈ PromiseBPP enc) :
    ∃ (L : Set α) (k C d : ℕ), Q.yes ⊆ L ∧ Disjoint L Q.no ∧
      DecidableInTimeAndSpace L enc
        (fun a => 2 ^ (C * (((enc a).length + 1) ^ (k + 2) + 1) /
          Nat.sqrt (Nat.log 2 (((enc a).length + 1) ^ (k + 2) + 1))))
        (fun a => (((enc a).length + 1) ^ (k + 2) + 1) ^ d) := by
  obtain ⟨L, hL, hyes, hno⟩ := PromiseBPP_subset_promiseClass_PP hQ
  obtain ⟨k, C, d, h⟩ := exists_decidableInTimeAndSpace_of_mem_PP_of_contractionAlgorithm A hL
  exact ⟨L, k, C, d, hyes, hno, h⟩

end Cslib.Complexity.CountingSimulation
