/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastSimulation
public import Complexity.Computability.Complexity.Classes.Promise.Time

/-!
# Deterministic promise completions at a prescribed clock

A native bounded-error promise solver running in time `T` has a strict-majority completion in
`PPTIME T`, at the same clock. The unconditional counting simulation then gives one deterministic
machine deciding that completion in time `2 ^ (C T / √⌊log₂ T⌋)` and workspace `T ^ d`.
The caller supplies `T`, its constructibility and `max n 2 ≤ T n`. Only the simulation constants
are existential: the time scale cannot be weakened by choosing a larger polynomial afterward.

Answers outside the promise are unrestricted. This is not a bounded-error total completion.
The verifier-defined `PromiseBPP` completion in `PP` is separately proved in `Promise.PP`;
no clock-preserving equivalence between that verifier definition and `PromiseBPTIME` is asserted.

## Main results

* `exists_completion_of_mem_PromiseBPTIME`: one deterministic completion with the prescribed
  subexponential time and independent polynomial-workspace bounds.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing.MultiTapeTM

/-- A native promise problem at caller-supplied time `T` has a deterministic completion within
`2 ^ O(T / √log T)` time and polynomial workspace, with one realizing machine. -/
theorem exists_completion_of_mem_PromiseBPTIME {α : Type} {enc : α ↪ List Bool}
    {T : ℕ → ℕ} (hT : TimeConstructible T) (hTn : ∀ n, max n 2 ≤ T n)
    {Q : PromiseProblem α} (hQ : Q ∈ PromiseBPTIME enc T) :
    ∃ (L : Set α) (C d : ℕ), Q.yes ⊆ L ∧ Disjoint L Q.no ∧
      DecidableInTimeAndSpace L enc
        (fun a => 2 ^ (C * T (enc a).length / Nat.sqrt (Nat.log 2 (T (enc a).length))))
        (fun a => T (enc a).length ^ d) := by
  obtain ⟨L, hL, hyes, hno⟩ := PromiseBPTIME_subset_promiseClass_PPTIME hQ
  obtain ⟨C, d, h⟩ :=
    exists_decidableInTimeAndSpace_two_pow_div_sqrt_log_two_of_mem_PPTIME hT hTn hL
  exact ⟨L, C, d, hyes, hno, h⟩

end Cslib.Complexity.CountingSimulation
