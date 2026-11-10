/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# The round count of the sparsification searches

The decision and counting sparsification searches (`Cslib.Complexity.Sparsify.search`,
`Cslib.Complexity.CountingSparsify.search`) both run for `2 ^ (n / M + 2)` rounds on formulas
with `n` variables. This module holds that round count and the facts about it that the running-time
analyses of both searches use: it is within `5 * 2 ^ (n / M)` rounds counting the last one, its
binary encoding has `n / M + 3` digits, and it is computable in polynomial time.

## Main definitions

* `Cslib.Complexity.Sparsify.rounds`: the number of rounds of the sparsification searches.

## Main results

* `Cslib.Complexity.Sparsify.rounds_add_one_le`: the number of rounds is `O(2 ^ (n / M))`.
* `Cslib.Complexity.Sparsify.length_encNat_rounds`: the length of the binary round counter.
* `Cslib.Complexity.Sparsify.computableInPolyTime_rounds`: the round count is polynomial-time.
-/

public section

namespace Cslib.Complexity.Sparsify

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The number of rounds of the sparsification searches, `2 ^ (n / M + 2)` on formulas with `n`
variables. -/
@[expose] def rounds (M : ℕ) (φ : CNF ℕ) : ℕ := 2 ^ (φ.distinctVars.length / M + 2)

/-- Counting the final round, the searches run for at most `5 * 2 ^ (n / M)` rounds. -/
theorem rounds_add_one_le (M : ℕ) (φ : CNF ℕ) : rounds M φ + 1 ≤ 5 * 2 ^ (φ.numVars / M) := by
  have h : rounds M φ = 4 * 2 ^ (φ.numVars / M) := by
    rw [rounds, CNF.length_distinctVars, pow_add]
    ring
  have : 1 ≤ 2 ^ (φ.numVars / M) := Nat.one_le_two_pow
  omega

/-- The binary round counter has `n / M + 3` digits. -/
theorem length_encNat_rounds (M : ℕ) (φ : CNF ℕ) :
    (encNat (rounds M φ)).length = φ.numVars / M + 3 := by
  rw [rounds, CNF.length_distinctVars, encNat_two_pow, List.length_append,
    List.length_replicate, List.length_singleton]

/-- The round count is computable in polynomial time. -/
theorem computableInPolyTime_rounds (M : ℕ) :
    ComputableInPolyTime (rounds M) encCNF encNat := by
  have hvars := SAT.computableInPolyTime_distinctVars
  have h := ComputableInPolyTime.unary_div_const M
  unfold rounds
  fun_prop

end Cslib.Complexity.Sparsify
