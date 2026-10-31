/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AcceptCount
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic

/-!
# Accepting choice strings of a fair-coin table

A closed fair-coin table `Turing.MultiTapePTM k Bool State` is the binary-choice normal form of a
machine: a run is a deterministic replay of a list of choice bits, one bit per live step. When
both branches of an instruction agree, its bit is ignored, and a halted configuration ignores all
further bits (`Turing.MultiTapePTM.stepCoins`). So every run on `τ` bits is padded to exactly `τ`
steps. A nondeterministic machine with finitely many states and a binary alphabet is put in this
form by its choice table `Turing.MultiTapeNTM.choiceTable`, which encodes each choice in binary and
rejects at a stuck configuration.

The *accepting count* `Turing.MultiTapePTM.acceptCount machine input τ` is the number of bit
strings `y ∈ {0,1}^τ` on which the table emits `[true]` on `input`: the count `A_M(x)` of the
counting simulations of nondeterministic and probabilistic time. It is the generic count
`Cslib.Complexity.acceptCount` of the replay predicate, so the elementary lemmas about that count
(`Cslib.Complexity.acceptCount_le_two_pow`, `Cslib.Complexity.acceptCount_pos_iff`, …) apply
to it directly. Its fraction of all `2 ^ τ`
strings is exactly the probability that the closed fair-coin run outputs `[true]`
(`Turing.MultiTapePTM.eval_runClosed_apply_eq_acceptCount`). The membership characterizations
for nondeterministic and bounded-error deciders are in
`Complexity.Computability.Complexity.Classes.Time.AcceptCount`.

## Main definitions

* `Turing.MultiTapePTM.acceptCount`: the number of accepting choice strings of a given length.

## Main results

* `Turing.MultiTapePTM.eval_runClosed_apply_eq_acceptCount`: the probability of output `[true]`
  is the accepting count divided by `2 ^ τ`.
* `Turing.MultiTapePTM.half_lt_eval_runClosed_apply_iff`: strict majority acceptance, as an
  integer comparison `2 ^ τ < 2 * acceptCount`.
* `Turing.MultiTapePTM.runClosedCoins_eq_output_stepCoins`: the replay on upstream
  configurations.
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability
open scoped ENNReal

variable {k : ℕ} {State : Type} (machine : MultiTapePTM k Bool State) (input : List Bool)
  (τ : ℕ)

/-- **The accepting count** `A_M(x)`: the number of choice strings `y ∈ {0,1}^τ` replaying
which the closed fair-coin table emits `[true]` on `input`. -/
abbrev acceptCount : ℕ :=
  Complexity.acceptCount
    (fun p : List Bool × List Bool => decide (machine.runClosedCoins p.2 p.1 = [true])) input τ

/-- **Acceptance probability is the accepting fraction.** The closed fair-coin run with clock
`τ` outputs `[true]` with probability `acceptCount / 2 ^ τ`. -/
theorem eval_runClosed_apply_eq_acceptCount :
    ProbComp.eval (machine.runClosed τ input) [true] =
      (machine.acceptCount input τ : ℝ≥0∞) / 2 ^ τ := by
  rw [eval_runClosed_eq_map_coins, BitString.uniformList_map_apply]
  simp only [Complexity.acceptCount, decide_eq_true_eq]

/-- **Strict majority acceptance** is the integer comparison `2 ^ τ < 2 * acceptCount`. -/
theorem half_lt_eval_runClosed_apply_iff :
    2⁻¹ < ProbComp.eval (machine.runClosed τ input) [true] ↔
      2 ^ τ < 2 * machine.acceptCount input τ := by
  rw [eval_runClosed_apply_eq_acceptCount, ENNReal.lt_div_iff_mul_lt (by simp) (by simp),
    ← ENNReal.div_eq_inv_mul, ENNReal.div_lt_iff (by simp) (by simp), mul_comm]
  exact_mod_cast Iff.rfl

/-- The replay on the configurations of the shared interpreter is the replay on upstream
configurations, by deterministic steps under each coin. -/
theorem runClosedCoins_eq_output_stepCoins (coins : List Bool) :
    machine.runClosedCoins coins input =
      (machine.stepCoins coins (Cfg.init machine.initial input)).output := by
  rw [runClosedCoins, tapes_runClosedConfigFromCoins]
  rfl

end Turing.MultiTapePTM
