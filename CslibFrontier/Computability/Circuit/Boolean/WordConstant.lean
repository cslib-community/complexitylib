/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.Pi

/-!
# Constant words over the Boolean basis

A word of any width uses two shared constant gates. All output bits select one of those gates;
the circuit ignores its input and includes both gates even at zero output width.

## Main definitions

* `Cslib.Circuits.Boolean.wordConstCircuit`: a word of shared Boolean constants.

## Main results

* `Cslib.Circuits.Boolean.eval_wordConstCircuit`: every input gives the specified word.
* `Cslib.Circuits.Boolean.size_wordConstCircuit`: the exact gate count is two.
* `Cslib.Circuits.Boolean.depth_wordConstCircuit_le`: depth is at most one.

Extracted unchanged from the threshold-circuit construction, preserving its source credit.
-/

public section

namespace Cslib.Circuits.Boolean

variable {n w : ℕ}

/-- Constant `w`-bit word circuit on `n` inputs: computes `false` and `true` once and wires each
output bit `i` to the corresponding constant gate. -/
@[expose] def wordConstCircuit (n : ℕ) (y : BitString w) : Circuit signature n w :=
  (Circuit.wiring signature fun i : Fin w =>
      if y i then Fin.natAdd 1 (0 : Fin 1) else Fin.castAdd 1 (0 : Fin 1)).comp
    ((Circuit.oneGate (Op.const false) Fin.elim0).append
      (Circuit.oneGate (Op.const true) Fin.elim0))

/-- `wordConstCircuit n y` evaluates to the constant bit string `y` on every input. -/
@[simp] theorem eval_wordConstCircuit (y : BitString w) (x : BitString n) :
    (wordConstCircuit n y).eval interpretation x = y := by
  funext i
  rw [wordConstCircuit, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_append,
    Function.comp_apply]
  cases y i <;> rfl

/-- `wordConstCircuit n y` uses `2` gates (one `false` and one `true` constant gate). -/
@[simp] theorem size_wordConstCircuit (n : ℕ) (y : BitString w) :
    (wordConstCircuit n y).size = 2 :=
  rfl

/-- `wordConstCircuit n y` has depth at most `1`. -/
theorem depth_wordConstCircuit_le (n : ℕ) (y : BitString w) :
    (wordConstCircuit n y).depth ≤ 1 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, zero_add]
  exact (Circuit.depth_append_le _ _).trans (by simp)

end Cslib.Circuits.Boolean
