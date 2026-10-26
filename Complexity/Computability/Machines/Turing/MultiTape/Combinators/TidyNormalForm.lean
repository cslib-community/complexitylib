/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- upstream: candidate (coordinate with crei on #611)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ClearShadowed
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
public import Cslib.Foundations.Data.Fin.Tuple
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Embedding
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The tidy normal form

Every computation can be made tidy (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) at a
linear cost in time and space: `tidy m₀ m₁ tm` runs `tm` with every work tape shadowed
(`Turing.MultiTapeTM.shadow`), then clears each work tape along its shadow
(`Turing.MultiTapeTM.clearShadowed`), and finally rewinds the input head
(`Turing.MultiTapeTM.rewindInput`); the symbols `m₀ ≠ m₁` mark the shadows. A computation of `tm`
within `t` steps and `s` cells becomes a tidy computation of `tidy m₀ m₁ tm` within
`2 t + 3 s + 2 k + 4` steps (`ComputesInTimeAndSpace.computesTidily_tidy`). So tidiness, which
makes machines composable, is no restriction on what is computable within given resources up to
constant factors (`ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`).

The shadow tapes are needed because a work tape may hold blanks among the cells `tm` has written:
sweeping until the first blank would not find them all.

## Main definitions

* `Turing.MultiTapeTM.clearList`: clear a list of work tapes along their shadows.
* `Turing.MultiTapeTM.tidy`: the tidy normal form of a machine.

## Main results

* `Turing.MultiTapeTM.exists_runPath_tidy`: the run path of `tidy m₀ m₁ tm` when `tm` halts.
* `Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`: `tidy m₀ m₁ tm` computes
  tidily what `tm` computes.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`: computable
  functions are tidily computable.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- **Computable functions are tidily computable**, at a linear cost: a function computable within
time `t` and space `s` is computable tidily within time `2 t + 3 s + c` and space `c (s + 1)`, for a
constant `c` that depends on the number of work tapes of the machine. -/
theorem ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 3 * s a + c)
      (fun a => c * (s a + 1)) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  refine ⟨4 * k * k + 6 * k + 4, k + k, _, inferInstance, tidy false true tm, fun a =>
    ((htm a).computesTidily_tidy Bool.false_ne_true).mono
      (by beta_reduce; generalize 4 * k * k = m; omega) ?_⟩
  beta_reduce
  have e₁ : 2 * s a + 2 * k * (3 * s a + 2 * k + 3) = (6 * k + 2) * s a + (4 * k * k + 6 * k) := by
    ring
  have e₂ : (4 * k * k + 6 * k + 4) * (s a + 1) =
      (4 * k * k + 6 * k + 4) * s a + (4 * k * k + 6 * k + 4) := by ring
  have : (6 * k + 2) * s a ≤ (4 * k * k + 6 * k + 4) * s a :=
    Nat.mul_le_mul_right _ (by generalize 4 * k * k = m; omega)
  rw [e₁, e₂]
  exact Nat.add_le_add this (by generalize 4 * k * k = m; omega)

end Turing.MultiTapeTM
