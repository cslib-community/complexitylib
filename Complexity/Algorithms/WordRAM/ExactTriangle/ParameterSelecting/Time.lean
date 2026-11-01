/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Admission

/-!
# Actual component ledger of the parameter-selecting solver

The fast component retains the proved concrete selector and callable-solver budgets. The
small component is the real exhaustive block with its argument and return copies. The common
budget adds actual saving, parameter execution, dispatch and restoration. No global exponent
or unproved aggregate bound is assumed. The source-reference memory indexes a derived finite
charge; it is not a runtime input or a supplied execution certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.Algorithms.ExactTriangle

/-- Stage charge for the computed regime, including real argument/return delivery. -/
@[expose] noncomputable def stageBudget (n p : ℕ) (values : List ℤ) (mem : ℕ → ℕ) : ℕ :=
  if h : 0 < ParameterChoice.blocks n then
    8 + PrimeSelection.timeBound n (ParameterChoice.window n) + 1 +
      CallableFixedPrime.timeBound (m := ParameterChoice.level n)
        (h.trans_le ((ParameterChoice.blocks_le_log n).trans (Nat.log_le_self 2 n)))
        (ParameterChoice.groups n) p values mem
  else 39 * (n * (n * n)) + 16

/-- Complete structured caller charge before halt: save8, actual parameters, stage,
conservative two-instruction dispatch and restore/return7. -/
@[expose] noncomputable def timeBound (n p : ℕ) (values : List ℤ) (mem : ℕ → ℕ) : ℕ :=
  8 + (DyadicParameters.timeBound n + ((stageBudget n p values mem + 2) + 7))

/-- A common workspace frame containing both real selection and selected-prime solver writes. -/
@[expose] def workspaceEnd (n b : ℕ) (values : List ℤ) : ℕ :=
  max (CountPrime.memoryEnd n (Nat.sqrt (ParameterChoice.window n)) (Nat.clog 2 n) b)
    (b + CallableFixedPrime.windowSize n (ParameterChoice.window n) (ParameterChoice.groups n)
      (Nat.sqrt (ParameterChoice.window n)) (CallableFixedPrime.rawTotal n values))

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
