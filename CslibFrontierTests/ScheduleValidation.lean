/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleValidation

open Turing.MultiTapeTM.ScheduleBits

example : validate 0 [] = true := by decide
example : validate 0 [true, false, false, true] = true := by decide
example : validate 1 [true, false] = false := by decide
example : validate 0 [false] = false := by decide
example : validate 0 [true, true] = false := by decide
-- The two adjacent true bits cross a pair boundary and are valid.
example : validate 1 [false, true, true, false] = true := by decide
example : validate 1 [false, false, true, true] = false := by decide

-- Validity supplies actual input-first rows, not just an abstract predicate.
example : ∃ rs : List (Option (Fin 1) → SignType),
    rows rs = [false, true, true, false] :=
  (validate_eq_true_iff_exists_rows _ _).mp (by decide)
