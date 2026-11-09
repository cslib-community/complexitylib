/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.WordRAM.Admission

/-!
# Scalar admission endpoints

The ceiling logarithm admits values strictly below its envelope, while admitting the envelope
itself needs a spare bit. Native execution distinguishes these endpoints. Width zero still
admits word zero, so neither sufficient admission rule is claimed to be necessary.
-/

namespace CslibFrontierTests.WordRAMAdmission

open Cslib.WordRAM

-- A nonempty key domain fits exactly at its existing ceiling-logarithm width.
example (key : Fin 8) : Fits 3 key.val :=
  fits_of_lt_clog_le key.isLt (by decide)

example : Fits 3 7 := fits_of_lt_clog_le (B := 8) (by decide) (by decide)
example : Fits 4 8 := fits_of_clog_lt (by decide)

-- The non-strict logarithmic bound cannot admit the envelope's positive endpoint.
example : Nat.clog 2 8 = 3 ∧ ¬Fits 3 8 := by decide

-- The distinction matters to actual native execution, including its charged halt.
example :
    run (B := .standard) 3 [.op (.const (0 : Fin 1) 7), .halt 0] 2 (.init []) = some (7, 2) ∧
      run (B := .standard) 3 [.op (.const (0 : Fin 1) 8), .halt 0] 2 (.init []) = none ∧
      run (B := .standard) 4 [.op (.const (0 : Fin 1) 8), .halt 0] 2 (.init []) = some (8, 2) :=
  by decide

-- Zero-width and zero-envelope controls prevent accidental positivity hypotheses.
example : Fits 0 0 := fits_zero _
example : ¬Fits 0 1 := by decide
example : Nat.clog 2 0 = 0 ∧ Fits 1 0 := ⟨by decide, fits_of_clog_lt (by decide)⟩
example : Fits 0 0 ∧ ¬Nat.clog 2 0 < 0 := ⟨fits_zero _, by decide⟩

end CslibFrontierTests.WordRAMAdmission
