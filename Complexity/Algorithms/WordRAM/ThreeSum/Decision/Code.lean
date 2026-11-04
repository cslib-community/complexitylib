/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Program

/-!
# Executable ordinary-host syntax from concrete callee code

The host's syntax depends only on the finite callee code. Building that syntax directly
lets clients evaluate it when the callee's separate proof-only time bound is noncomputable.
The equality theorem identifies this exact syntax with the existing certified host assembly.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- Build the actual ordinary host without depending on its callee's resource metadata. -/
@[expose] def programOfCode {r : ℕ} (κ : ℕ) (solver : Code .standard (r + 7)) :
    Code .standard (registerCount r) :=
  let body : Code .standard (registerCount r) :=
    .seq (.seq (loadSource.rename (controllerRegisters r)) callSetup)
      (.seq ((Host.bodyAt solver).rename (hostRegisters r)) finish)
  let calls := .loop (.lt (controllerRegisters r current) (controllerRegisters r count)) body
  let large := .seq ((ChanHe.Preprocessing.program κ).rename (preprocessingRegisters r))
    (.seq (.seq (setup κ) (.seq (power.rename (controllerRegisters r))
      (reserve.rename (controllerRegisters r)))) calls)
  .seq (readLength.rename (controllerRegisters r))
    (.branch (.lt (controllerRegisters r inputLength) (controllerRegisters r three))
      (.op (.copy (controllerRegisters r answer) (controllerRegisters r answer))) large)

/-- Code-only construction preserves the existing complete certified host instruction graph. -/
theorem programOfCode_eq_program {r : ℕ} (κ : ℕ) (c : Host.Callee r) :
    programOfCode κ c.code = program κ c := rfl

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
