/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Program
public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Data

/-!
# Stack representation for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.encode`: represent a raw configuration at a source-step boundary.
-/

public section

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Finite control corresponding to raw simulation data, with arbitrary scratch registers. -/
@[expose] def control (d : Data k State) (symbol : Option Bool := none) (busy : Bool := false) :
    Control k State := ⟨d.state, d.input.atLeft, fun i => (d.work i).head, symbol, busy⟩

/-- The stack representation keeps output in reverse order until cleanup. -/
@[expose] def store (d : Data k State) : (s : Stack k) → List (Alphabet s)
  | .input => d.input.right
  | .before => d.input.left
  | .output => []
  | .reversed => d.output.reverse
  | .work i false => (d.work i).left
  | .work i true => (d.work i).right

/-- The TM2 configuration at a source-step boundary. -/
@[expose] def encode (d : Data k State) : TM2.Cfg (Alphabet (k := k)) Label (Control k State) :=
  ⟨some .run, control d, store d⟩

end

end Turing.MultiTapeTM.ToTM2
