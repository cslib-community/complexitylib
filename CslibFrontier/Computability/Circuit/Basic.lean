/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Basic

/-!
# Evaluating a designated circuit output

## Main results

* `Cslib.Circuits.Circuit.eval_of_output_eq_gate`: an output selecting a gate reads that gate's
  value in the program evaluation.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u} {n m : ℕ}

/-- A designated gate output reads its value from the program evaluation. -/
theorem Circuit.eval_of_output_eq_gate {c : Circuit σ n m} {j : Fin m} {gate : Fin c.size}
    (h : c.outputs j = .gate gate) (I : Interpretation σ U) (x : Fin n → U) :
    c.eval I x j = c.program.eval I x gate := by
  simp only [Circuit.eval, Function.comp_apply, h, Program.trace, Wire.elim_gate]

end Cslib.Circuits
