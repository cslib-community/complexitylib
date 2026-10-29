/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Synthesis
import Complexity.Computability.Circuit.Boolean.ShannonSynthesis

/-!
# Finite Shannon synthesis regression clients

Check actual circuit evaluation on small truth tables, empty input blocks, constants,
the finite threshold and the placement of natural division in the replicated bound.
-/

namespace ComplexityTests.ShannonSynthesis

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ShannonSynthesis

-- Actual circuit evaluation on small truth tables, empty input blocks, constants, the finite
-- threshold, and the placement of natural division in the replicated bound.
example (f₁₆ : BooleanFunction 16) (f₁₇ : BooleanFunction 17) (copies : ℕ) :
    ((mintermCircuit 0).eval interpretation ![] 0 = true ∧ (mintermCircuit 0).size = 1 ∧
      (mintermCircuit 2).eval interpretation ![true, false] = ![false, true, false, false] ∧
      (mintermCircuit 2).size = 10) ∧
    ((columnFormula ![false, false, false, false]).size = 1 ∧
      (columnFormula ![true, true, true, true]).size = 3 ∧
      (columnFormula ![false, true, false, true]).eval interpretation
        ![true, false, true, false] = false) ∧
    (∀ (table : BitString 4) (x : BitString 2),
      (circuit (k := 1) (d := 1) (fun a => table (BitString.equivFin 2 a))).eval
        interpretation x 0 = table (BitString.equivFin 2 x)) ∧
    ((∀ x : BitString 1,
        (circuit (k := 0) (d := 1) (fun a => !a 0)).eval interpretation x 0 = !x 0) ∧
      (∀ x : BitString 1,
        (circuit (k := 1) (d := 0) (fun a => !a 0)).eval interpretation x 0 = !x 0) ∧
      (∀ b : Bool,
        (circuit (k := 0) (d := 0) (fun _ => b)).eval interpretation ![] 0 = b) ∧
      (∀ x : BitString 2,
        (synthesize (fun a : BitString 2 => a 0 ^^ a 1)).eval interpretation x 0 =
          (x 0 ^^ x 1))) ∧
    (addressWidth 16 = 3 ∧ dataWidth 16 = 13 ∧ bound 3 13 ≤ 27 * 2 ^ 16 / 16 ∧
      27 * 2 ^ 17 / 17 = 208173 ∧ 27 * (2 ^ 17 / 17) = 208170) ∧
    (∃ c : Circuit signature 16 1,
      c.Computes interpretation (single f₁₆) ∧ c.size ≤ 110592) ∧
    MassProduction.massComplexity f₁₇ copies ≤ (copies * 208173 : ℕ) ∧
    MassProduction.massComplexity f₁₆ 0 ≤ (0 : ℕ) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide,
    exists_circuit (by decide) f₁₆,
    MassProduction.massComplexity_le_shannon (by decide) f₁₇ copies,
    MassProduction.massComplexity_le_shannon (by decide) f₁₆ 0⟩

end ComplexityTests.ShannonSynthesis
