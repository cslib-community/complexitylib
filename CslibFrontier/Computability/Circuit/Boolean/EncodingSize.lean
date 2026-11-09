/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Bounding the complete binary encoding of a circuit

A circuit's typed wires bound every binary reference by its input and gate counts. This gives a
polynomial bound on its complete serialized code, including gate tags, outputs and framing.
It is useful for certifying circuit-construction loops whose intermediate circuits have bounded
size, without making a claim about the complexity of the functions those circuits compute.

## Main results

* `Cslib.Circuits.Boolean.length_encCode_le`: a bound in the input, output and gate counts.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- The full code of a typed De Morgan circuit has polynomially bounded encoded length. -/
theorem length_encCode_le {n m : ℕ} (c : Circuit signature n m) :
    (encCode c.code).length ≤
      2 * c.size * (23 + 8 * (n + c.size)) + 1 + m * (2 * (n + c.size) + 1) := by
  have hgate (line : Line signature n c.size) :
      (encGate line.code).length ≤ 11 + 4 * (n + c.size) := by
    have hop : (encOp line.op).length ≤ 4 := by
      cases line.op with
      | const b => cases b <;> decide
      | _ => decide
    have hargs : (encList encNat line.code.2).length ≤ 2 * (2 * (n + c.size) + 1) := by
      have h := length_encList_le encNat line.code.2 (b := n + c.size) (fun i hi => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
        exact (length_encNat_le_self _).trans (Wire.toNat_lt (line.wires j)).le)
      have ha : line.code.2.length ≤ 2 := by grind [Line.length_code_snd]
      exact h.trans (Nat.mul_le_mul_right _ ha)
    simp only [encGate, length_encPair, Line.code_fst]
    omega
  have hgates : (encList encGate c.code.1).length ≤ c.size * (23 + 8 * (n + c.size)) := by
    have h := length_encList_le encGate c.code.1 (b := 11 + 4 * (n + c.size)) (fun g hg => by
      rw [Circuit.code, Program.code_eq_ofFn_lines] at hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact hgate (c.program.lines j))
    rw [show c.code.1.length = c.size from Program.length_code c.program] at h
    nlinarith
  have houtputs : (encList encNat c.code.2).length ≤ m * (2 * (n + c.size) + 1) := by
    have h := length_encList_le encNat c.code.2 (b := n + c.size) (fun i hi => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      exact (length_encNat_le_self _).trans (Wire.toNat_lt (c.outputs j)).le)
    simpa [Circuit.code] using h
  simp only [encCode, length_encPair]
  nlinarith

end Cslib.Circuits.Boolean
