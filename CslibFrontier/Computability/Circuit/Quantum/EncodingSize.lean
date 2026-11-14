/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Uniform
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Length of encoded quantum circuits

Gate codes use unary wire indices and framed lists. These are lengths in that encoding,
not implementation bytes or the size of a circuit generator's program.

## Main results

* `Cslib.Quantum.length_encGateCode`: the contribution of the target and controls.
* `Cslib.Quantum.GateCode.WellFormed.length_encoding_le`: a well-formed gate on `m` wires
  occupies at most `6 * m` bits.
* `Cslib.Quantum.length_encGateCodes_le`: a list of `G` well-formed gates occupies at most
  `G * (12 * m + 1)` bits, including list framing.

These bounds are original consequences of the existing encoding definitions.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- The exact encoded length: a framed flag, a framed unary target, and framed unary controls. -/
theorem length_encGateCode (hadamard : Bool) (target : ℕ) (controls : List ℕ) :
    (encGateCode (hadamard, target, controls)).length =
      4 + 2 * target + (encList encUnary controls).length := by
  simp only [encGateCode, length_encPair, encUnary_apply, encBool_apply,
    List.length_singleton, List.length_replicate]
  omega

/-- A valid gate has at most two controls, and every wire index is below the register width. -/
theorem GateCode.WellFormed.length_encoding_le {m : ℕ} {g : GateCode}
    (hg : g.WellFormed m) : (encGateCode g).length ≤ 6 * m := by
  obtain ⟨b, t, cs⟩ := g
  have ht : t < m := by cases b <;> simp_all [GateCode.WellFormed]
  have hlen : cs.length ≤ 2 := by cases b <;> simp_all [GateCode.WellFormed]
  have hcs : ∀ c ∈ cs, c < m := by cases b <;> simp_all [GateCode.WellFormed]
  have henc := length_encList_le encUnary cs (b := m - 1) (by
    intro c hc
    simpa only [encUnary_apply, List.length_replicate] using Nat.le_sub_one_of_lt (hcs c hc))
  have hmul := Nat.mul_le_mul_right (2 * (m - 1) + 1) hlen
  rw [length_encGateCode]
  omega

/-- Encoded length of a valid circuit, counting the framing around every instruction. -/
theorem length_encGateCodes_le {m : ℕ} {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed m) :
    (encList encGateCode gs).length ≤ gs.length * (12 * m + 1) := by
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using
    length_encList_le encGateCode gs (fun g hg => (hgs g hg).length_encoding_le)

end Cslib.Quantum
