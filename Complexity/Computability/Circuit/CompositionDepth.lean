/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Composition.lean`)

public import Cslib.Computability.Circuit.Composition
public import Complexity.Computability.Circuit.Depth

/-!
# Depth of composed circuits

Continuing a program does not change the depths of its wires (`Program.wireDepths_append_castAdd`),
and the wires of the continuation are at most as deep as in the continuation alone, plus the depth
of the wires feeding it (`Program.wireDepths_append_appendedWire_le`). So sequential composition
adds depths (`Circuit.depth_comp_le`) and parallel composition takes their maximum
(`Circuit.depth_append_le`).

## Main results

* `Cslib.Circuits.Program.wireDepths_append_castAdd`,
  `Cslib.Circuits.Program.wireDepths_append_appendedWire_le`: depths in a continued program.
* `Cslib.Circuits.Circuit.depth_comp_le`: `depth (d.comp c) ≤ depth d + depth c`.
* `Cslib.Circuits.Circuit.depth_append_le`: `depth (c.append d) ≤ max (depth c) (depth d)`.
* `Cslib.Circuits.Circuit.depthWith_comp_le`, `Cslib.Circuits.Circuit.depthWith_append_le`: the
  same for depths with costs.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n k m p g₁ g₂ : ℕ}

namespace Program

variable (P : Program σ n g₁) (feed : Fin k → Wire n g₁)

/-- Continuing a program does not change the depths with costs of its wires. -/
@[simp] theorem wireDepthsWith_append_castAdd (cost : σ.Op → ℕ) (q : Program σ k g₂)
    (w : Wire n g₁) :
    (P.append feed q).wireDepthsWith cost (w.castAdd g₂) = P.wireDepthsWith cost w :=
  P.trace_append_castAdd feed (depthInterpretation cost) (fun _ => 0) q w

/-- With costs, a wire of the continuation is at most as deep as in the continuation alone, plus
the depth of the wires feeding it. -/
theorem wireDepthsWith_append_appendedWire_le (cost : σ.Op → ℕ) {D : ℕ}
    (hD : ∀ i, P.wireDepthsWith cost (feed i) ≤ D) (q : Program σ k g₂) (w : Wire k g₂) :
    (P.append feed q).wireDepthsWith cost (appendedWire feed w) ≤ q.wireDepthsWith cost w + D := by
  change (P.append feed q).trace (depthInterpretation cost) (fun _ => 0)
    (appendedWire feed w) ≤ q.trace (depthInterpretation cost) (fun _ => 0) w + D
  rw [P.trace_append_appendedWire]
  exact q.trace_rel (fun a b => a ≤ b + D) (fun i => (hD i).trans_eq (Nat.zero_add D).symm)
    (fun j _ _ h => depthInterpretation_le_add cost (q.lines j).op h) w

/-- Continuing a program does not change the depths of its wires. -/
@[simp] theorem wireDepths_append_castAdd (q : Program σ k g₂) (w : Wire n g₁) :
    (P.append feed q).wireDepths (w.castAdd g₂) = P.wireDepths w := by
  simpa only [Program.wireDepthsWith_one] using wireDepthsWith_append_castAdd P feed 1 q w

/-- A wire of the continuation is at most as deep as in the continuation alone, plus the depth of
the wires feeding it. -/
theorem wireDepths_append_appendedWire_le {D : ℕ} (hD : ∀ i, P.wireDepths (feed i) ≤ D)
    (q : Program σ k g₂) (w : Wire k g₂) :
    (P.append feed q).wireDepths (appendedWire feed w) ≤ q.wireDepths w + D := by
  simpa only [Program.wireDepthsWith_one] using
    wireDepthsWith_append_appendedWire_le P feed 1 (by simpa only [Program.wireDepthsWith_one]) q w

end Program

namespace Circuit

/-- Output `o` in the left block of `c.append d` is the corresponding output wire of `c`. -/
@[simp] theorem outputs_append_castAdd (c : Circuit σ n m) (d : Circuit σ n p) (o : Fin m) :
    (c.append d).outputs (Fin.castAdd p o) = (c.outputs o).castAdd d.size :=
  Fin.append_left _ _ o

/-- Output `o` in the right block of `c.append d` is the appended output wire of `d`. -/
@[simp] theorem outputs_append_natAdd (c : Circuit σ n m) (d : Circuit σ n p) (o : Fin p) :
    (c.append d).outputs (Fin.natAdd m o) = Program.appendedWire Wire.input (d.outputs o) :=
  Fin.append_right _ _ o

/-- **Sequential composition adds depths with costs.** -/
theorem depthWith_comp_le (cost : σ.Op → ℕ) (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).depthWith cost ≤ d.depthWith cost + c.depthWith cost :=
  (Circuit.depthWith_le_iff cost _).2 fun o =>
    (Program.wireDepthsWith_append_appendedWire_le c.program c.outputs cost
      (fun i => c.wireDepthsWith_outputs_le_depthWith cost i) d.program (d.outputs o)).trans
      (Nat.add_le_add_right (d.wireDepthsWith_outputs_le_depthWith cost o) _)

/-- **Parallel composition takes the larger depth with costs.** -/
theorem depthWith_append_le (cost : σ.Op → ℕ) (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).depthWith cost ≤ max (c.depthWith cost) (d.depthWith cost) := by
  refine (Circuit.depthWith_le_iff cost _).2 fun o => ?_
  induction o using Fin.addCases with
  | left o =>
    change (c.program.append Wire.input d.program).wireDepthsWith cost
      ((c.append d).outputs _) ≤ _
    rw [outputs_append_castAdd, Program.wireDepthsWith_append_castAdd]
    exact (c.wireDepthsWith_outputs_le_depthWith cost o).trans (le_max_left _ _)
  | right o =>
    change (c.program.append Wire.input d.program).wireDepthsWith cost
      ((c.append d).outputs _) ≤ _
    rw [outputs_append_natAdd]
    exact (Program.wireDepthsWith_append_appendedWire_le c.program Wire.input cost (D := 0)
      (fun i => le_rfl) d.program (d.outputs o)).trans
      ((d.wireDepthsWith_outputs_le_depthWith cost o).trans (le_max_right _ _))

/-- **Sequential composition adds depths.** -/
theorem depth_comp_le (d : Circuit σ m p) (c : Circuit σ n m) :
    (d.comp c).depth ≤ d.depth + c.depth := by
  simpa only [Circuit.depthWith_one] using depthWith_comp_le 1 d c

/-- **Parallel composition takes the larger depth.** -/
theorem depth_append_le (c : Circuit σ n m) (d : Circuit σ n p) :
    (c.append d).depth ≤ max c.depth d.depth := by
  simpa only [Circuit.depthWith_one] using depthWith_append_le 1 c d

end Circuit

end Cslib.Circuits
