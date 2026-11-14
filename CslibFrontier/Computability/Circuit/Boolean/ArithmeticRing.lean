/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Arithmetic.Synthesis

/-!
# Boolean circuits as arithmetic circuits over any ring

Boolean values are represented by the ring elements zero and one. AND is multiplication,
NOT is `1 + (-1) * x`, and OR is `(x + y) + (-1) * (x * y)`. These expressions use only
constant, addition and multiplication gates and work in every characteristic. Five arithmetic
gates per Boolean gate suffice. All outputs agree on Boolean-valued inputs; no assertion about
arbitrary ring-valued inputs is made. Constants count as gates and wires are free.

This is the Boolean-to-arithmetic direction of [Arora–Barak, web draft 2007-01-08,
Chapter 14 Exercise 1, printed p. 265/PDF p. 281][AroraBarak07]. Rings need not be finite.
The opposite direction requires a finite-carrier encoding. No formal polynomial equality or
compiler-runtime bound is claimed.

## Main results

* `Cslib.Circuits.Boolean.exists_ring_simulation`: all-output simulation with gate-size factor
  five over any ring, using the zero/one representation.
-/

public section

namespace Cslib.Circuits.Boolean

variable {R : Type*} [Ring R]

private def ringInterpretation : Interpretation signature R
  | .const b, _ => b.toNat
  | .not, x => 1 + (-1) * x 0
  | .and, x => x 0 * x 1
  | .or, x => (x 0 + x 1) + (-1) * (x 0 * x 1)

private theorem ring_gate_synthesis (op : Op) :
    Synthesis (arithInterpretation R) (inputs (signature.Arity op))
      {ringInterpretation op} 5 := by
  cases op with
  | const b =>
    exact (Synthesis.arith_const (constant := id) (b.toNat : R)).mono
      Set.Subset.rfl Set.Subset.rfl (by decide)
  | not =>
    have hx : Synthesis (arithInterpretation R) (inputs 1) {fun x => x 0} 0 :=
      Synthesis.of_mem ⟨0, rfl⟩
    have hm : Synthesis (arithInterpretation R) (inputs 1) {fun _ => (-1 : R)} 1 :=
      Synthesis.arith_const (constant := id) (-1)
    have hc : Synthesis (arithInterpretation R) (inputs 1) {fun _ => (1 : R)} 1 :=
      Synthesis.arith_const (constant := id) 1
    have h := hc.binary (hm.binary hx ArithOp.mul) ArithOp.add
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by decide)
  | and =>
    exact (Synthesis.arith_mul (constant := id) (R := R)
      (s := inputs 2) ⟨0, rfl⟩ ⟨1, rfl⟩).mono
      Set.Subset.rfl Set.Subset.rfl (by decide)
  | or =>
    have hs : Synthesis (arithInterpretation R) (inputs 2) {fun x => x 0 + x 1} 1 :=
      Synthesis.arith_add (constant := id) ⟨0, rfl⟩ ⟨1, rfl⟩
    have hp : Synthesis (arithInterpretation R) (inputs 2) {fun x => x 0 * x 1} 1 :=
      Synthesis.arith_mul (constant := id) ⟨0, rfl⟩ ⟨1, rfl⟩
    have hm : Synthesis (arithInterpretation R) (inputs 2) {fun _ => (-1 : R)} 1 :=
      Synthesis.arith_const (constant := id) (-1)
    exact hs.binary (hm.binary hp ArithOp.mul) ArithOp.add

/-- Every De Morgan circuit has an arithmetic simulation over any ring with at most five
arithmetic gates per Boolean gate. Inputs and outputs represent false by zero and true by one.
Correctness is on these represented inputs, rather than on arbitrary ring inputs. -/
theorem exists_ring_simulation {n m : ℕ} (c : Circuit signature n m) :
    ∃ d : Circuit (arithSignature R) n m,
      d.size ≤ 5 * c.size ∧ ∀ x : Fin n → Bool,
        d.eval (arithInterpretation R) (fun i => (x i).toNat) =
          fun j => ((c.eval interpretation x j).toNat : R) := by
  let hom : Homomorphism interpretation (ringInterpretation (R := R)) :=
    ⟨(fun b => (b.toNat : R)), by
      intro op input
      cases op with
      | const b => rfl
      | not => cases h : input 0 <;> simp [interpretation, ringInterpretation, h]
      | and => cases h : input 0 <;> cases k : input 1 <;>
          simp [interpretation, ringInterpretation, h, k]
      | or => cases h : input 0 <;> cases k : input 1 <;>
          simp [interpretation, ringInterpretation, h, k]⟩
  obtain ⟨d, hd, hsize⟩ := c.exists_simulation_le
    (fun op => (ring_gate_synthesis (R := R) op).exists_circuit)
  refine ⟨d, hsize, ?_⟩
  intro x
  rw [hd]
  exact (c.map_eval hom x).symm

end Cslib.Circuits.Boolean
