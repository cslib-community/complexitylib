/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.ShannonSynthesis
import Complexity.Computability.Circuit.Support
import Complexity.Computability.Circuit.Wiring

/-!
# Stored circuit evaluation regression clients

Compiled evaluations exercise the compiler replacements; kernel proofs separately check that
the mathematical API is unchanged. Synthesis imports the evaluator through its minterm client.
-/

namespace ComplexityTests.CircuitEvaluation

universe v u

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.ShannonSynthesis

-- The ordinary evaluator is usable on all inputs of a synthesized three-bit function.
/-- info: true -/
#guard_msgs in
#eval
  let f : BooleanFunction 3 := fun x => x 0 ^^ x 1 ^^ x 2
  let c := synthesize f
  (List.finRange 8).all fun j =>
    let x := (BitString.equivFin 3).symm j
    c.eval interpretation x 0 == f x

-- Read shared outputs from one retained vector, including the native input-index order.
/-- info: #[false, true, false, false, false, false, false, false] -/
#guard_msgs in
#eval ((mintermCircuit 3).evalVector interpretation ![true, false, false]).toArray

-- Structured fan-out repeats a record without changing its bit order.
/-- info: [true, false, true, false, true, false] -/
#guard_msgs in
#eval List.ofFn ((Circuit.wiringOn signature finProdFinEquiv finProdFinEquiv
  (fun p : Fin 3 × Fin 2 => ((0 : Fin 1), p.2))).eval interpretation ![true, false])

-- One unused gate, repeated gate outputs, and a direct input output.
private def shared : Circuit signature 1 4 :=
  ⟨.gate (.gate .empty ⟨.not, fun _ => .input 0⟩) ⟨.const true, Fin.elim0⟩,
    ![.gate 0, .input 0, .gate 0, .gate 0]⟩

/-- info: (#[false, true, false, false], [false, true, false, false], [false, true]) -/
#guard_msgs in
#eval
  let outputs := shared.eval interpretation ![true]
  (shared.evalVector interpretation ![true] |>.toArray, List.ofFn outputs,
    List.ofFn (shared.program.eval interpretation ![true]))

/-- info: (false, true, true) -/
#guard_msgs in
#eval (shared.program.trace interpretation ![true] (.gate ⟨0, by decide⟩),
  shared.program.trace interpretation ![true] (.gate ⟨1, by decide⟩),
  shared.program.trace interpretation ![true] (.input 0))

example : shared.eval interpretation ![true] = ![false, true, false, false] := by
  decide +kernel

-- A free negation and an expensive unused constant have different structural depths.
-- Only designated outputs contribute to circuit depth or input support.
private def weighted : signature.Op → ℕ
  | .const _ => 7
  | _ => 0

example : shared.program.depthsWith weighted ⟨0, by decide⟩ = 0 ∧
    shared.program.depthsWith weighted ⟨1, by decide⟩ = 7 ∧ shared.depthWith weighted = 0 ∧
    shared.program.gateSupport ⟨1, by decide⟩ = ∅ ∧ shared.inputSupport = {0} := by
  decide +kernel

-- Zero inputs and outputs need neither operations nor an inhabited carrier.
private def emptySignature : Signature where
  Op := Empty
  Arity := Empty.elim

private def emptyInterpretation : Interpretation emptySignature Empty := fun op => nomatch op

example : ((Circuit.id emptySignature 0).evalVector emptyInterpretation Fin.elim0).toArray =
    #[] := rfl

example : ((Program.empty : Program emptySignature 0 0).evalVector
    emptyInterpretation Fin.elim0).get = Fin.elim0 := by
  funext j
  exact j.elim0

-- Empty structured layouts work with an empty evaluation carrier.
example : ((Circuit.wiringOn emptySignature
    (finProdFinEquiv : Fin 0 × Fin 3 ≃ Fin 0) (Equiv.refl (Fin 0)) Fin.elim0).evalVector
      emptyInterpretation Fin.elim0).toArray = #[] := rfl

-- Nullary operations and a non-Boolean carrier do not require input values.
private def constantSignature : Signature where
  Op := Unit
  Arity := fun _ => 0

private def naturalConstant : Circuit constantSignature 0 2 :=
  ⟨.gate .empty ⟨(), Fin.elim0⟩, fun _ => .gate 0⟩

-- A nullary gate retains its weight, even though its support and input list are empty.
example : naturalConstant.depthWith (fun _ => 9) = 9 ∧
    naturalConstant.inputSupport = ∅ := by decide +kernel

/-- info: (#[37, 37], 37) -/
#guard_msgs in
#eval (naturalConstant.evalVector (fun _ _ => (37 : Nat)) Fin.elim0 |>.toArray,
  naturalConstant.eval (fun _ _ => (37 : Nat)) Fin.elim0 1)

-- Selecting no outputs preserves the cost of a gate already computed.
example (cost : constantSignature.Op → ℕ) :
    ((Circuit.wiringOn constantSignature (Equiv.refl (Fin 2)) finProdFinEquiv
      (fun _ : Fin 0 × Fin 3 => (0 : Fin 2))).comp naturalConstant).program.cost cost =
        cost () := by
  simp only [Circuit.cost_program_comp, Circuit.cost_program_wiringOn, Nat.add_zero,
    naturalConstant, Program.cost_gate, Program.cost_empty, Nat.zero_add]

-- Distinct signature and carrier universes remain polymorphic, including compiler adapters.
example {σ : Signature.{v}} {U : Type u} {n m : Nat} (c : Circuit σ n m)
    (i : Interpretation σ U) (x : Fin n → U) (j : Fin m) :
    (c.evalVector i x).get j = c.evalImpl i x j := by
  rw [← Circuit.eval_eq_evalImpl]
  simp

end ComplexityTests.CircuitEvaluation
