/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CodeComposition
public import Complexity.Computability.Circuit.Boolean.Formula
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform instantiation of fixed Boolean formula templates

The formula is fixed, while the target input count and its selected binary input references may
vary. The certificate constructs the actual code of the renamed formula. It does not use a
finite encoding of circuits at a fixed width. Variable-size families of instances can use
`appendCodes` after providing their uniform scalar generator.

## Main definitions

* `Cslib.Circuits.Boolean.formulaCode`: the actual code of a fixed formula at selected wires.

## Main results

* `Cslib.Circuits.Boolean.formulaCode_eq_code`: exact agreement with typed instantiation.
* `Cslib.Circuits.Boolean.computableInPolyTime_formulaCode`: instantiate a fixed formula
  at efficiently computed input wires.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

/-- Instantiate a formula at raw wire numbers. This algorithm is total even when a selected
wire is outside the declared input count; its typed correctness theorem requires valid wires. -/
def formulaCode {m : ℕ} (n : ℕ) (F : Formula signature m) (wires : Fin m → ℕ) :
    List (Op × List ℕ) × List ℕ :=
  match F with
  | .input i => ([], [wires i])
  | .gate op args => compCode n (Circuit.oneGate (σ := signature) op id).code
      (appendCodes n (List.ofFn fun i => formulaCode n (args i) wires))

/-- Instantiating valid input wires constructs exactly the renamed formula's circuit code. -/
theorem formulaCode_eq_code {n m : ℕ} (F : Formula signature m) (wires : Fin m → Fin n) :
    formulaCode n F (fun i => (wires i).val) = (F.rename wires).toCircuit.code := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [formulaCode, ih, appendCodes_code, compCode_code,
      Formula.rename, Formula.gate_bind, Formula.toCircuit]

/-- A fixed formula's full instantiated code is polynomial-time in the target input count and
its selected binary wire numbers. This is uniform in every target width and reference. -/
theorem computableInPolyTime_formulaCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {m : ℕ} (F : Formula signature m) {wires : α → Fin m → ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hwires : ∀ i, ComputableInPolyTime (fun a => wires a i) enc encNat) :
    ComputableInPolyTime (fun a => formulaCode (n a) F (wires a)) enc encCode := by
  induction F with
  | input i => exact (const []).prod ((hwires i).cons' (const []))
  | gate op args ih =>
    exact computableInPolyTime_compCode hn
      (const (Circuit.oneGate (σ := signature) op id).code)
      (computableInPolyTime_appendCodes hn (ofFn (fun i => ih i)))

end Cslib.Circuits.Boolean
