/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Basic
import Batteries.Data.Vector.Lemmas

/-!
# Circuit evaluation with stored gate values

`Program.evalVector` stores gate values in an array-backed vector as it evaluates the program.
The compiler uses this implementation for `Program.eval`, `Program.trace` and `Circuit.eval`;
the kernel definitions and their simplification rules remain unchanged. The replacement theorems
prove equality for arbitrary signatures and interpretations, without an inhabited carrier.

The vector evaluators compute every gate, including unused gates. Separate calls may recompute
the vector; retain `Circuit.evalVector` explicitly when reading several outputs. Compiler
replacements apply to callers compiled with this module imported, not previously compiled callers.
This module does not certify a runtime bound.

## Main definitions

* `Cslib.Circuits.Program.evalVector`, `Cslib.Circuits.Program.evalImpl`,
  `Cslib.Circuits.Program.traceImpl`: evaluate a program into a vector of gate values and
  provide compiler implementations for `Program.eval` and `Program.trace`.
* `Cslib.Circuits.Circuit.evalVector`, `Cslib.Circuits.Circuit.evalImpl`: evaluate all
  circuit outputs using one gate-value vector and provide a compiler implementation for
  `Circuit.eval`.

## Main results

* `Cslib.Circuits.Program.get_evalVector`: the stored values agree with `Program.eval`.
* `Cslib.Circuits.Circuit.get_evalVector`: the stored outputs agree with `Circuit.eval`.
* `Cslib.Circuits.Circuit.eval_eq_evalImpl`: proved compiler replacement for circuit evaluation.
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

namespace Program

/-- Evaluate every gate in program order, storing its value in a vector. -/
def evalVector {σ : Signature.{v}} {inputCount : Nat} {U : Type u} {gateCount : Nat}
    (p : Program σ inputCount gateCount) (i : Interpretation σ U) (x : Fin inputCount → U) :
    Vector U gateCount :=
  match p with
  | .empty => #v[]
  | .gate p line =>
    let prior := p.evalVector i x
    prior.push (line.eval i x prior.get)

/-- The stored gate values agree with the functional evaluator. -/
@[simp] theorem get_evalVector {σ : Signature.{v}} {inputCount : Nat} {U : Type u}
    {gateCount : Nat} (p : Program σ inputCount gateCount) (i : Interpretation σ U)
    (x : Fin inputCount → U) : (p.evalVector i x).get = p.eval i x := by
  induction p with
  | empty => funext j; exact j.elim0
  | gate p line ih =>
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [evalVector, ih]
    · simp [evalVector, ih]

/-- Compiler implementation of `Program.eval` using stored gate values. -/
def evalImpl {σ : Signature.{v}} {inputCount : Nat} {U : Type u} {gateCount : Nat}
    (p : Program σ inputCount gateCount) (i : Interpretation σ U) (x : Fin inputCount → U) :
    Fin gateCount → U :=
  (p.evalVector i x).get

/-- Proved compiler replacement of `Program.eval` by `Program.evalImpl`. -/
@[csimp] theorem eval_eq_evalImpl : @Program.eval = @Program.evalImpl := by
  funext σ n U g p i x
  exact (get_evalVector p i x).symm

/-- Compiler implementation of `Program.trace`, evaluating gates only for a gate wire. -/
def traceImpl {σ : Signature.{v}} {inputCount gateCount : Nat} {U : Type u}
    (p : Program σ inputCount gateCount) (i : Interpretation σ U) (x : Fin inputCount → U) :
    Wire inputCount gateCount → U
  | .input j => x j
  | .gate j => p.evalImpl i x j

/-- Proved compiler replacement of `Program.trace` by `Program.traceImpl`. -/
@[csimp] theorem trace_eq_traceImpl : @Program.trace = @Program.traceImpl := by
  funext σ n g U p i x w
  cases w with
  | input j => rfl
  | gate j => exact congrFun (get_evalVector p i x).symm j

end Program

namespace Circuit

/-- Evaluate all circuit outputs using one vector of stored gate values. Retain the result to
read several outputs without reevaluating the program. This also evaluates unused gates. -/
def evalVector {σ : Signature.{v}} {inputCount outputCount : Nat} {U : Type u}
    (c : Circuit σ inputCount outputCount) (i : Interpretation σ U) (x : Fin inputCount → U) :
    Vector U outputCount :=
  let gates := c.program.evalVector i x
  Vector.ofFn (fun j => Wire.elim x gates.get (c.outputs j))

/-- The stored output values agree with the functional evaluator. -/
@[simp] theorem get_evalVector {σ : Signature.{v}} {inputCount outputCount : Nat} {U : Type u}
    (c : Circuit σ inputCount outputCount) (i : Interpretation σ U) (x : Fin inputCount → U) :
    (c.evalVector i x).get = c.eval i x := by
  funext j
  simp [evalVector, Circuit.eval, Program.trace]

/-- Compiler implementation of `Circuit.eval` using stored gate values. -/
def evalImpl {σ : Signature.{v}} {inputCount outputCount : Nat} {U : Type u}
    (c : Circuit σ inputCount outputCount) (i : Interpretation σ U) (x : Fin inputCount → U) :
    Fin outputCount → U :=
  c.program.traceImpl i x ∘ c.outputs

/-- Proved compiler replacement of `Circuit.eval` by `Circuit.evalImpl`. -/
@[csimp] theorem eval_eq_evalImpl : @Circuit.eval = @Circuit.evalImpl := by
  funext σ n m U c i x
  unfold Circuit.eval evalImpl
  rw [Program.trace_eq_traceImpl]

end Circuit

end Cslib.Circuits
