/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Basic
public import Cslib.Computability.Circuit.Composition

/-!
# Fusion atoms under circuit composition

Continuing a native program concatenates its semantic atoms with those of the continuation,
evaluated on the values supplied by the feeding wires. The identity keeps gate order and
multiplicity, including unused gates. No separate substitution operation is needed.

## Main results

* `Cslib.Circuits.Fusion.programAtoms_append`: exact atom extraction under program continuation.
* `Cslib.Circuits.Fusion.programAtoms_comp`: exact atom extraction under circuit composition.

## References

* Adapted from LowerBound/Fusion/Substitution.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u v

variable {σ : Signature.{u}} {U : Type v} {n m k g h : ℕ}

/-- Continuing a program appends the continuation's atoms, evaluated at its supplied inputs. -/
theorem programAtoms_append (p : Program σ n g) (feed : Fin m → Wire n g)
    (q : Program σ m h) (I : Interpretation σ U) (input : Fin n → U) :
    programAtoms (p.append feed q) I input =
      Fin.append (programAtoms p I input) (programAtoms q I (p.trace I input ∘ feed)) := by
  induction q with
  | empty =>
    funext k
    exact (Fin.append_left (programAtoms p I input) _ k).symm
  | gate q line ih =>
    rw [Program.append, programAtoms_gate, programAtoms_gate, Fin.append_snoc, ih]
    congr 1
    congr 1 with a : 1
    exact p.trace_append_appendedWire feed I input q (line.wires a)

/-- Composition lists the inner circuit's atoms first, then the outer circuit's atoms
evaluated on the inner outputs. -/
theorem programAtoms_comp (outer : Circuit σ m k) (inner : Circuit σ n m)
    (I : Interpretation σ U) (input : Fin n → U) :
    programAtoms (outer.comp inner).program I input =
      Fin.append (programAtoms inner.program I input)
        (programAtoms outer.program I (inner.eval I input)) :=
  programAtoms_append inner.program inner.outputs outer.program I input

end Cslib.Circuits.Fusion
