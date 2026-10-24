/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Probabilistic.PPT.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform PPT with a security parameter

Cryptographic algorithms receive a unary security parameter and an auxiliary binary word.
`IsPPT` uses the existing pair encoding and the same strict, finite-machine contract as
`IsPPTOn`. One machine and one polynomial work for every parameter and auxiliary input;
the definition does not permit a separate algorithm or nonuniform advice at each length.

## Main definitions

* `Cslib.Probability.IsPPT`: strict uniform PPT for parameterized algorithms.

## Main results

* `Cslib.Probability.IsPPT.preprocess`: compute the parameter and auxiliary input efficiently.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPT`: run a deterministic word algorithm.

## References

Adapted from Computability/Probabilistic/{PPT,Parameter}.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy pair and unary encodings.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- A uniform algorithm with a unary security parameter and an auxiliary binary word.
Its strict clock is polynomial in the sum of the parameter and auxiliary-input length. -/
@[fun_prop]
def IsPPT {β : Type} (output : β ↪ List Bool)
    (program : ℕ → List Bool → ProbComp β) : Prop :=
  IsPPTOn (encPair encUnary encBits) output (fun input => program input.1 input.2)

variable {β : Type} {output : β ↪ List Bool} {program program' : ℕ → List Bool → ProbComp β}

/-- Expose the existing encoded-input contract. -/
theorem IsPPT.on (h : IsPPT output program) :
    IsPPTOn (encPair encUnary encBits) output (fun input => program input.1 input.2) := h

/-- An encoded certificate for the unary parameter and auxiliary input is uniform PPT. -/
@[fun_prop]
theorem IsPPTOn.isPPT
    (h : IsPPTOn (encPair encUnary encBits) output (fun input => program input.1 input.2)) :
    IsPPT output program := h

/-- Distributionally equal parameterized programs share their finite-machine certificate. -/
theorem IsPPT.congr (h : IsPPT output program)
    (heq : ∀ n input, ProbComp.eval (program n input) = ProbComp.eval (program' n input)) :
    IsPPT output program' := h.on.congr (fun input => heq input.1 input.2)

/-- Call a parameterized routine after efficiently preparing both input components. -/
theorem IsPPT.preprocess {α : Type} {input : α ↪ List Bool}
    (h : IsPPT output program) {parameter : α → ℕ} {auxiliary : α → List Bool}
    (hparameter : ComputableTidilyInPolyTime parameter input encUnary)
    (hauxiliary : ComputableTidilyInPolyTime auxiliary input encBits) :
    IsPPTOn input output (fun a => program (parameter a) (auxiliary a)) :=
  h.on.preprocess
    (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy (hparameter.prod hauxiliary))

end Cslib.Probability

/-- Run a deterministic polynomial-time word algorithm on the auxiliary input. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.isPPT {β : Type}
    {output : β ↪ List Bool} {f : List Bool → β}
    (h : ComputableTidilyInPolyTime f encBits output) :
    Cslib.Probability.IsPPT output (fun _ input => pure (f input)) :=
  (h.comp (ComputableTidilyInPolyTime.snd encUnary encBits)).isPPTOn
