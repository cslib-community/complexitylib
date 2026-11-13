/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Adversaries with advice

An adversary with advice reads the unary parameter `n`, an advice word and its challenge word.
This module fixes that input encoding and relates such adversaries to uniform ones, in both
directions. A uniform adversary is an advice adversary that ignores its advice, and an advice
adversary run on empty advice is a uniform adversary. Every notion relative to a fixed advice
family thus specializes to its uniform counterpart at empty advice.

## Main definitions

* `Cslib.Crypto.encAdvisedInput`: the input encoding `((1ⁿ, advice), x)` of an adversary with
  advice.

## Main results

* `Cslib.Probability.IsPPT.dropAdvice`: a uniform adversary is an advice adversary that ignores
  its advice.
* `Cslib.Probability.IsPPTOn.nilAdvice`: an advice adversary run on empty advice is a uniform
  adversary.
-/

@[expose] public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- Input `((1ⁿ, advice), x)` of an adversary with advice: the parameter `n` in unary paired
with the advice word, then the challenge word `x`. The pair `(n, advice)` is framed, and within it
the parameter; `x` is not. -/
abbrev encAdvisedInput : (ℕ × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encUnary encBits) encBits

end Cslib.Crypto

namespace Cslib.Probability

open Cslib.Crypto Turing.MultiTapeTM

variable {β : Type} {output : β ↪ List Bool}

/-- A uniform adversary is an advice adversary that ignores its advice. -/
theorem IsPPT.dropAdvice {adversary : ℕ → List Bool → ProbComp β}
    (h : IsPPT output adversary) :
    IsPPTOn encAdvisedInput output
      (fun input : (ℕ × List Bool) × List Bool => adversary input.1.1 input.2) :=
  h.on.preprocess (input := encAdvisedInput)
    (prepare := fun input : (ℕ × List Bool) × List Bool => (input.1.1, input.2)) (by fun_prop)

/-- An advice adversary run on empty advice is a uniform adversary. -/
theorem IsPPTOn.nilAdvice {adversary : (ℕ × List Bool) × List Bool → ProbComp β}
    (h : IsPPTOn encAdvisedInput output adversary) :
    IsPPT output (fun n word => adversary ((n, []), word)) :=
  h.preprocess (input := encPair encUnary encBits)
    (prepare := fun input : ℕ × List Bool => ((input.1, []), input.2)) (by fun_prop)

end Cslib.Probability
