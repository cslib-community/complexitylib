/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Clock
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Composing uniformly efficient probabilistic programs

Encoded probabilistic programs compose through ordinary monadic `bind`. Each certificate gives
one finite machine for every input. The output-length bound controls the continuation's clock,
and the machine compiler charges every instruction needed to prepare its fresh input.

This module also registers deterministic preprocessing and postprocessing with `fun_prop`.
Closed composition specializes the strict oracle calculus to the empty external-operation type.
The embedding preserves sampling and monadic sequencing, so the shared clean-realization
compiler supplies the machine and its resource bound. Continuations here consume the sampled
result; `PPT.Capture` retains the caller's input through the same calculus.

## Main results

* `Cslib.Probability.IsPPTOn.bind`: monadic composition preserves uniform strict PPT.
* `Cslib.Probability.IsPPTOn.map`: polynomial-time deterministic postprocessing preserves PPT.
* `Cslib.Probability.IsPPTOn.preprocess`: efficiently prepare a probabilistic program's input.

## References

Adapted from Computability/Probabilistic/Realization/Composition.lean and
Computability/Probabilistic/Composition.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the common machine and tidy deterministic
calculus.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM (ComputableInPolyTime ComputableTidilyInPolyTime)

variable {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
  {output : γ ↪ List Bool}

/-- Sequence two uniformly efficient encoded programs. The intermediate output length bounds
the continuation's time, and input preparation is included in the compiled polynomial clock. -/
@[fun_prop]
theorem IsPPTOn.bind {first : α → ProbComp β} {second : β → ProbComp γ}
    (hfirst : IsPPTOn input middle first) (hsecond : IsPPTOn middle output second) :
    IsPPTOn input output (fun a => do
      let b ← first a
      second b) := by
  apply IsOraclePPTOn.isPPTOn
  simpa only [ProbOracleComp.sample_bind] using
    (hfirst.isOraclePPTOn (Operation := Empty)).bind
      (hsecond.isOraclePPTOn (Operation := Empty))

/-- Prepare the encoded argument of a uniformly efficient probabilistic program. -/
@[fun_prop]
theorem IsPPTOn.preprocess {program : β → ProbComp γ} {prepare : α → β}
    (hprogram : IsPPTOn middle output program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsPPTOn input output (fun a => program (prepare a)) := by
  simpa only [pure_bind] using hprepare.tidy.isPPTOn.bind hprogram

/-- Polynomial-time deterministic processing of each sampled result preserves PPT. -/
@[fun_prop]
theorem IsPPTOn.map {program : α → ProbComp β} {f : β → γ}
    (hprogram : IsPPTOn input middle program) (hf : ComputableTidilyInPolyTime f middle output) :
    IsPPTOn input output (fun a => f <$> program a) := by
  simpa only [bind_pure_comp] using hprogram.bind hf.isPPTOn

end Cslib.Probability
