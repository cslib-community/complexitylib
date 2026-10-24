/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Certified fair-bit and word sampling

The finite-uniform Boolean program has a one-instruction machine realization. This primitive is
independent of the input and is registered with `fun_prop`. Uniform words are sampled by one fixed
scanner with a linear clock. A runtime sample length must itself be computed in unary, so the
certificate includes the cost of writing the sampled word. Finite uniformity alone does not imply
strict fair-coin PPT.

## Main results

* `Cslib.Probability.isPPTOn_uniform_bool`: one fair bit is uniformly PPT.
* `Cslib.Probability.isPPTOn_sampleList`: uniform words from a unary count.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleList`: sample an efficiently computed length.

## References

Adapted from Cslib/Computability/Probabilistic/Sampling.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing encodings and common machine.
-/

@[expose] public section

namespace Cslib.Probability

private def coinMachine : Turing.MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

/-- Sampling one fair bit is strict PPT for every fixed input encoding. -/
@[fun_prop]
theorem isPPTOn_uniform_bool {α : Type} (input : α ↪ List Bool) :
    IsPPTOn input Turing.MultiTapeTM.encBool (fun _ => ProbComp.uniform Bool) := by
  refine ⟨0, Unit, inferInstance, coinMachine, 1, 0, fun a => ?_⟩
  change (ProbComp.eval (ProbComp.uniform Bool)).map (fun bit => [bit]) = _
  simp [Turing.MultiTapePTM.runClosed, Turing.MultiTapePTM.run, Turing.MultiTapePTM.runFrom,
    Turing.MultiTapePTM.runConfigFrom, Turing.MultiTapeMachine.runConfigFrom, coinMachine,
    Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init, Turing.MultiTapeMachine.Config.step,
    Turing.Action.apply]

/-- Uniform words have one finite fair-coin implementation for all unary input lengths. -/
theorem isPPTOn_sampleList :
    IsPPTOn Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encBits BitString.sampleList := by
  refine ⟨0, Unit, inferInstance, Turing.MultiTapePTM.uniformListMachine, 1, 1, fun n => ?_⟩
  simpa only [BitString.eval_sampleList, Turing.MultiTapeTM.encBits, Function.Embedding.coe_refl,
    Turing.MultiTapeTM.encUnary_apply, List.length_replicate, pow_one, one_mul, PMF.map_id] using
    (Turing.MultiTapePTM.eval_uniformListMachine (Turing.MultiTapeTM.encUnary n)).symm

end Cslib.Probability

/-- Sample an efficiently computed number of independent fair bits, charging the count in unary. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.sampleList {α : Type}
    {input : α ↪ List Bool} {count : α → ℕ}
    (hcount : ComputableTidilyInPolyTime count input encUnary) :
    Cslib.Probability.IsPPTOn input encBits (fun a => Cslib.BitString.sampleList (count a)) :=
  Cslib.Probability.isPPTOn_sampleList.preprocess
    (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy hcount)
