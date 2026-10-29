/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Repeat
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime.Init
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Strict PPT bounded repetition

Repeated runs are realized by splitting one polynomial-length random tape into independent
blocks and mapping the saved-coin evaluator over them. The caller writes an ordinary list
traversal, and the certificate charges for the entire encoded result list. Neither the output
type nor its encoding needs a finite range.

## Main results

* `Cslib.Probability.IsPPTOn.replicate`, `.replicate_bool`: collect independent runs.
* `Cslib.Probability.IsPPTOn.countTrue`: count successful trials in unary.
* `Cslib.Probability.IsPPTOn.testProbabilityLT`: test a rational acceptance threshold.

## References

Adapted from Computability/Probabilistic/Repeat.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing flat-seed law and plain list
calculus.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Collect an efficiently computed number of independent runs. All output framing and storage
are charged, including when the number of runs depends on the complete input. -/
@[program_certificate]
theorem IsPPTOn.replicate {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → ProbComp β} {count : α → ℕ}
    (hprogram : IsPPTOn input output program)
    (hcount : ComputableInPolyTime count input encUnary) :
    IsPPTOn input (encList output) (fun a => OracleComp.replicate (count a) (program a)) := by
  obtain ⟨c, d, evaluate, hevaluate, hlaw⟩ := hprogram.exists_seeded_evaluator
  let budget (a : α) := c * ((input a).length + 1) ^ d
  have hbudget : ComputableInPolyTime budget input encUnary := by
    dsimp only [budget]
    fun_prop
  have hrows : ComputableInPolyTime (fun p : α × List Bool =>
      BitString.listRows (count p.1) (budget p.1) p.2)
      (encPair input encBits) (encList encBits) := by fun_prop
  have heval : ComputableInPolyTime (fun p : (α × List Bool) × List Bool => evaluate p.1.1 p.2)
      (encPair (encPair input encBits) encBits) output :=
    (ComputableInPolyTime.of_tidy hevaluate).comp
      (((ComputableInPolyTime.fst input encBits).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  have hmap := ComputableInPolyTime.mapWithInput (f := fun q row => evaluate q.1 row) hrows heval
  have hcoins := (ComputableInPolyTime.unary_mul' hcount hbudget).sampleList
  apply (hcoins.map_with (f := fun a coins =>
    (BitString.listRows (count a) (budget a) coins).map (evaluate a)) hmap).congr
  intro a
  simpa only [ProbComp.eval_map, BitString.eval_sampleList, Function.comp_def] using
    (ProbComp.eval_replicate_of_uniformList (count a) (budget a)
      (program a) (evaluate a) (hlaw a)).symm

/-- Repeated Boolean results may use the raw bit-list encoding. -/
@[program_certificate]
theorem IsPPTOn.replicate_bool {α : Type} {input : α ↪ List Bool}
    {program : α → ProbComp Bool} {count : α → ℕ}
    (hprogram : IsPPTOn input encBool program)
    (hcount : ComputableInPolyTime count input encUnary) :
    IsPPTOn input encBits (fun a => OracleComp.replicate (count a) (program a)) := by
  simpa only [id_map'] using (hprogram.replicate hcount).map
    ComputableInPolyTime.listToBits

/-- Count successes in independent trials, charging all collected bits and the unary result. -/
@[program_certificate]
theorem IsPPTOn.countTrue {α : Type} {input : α ↪ List Bool}
    {program : α → ProbComp Bool} {count : α → ℕ}
    (hprogram : IsPPTOn input encBool program)
    (hcount : ComputableInPolyTime count input encUnary) :
    IsPPTOn input encUnary (fun a => OracleComp.countTrue (count a) (program a)) := by
  unfold OracleComp.countTrue
  fun_prop

/-- Rational threshold testing charges the trial count and every unary cross-product. -/
@[program_certificate]
theorem IsPPTOn.testProbabilityLT {α : Type} {input : α ↪ List Bool}
    {program : α → ProbComp Bool} {count numerator denominator : α → ℕ}
    (hprogram : IsPPTOn input encBool program)
    (hcount : ComputableInPolyTime count input encUnary)
    (hnumerator : ComputableInPolyTime numerator input encUnary)
    (hdenominator : ComputableInPolyTime denominator input encUnary) :
    IsPPTOn input encBool (fun a =>
      OracleComp.testProbabilityLT (count a) (numerator a) (denominator a) (program a)) := by
  unfold OracleComp.testProbabilityLT
  fun_prop

end Cslib.Probability
