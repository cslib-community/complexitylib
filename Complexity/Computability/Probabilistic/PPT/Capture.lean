/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.OutputPrefix
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Captured inputs in efficient probabilistic programs

Ordinary monadic continuations and callbacks may use both the caller's input and a sampled
result. These operations specialize the strict oracle calculus to empty external channels. Its
clean-realization compiler charges copying, framing and preparation; the existing pair encoding
makes the retained data a typed value for the next computation. Prefixing is pairing followed by
efficient deterministic concatenation.

## Main results

* `Cslib.Probability.IsPPTOn.prefix`: write efficiently computed input data before
  probabilistic output.
* `Cslib.Probability.IsPPTOn.pair`: retain efficiently computed data alongside a sampled result.
* `Cslib.Probability.IsPPTOn.bind_with`: a monadic continuation may capture the original input.
* `Cslib.Probability.IsPPTOn.map_with`: a deterministic callback may capture the original input.
* `Cslib.Probability.IsPPTOn.cond`, `Cslib.Probability.IsPPTOn.cond'`,
  `Cslib.Probability.IsPPTOn.ite`, `Cslib.Probability.IsPPTOn.ite'`: efficient branch selection.

## References

Adapted from Computability/Probabilistic/{Realization/Composition,Composition}.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy calculus
and framed pair encoding.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- Write efficiently computed input data before a probabilistic output, charging preparation. -/
theorem IsPPTOn.prefix {α : Type} {input : α ↪ List Bool} {pre : α → List Bool}
    {program : α → ProbComp (List Bool)} (hprogram : IsPPTOn input encBits program)
    (hprefix : ComputableTidilyInPolyTime pre input encBits) :
    IsPPTOn input encBits (fun a => (pre a ++ ·) <$> program a) := by
  apply IsOraclePPTOn.isPPTOn
  have happend := ComputableTidilyInPolyTime.bitsAppend
    (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  simpa only [ProbOracleComp.sample_map, Functor.map_map, Function.comp_def] using
    ((hprogram.isOraclePPTOn (Operation := Empty)).pair hprefix).map happend

variable {α β γ : Type} {input : α ↪ List Bool} {left : β ↪ List Bool}
  {right : γ ↪ List Bool}

/-- Retain efficiently computed input data beside a sampled result, using the existing encoding. -/
@[fun_prop]
theorem IsPPTOn.pair {program : α → ProbComp γ} {f : α → β}
    (hprogram : IsPPTOn input right program) (hf : ComputableTidilyInPolyTime f input left) :
    IsPPTOn input (encPair left right) (fun a => (fun b => (f a, b)) <$> program a) := by
  apply IsOraclePPTOn.isPPTOn
  simpa only [ProbOracleComp.sample_map] using
    (hprogram.isOraclePPTOn (Operation := Empty)).pair hf

/-- Keep the original argument available to a later computation, charging its encoded copy. -/
theorem IsPPTOn.keep_input {program : α → ProbComp β}
    (hprogram : IsPPTOn input left program) :
    IsPPTOn input (encPair input left) (fun a => (fun b => (a, b)) <$> program a) :=
  hprogram.pair ComputableTidilyInPolyTime.id'

/-- A monadic continuation may use both the caller's input and the sampled result. -/
@[fun_prop]
theorem IsPPTOn.bind_with {first : α → ProbComp β} {second : α → β → ProbComp γ}
    (hfirst : IsPPTOn input left first)
    (hsecond : IsPPTOn (encPair input left) right (fun pair => second pair.1 pair.2)) :
    IsPPTOn input right (fun a => do
      let b ← first a
      second a b) := by
  simpa only [bind_map_left] using hfirst.keep_input.bind hsecond

/-- A deterministic callback may capture the original argument. -/
@[fun_prop]
theorem IsPPTOn.map_with {program : α → ProbComp β} {f : α → β → γ}
    (hprogram : IsPPTOn input left program)
    (hf : ComputableInPolyTime (fun pair => f pair.1 pair.2) (encPair input left) right) :
    IsPPTOn input right (fun a => f a <$> program a) := by
  simpa only [bind_pure_comp] using
    hprogram.bind_with (right := right) (second := fun a b => pure (f a b)) hf.tidy.isPPTOn

/-- Select a closed probabilistic branch with an efficient Boolean condition, using the
empty-channel specialization of oracle branch selection. -/
@[fun_prop]
theorem IsPPTOn.cond {condition : α → Bool} {yes no : α → ProbComp β}
    (hcondition : ComputableTidilyInPolyTime condition input encBool)
    (hyes : IsPPTOn input left yes) (hno : IsPPTOn input left no) :
    IsPPTOn input left (fun a => if condition a then yes a else no a) := by
  apply IsOraclePPTOn.isPPTOn
  simpa only [apply_ite] using IsOraclePPTOn.cond hcondition
    (hyes.isOraclePPTOn (Operation := Empty)) (hno.isOraclePPTOn (Operation := Empty))

/-- Select a closed probabilistic branch with an efficiently decidable condition. -/
@[fun_prop]
theorem IsPPTOn.ite {condition : α → Prop} [∀ a, Decidable (condition a)]
    {yes no : α → ProbComp β}
    (hcondition : ComputableTidilyInPolyTime (fun a => decide (condition a)) input encBool)
    (hyes : IsPPTOn input left yes) (hno : IsPPTOn input left no) :
    IsPPTOn input left (fun a => if condition a then yes a else no a) := by
  simpa only [decide_eq_true_eq] using hyes.cond hcondition hno

/-- `Cslib.Probability.IsPPTOn.cond` with a plain polynomial-time condition. -/
@[fun_prop]
theorem IsPPTOn.cond' {condition : α → Bool} {yes no : α → ProbComp β}
    (hcondition : ComputableInPolyTime condition input encBool)
    (hyes : IsPPTOn input left yes) (hno : IsPPTOn input left no) :
    IsPPTOn input left (fun a => if condition a then yes a else no a) := by
  apply IsOraclePPTOn.isPPTOn
  simpa only [apply_ite] using IsOraclePPTOn.cond' hcondition
    (hyes.isOraclePPTOn (Operation := Empty)) (hno.isOraclePPTOn (Operation := Empty))

/-- `Cslib.Probability.IsPPTOn.ite` with a plain polynomial-time decision. -/
@[fun_prop]
theorem IsPPTOn.ite' {condition : α → Prop} [∀ a, Decidable (condition a)]
    {yes no : α → ProbComp β}
    (hcondition : ComputableInPolyTime (fun a => decide (condition a)) input encBool)
    (hyes : IsPPTOn input left yes) (hno : IsPPTOn input left no) :
    IsPPTOn input left (fun a => if condition a then yes a else no a) := by
  simpa only [decide_eq_true_eq] using hyes.cond' hcondition hno

end Cslib.Probability
