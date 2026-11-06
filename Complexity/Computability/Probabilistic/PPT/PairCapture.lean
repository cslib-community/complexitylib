/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.PPT.Capture
public import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Pair-unpacked captured-input composition for efficient probabilistic programs

`IsPPTOn.bind_with`, `IsPPTOn.map_with`, `IsOraclePPTOn.bind_with` and
`IsOraclePPTOn.map_with'` take curried continuations `α → β → …` and synthesize
`fun pair => second pair.1 pair.2` over `encPair input middle`. When chaining multi-step
`do` blocks directly without `fun_prop` synthesis, passing an uncurried continuation
`α × β → …` avoids repeated `Prod.mk.eta` normalization in the premise.

## Main results

* `Cslib.Probability.IsPPTOn.bind_pair`: uncurried captured-input monadic bind for closed
  strict PPT programs.
* `Cslib.Probability.IsPPTOn.map_pair`: uncurried captured-input deterministic `pure`
  continuation for closed strict PPT programs.
* `Cslib.Probability.IsOraclePPTOn.bind_pair`: uncurried captured-input monadic bind for
  strict oracle PPT programs.
* `Cslib.Probability.IsOraclePPTOn.map_pair'`: uncurried captured-input deterministic `pure`
  continuation for strict oracle PPT programs with a plain `ComputableInPolyTime` premise.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {left : β ↪ List Bool} {middle : β ↪ List Bool}
  {right : γ ↪ List Bool} {output : γ ↪ List Bool}

/-- Sequence a closed strict PPT program with an uncurried continuation on `(a, b)` encoded
by `encPair input left`. -/
theorem IsPPTOn.bind_pair {first : α → ProbComp β} {second : α × β → ProbComp γ}
    (hfirst : IsPPTOn input left first)
    (hsecond : IsPPTOn (encPair input left) right second) :
    IsPPTOn input right (fun a => do
      let b ← first a
      second (a, b)) :=
  hfirst.bind_with (right := right) (second := fun a b => second (a, b)) hsecond

/-- Sequence a closed strict PPT program with an uncurried deterministic `pure` continuation
on `(a, b)` encoded by `encPair input left`. -/
theorem IsPPTOn.map_pair {first : α → ProbComp β} {second : α × β → γ}
    (hfirst : IsPPTOn input left first)
    (hsecond : ComputableInPolyTime second (encPair input left) right) :
    IsPPTOn input right (fun a => do
      let b ← first a
      pure (second (a, b))) :=
  hfirst.bind_pair hsecond.isPPTOn

/-- Sequence a strict oracle PPT program with an uncurried continuation on `(a, b)` encoded
by `encPair input middle`. -/
theorem IsOraclePPTOn.bind_pair
    {first : α → WordOracleComp Operation β} {second : α × β → WordOracleComp Operation γ}
    (hfirst : IsOraclePPTOn input middle first)
    (hsecond : IsOraclePPTOn (encPair input middle) output second) :
    IsOraclePPTOn input output (fun a => do
      let b ← first a
      second (a, b)) :=
  hfirst.bind_with (output := output) (second := fun a b => second (a, b)) hsecond

/-- Sequence a strict oracle PPT program with an uncurried deterministic `pure` continuation
on `(a, b)` encoded by `encPair input middle`. -/
theorem IsOraclePPTOn.map_pair'
    {first : α → WordOracleComp Operation β} {second : α × β → γ}
    (hfirst : IsOraclePPTOn input middle first)
    (hsecond : ComputableInPolyTime second (encPair input middle) output) :
    IsOraclePPTOn input output (fun a => do
      let b ← first a
      pure (second (a, b))) := by
  have := hfirst.1
  exact hfirst.bind_pair hsecond.isOraclePPTOn

end Cslib.Probability
