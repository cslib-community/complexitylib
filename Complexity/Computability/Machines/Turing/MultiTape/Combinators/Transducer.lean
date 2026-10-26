/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyZeroSpace
import Mathlib.Basic.Finite.Sum

/-!
# Finite-state transducers

A finite-state transducer reads its input once from left to right. In state `q`, on the symbol
`a`, it moves to state `(τ.step q a).1` and emits the word `(τ.step q a).2`; at the end of the
input it emits `τ.final q`. Every emitted word has length at most two.

`τ.toTM` runs a transducer as a Turing machine without work tapes, so every function computed by a
transducer is tidily computable in linear time and zero space.

## Main definitions

* `Turing.MultiTapeTM.Transducer`: finite-state transducers.
* `Turing.MultiTapeTM.Transducer.run`: the word a transducer emits on a word.
* `Turing.MultiTapeTM.Transducer.toTM`: the transducer as a machine without work tapes.

## Main results

* `Turing.MultiTapeTM.Transducer.computesInTimeAndSpace_toTM`: `τ.toTM` emits `τ.run τ.q₀ w` on
  `w` within `2 * w.length + 3` steps and zero space.
* `Turing.MultiTapeTM.Transducer.computableTidilyInTimeAndSpace`: a function computed by a
  transducer with finitely many states is tidily computable in linear time and zero space.
-/

namespace Turing.MultiTapeTM

namespace Transducer

/-- A function computed by a transducer with finitely many states is tidily computable in linear
time and zero space. -/
public theorem computableTidilyInTimeAndSpace {Q : Type} [Finite Q] (τ : Transducer Bool Q)
    {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 4 * (encIn a).length + 8)
      (fun _ => 0) :=
  ⟨0, _, inferInstance, τ.toTM.seq (rewindInput Bool), fun a =>
    hf a ▸ τ.computesTidily (encIn a)⟩

end Transducer

end Turing.MultiTapeTM
