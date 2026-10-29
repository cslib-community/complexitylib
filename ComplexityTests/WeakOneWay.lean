/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Computational.OneWay.Weak

/-!
# Tests for `Complexity.Crypto.Computational.OneWay.Weak`

Concrete nonvacuity, strong-to-weak specialization, fixed-output-length normalization, and
schedule-reindexing tests for `WeakOneWayAt`, `WeakOneWay`, and `OneWayReindex`.
-/

@[expose] public section

namespace Cslib.Crypto.WeakOneWayTests

open Cslib Cslib.Crypto Filter Turing.MultiTapeTM

/-- Composing `OneWay.weakOneWay` with `not_weakOneWay_const` rules out constant strong one-way
functions. -/
example (word : List Bool) : ¬ OneWay (fun _ => word) :=
  fun h => not_weakOneWay_const word h.weakOneWay

/-- The identity function `id` is not weakly one-way. -/
example : ¬ WeakOneWay id :=
  not_weakOneWay_of_inverse (fun _ y => y) (by fun_prop) (fun _ => rfl)

/-- Every strong one-way function is a weak one-way function and yields a normalized weak one-way
function with fixed output length at each input length. -/
example (f : List Bool → List Bool) (hf : OneWay f) :
    WeakOneWay f ∧
      ∃ (g : List Bool → List Bool) (length : ℕ → ℕ),
        WeakOneWay g ∧
        (∀ input, (g input).length = length input.length) ∧
        ComputableInPolyTime length encUnary encUnary :=
  ⟨hf.weakOneWay, hf.weakOneWay.exists_fixedOutputLength⟩

/-- Concrete evaluation of `OneWayReindex.reindex` on the schedule `m n = n + 1` and identity core
`core _ x = x`: on an input `[true, false, true]` of length `3`, the selected parameter is `2` and
the output wraps `(2, [true, false, true])`. -/
example :
    OneWayReindex.reindex (fun n => n + 1) (fun _ x => x) [true, false, true] =
      OneWayReindex.wrappedImage 2 [true, false, true] := by
  decide

end Cslib.Crypto.WeakOneWayTests
