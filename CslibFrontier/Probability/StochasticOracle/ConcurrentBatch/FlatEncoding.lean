/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.Codec
import Mathlib.Tactic

/-!
# Runtime-list compilation of concurrent batch slots

The original residual selector and the runtime-role routing selector share this
literal serialization identity; their wire formats are unchanged.

## Main definitions

* `encodeSlot`: inactive marker or framed query for one opportunity.

## Main results

* `encodeSlots_flatMap`: the indexed source codec equals a variable-length native list scan.
-/

public section
namespace Cslib.Probability.StochasticOracle.ConcurrentBatch

/-- Encode one inactive marker or one framed active query. -/
@[expose] def encodeSlot : Option Word → Word
  | none => [false]
  | some word => true :: Kolmogorov.selfDelimitingCode word

/-- Slot serialization is a flat native scan in opportunity order. -/
theorem encodeSlots_flatMap (n : ℕ) (f : Fin n → Option Word) :
    encodeSlots n f = (List.ofFn f).flatMap encodeSlot := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.flatMap_cons, encodeSlots, ih]
    cases f 0 <;> rfl

end Cslib.Probability.StochasticOracle.ConcurrentBatch
