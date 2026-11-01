/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeEncode

/-!
# Reading a child label from a packed assignment counter

The interpolation caller supplies its actual binary loop limit and assignment counter. The
limit's binary size pays the zero-padded assignment word. A child label is a stored slice of that
word, with runtime stride, label width and child index. A slice never exceeds its stored source
word; a large binary width cannot allocate its numeric magnitude. No runtime power is
constructed here.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.AssignmentLabels

/-- Actual interpolation limit, assignment counter, padded child stride, label width and child. -/
abbrev Args := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Read one label from the actual counter's padded binary word. -/
@[expose] def label : Args → List Bool := fun (limit, counter, stride, width, child) =>
  ((Turing.MultiTapePTM.BlockComputation.Encoding.NativeEncode.word limit counter).drop
    (child * stride)).take width

end Cslib.TreeEval.Ary.Packed.AssignmentLabels
