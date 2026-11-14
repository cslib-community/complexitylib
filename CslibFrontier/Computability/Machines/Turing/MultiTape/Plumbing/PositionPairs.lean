/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PositionPairsCore

/-!
# Positioning a pair cursor from a binary counter

One fixed finite machine decrements a runtime binary word until underflow and moves the source
head twice after each successful decrement. It preserves every source cell and the old output.
The flag and counter tapes are cleared before returning, with both auxiliary heads at zero.
The amortized clock charges the borrow prefixes and cleanup, not the full width on every round.
-/

public section

namespace Turing.MultiTapeTM.PositionPairs

open Cslib.BitString

/-- Advance by twice the runtime binary index, without testing source cells. -/
noncomputable def machine := guarded fun _ => true

/-- Position the source head at twice the counter value, clearing both auxiliary tapes.
The source need not contain a word long enough to include the final cursor. -/
theorem runsBetween (input source w out : List Bool) :
    RunsBetween machine (config input source w [] 0 out)
      (config input source [] [] (2 * (lsbValue w : ℤ)) out)
      (11 * lsbValue w + 5 * w.length + 13)
      (3 * (11 * lsbValue w + 5 * w.length + 14)) :=
  runsBetween_guarded (fun _ => true) input source w out (lsbValue w) le_rfl
    (fun _ _ => rfl) (Or.inl rfl)

/-- Canonical binary input positions the source at pair `p`, using one uniform finite machine. -/
theorem runsBetween_bits (input source out : List Bool) (p : ℕ) :
    RunsBetween machine (config input source p.bits [] 0 out)
      (config input source [] [] (2 * (p : ℤ)) out)
      (11 * p + 5 * p.bits.length + 13) (3 * (11 * p + 5 * p.bits.length + 14)) := by
  simpa only [lsbValue_bits] using runsBetween input source p.bits out

end Turing.MultiTapeTM.PositionPairs
