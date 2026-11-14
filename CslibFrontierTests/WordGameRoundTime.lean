/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordGameRoundTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime

namespace CslibFrontierTests.WordGameRoundTime

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.WordGameRound

private def update (p : Bool × Bool) : Option Bool × Bool :=
  (if p.2 then some p.1 else none, p.1 != p.2)

-- Both moves change physical metadata; the old metadata determines terminal versus live control.
-- One actual finite machine preserves an arbitrary host input and emitted-output prefix.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 4) Bool S) (c d : ℕ),
    ∀ (input out : List Bool) (player move current : Bool),
      tm.runFrom ((config k input [player, move] [current] out).withState (some tm.q₀))
        (c * 2 ^ d) =
        (config k input (if current then [move, false] else []) [move != current] out).withState
          none := by
  obtain ⟨k, S, hS, tm, c, d, h⟩ := exists_round encBool update
    (ComputableInPolyTime.of_finite update)
  refine ⟨k, S, hS, tm, c, d, ?_⟩
  intro input out player move current
  have hr := h input out player move current
  cases current <;> simpa [update, wordGameHeader] using hr

end CslibFrontierTests.WordGameRoundTime
