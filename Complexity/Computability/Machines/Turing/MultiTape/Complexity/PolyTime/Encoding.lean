/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Exposing encoded outputs as words

Plain polynomial-time computations can return their encoded output without decoding it again.
These rules let clients compose typed computations with word-level machine interfaces.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.encode`: expose the input encoding as a word.
* `Turing.MultiTapeTM.ComputableInPolyTime.encoded`: expose a computation's encoded output.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Expose an already encoded input as a raw word; no inverse for the encoding is required. -/
@[fun_prop] theorem encode {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime enc enc encBits :=
  .of_tidy (ComputableTidilyInPolyTime.encode enc)

/-- The output encoding of a plain polynomial-time computation is itself efficiently produced. -/
@[fun_prop] theorem encoded {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {f : α → β} (h : ComputableInPolyTime f input output) :
    ComputableInPolyTime (fun a => output (f a)) input encBits :=
  (encode output).comp h

end Turing.MultiTapeTM.ComputableInPolyTime
