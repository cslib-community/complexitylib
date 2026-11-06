/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.MPC.OTCommitment.Opening.PolyTime

/-! Actual list checker clients, including every malformed-length direction. -/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment.Tests

open Turing.MultiTapeTM Turing.MultiTapeTM.Encodings

-- The two choices check different components of honest parity-one pairs.
example : openPairs [false, true] [true, true]
    (some (true, [(true, false), (false, true)])) = some true := by decide

-- Consistent selected values do not excuse incorrect parity.
example : openPairs [false] [false] (some (true, [(false, false)])) = none := by decide

-- Consistent parity does not excuse an incorrect selected value.
example : openPairs [true] [false] (some (true, [(false, true)])) = none := by decide

-- Short and long choice vectors are rejected even though every zipped row would pass.
example : openPairs [] [false] (some (false, [(false, false)])) = none := by decide
example : openPairs [false, false] [false] (some (false, [(false, false)])) = none := by decide

-- Short and long answer vectors are rejected too.
example : openPairs [false] [] (some (false, [(false, false)])) = none := by decide
example : openPairs [false] [false, false] (some (false, [(false, false)])) = none := by decide

-- Short and long pair lists must not be silently truncated.
example : openPairs [false] [false] (some (false, [])) = none := by decide
example : openPairs [false] [false]
    (some (false, [(false, false), (false, false)])) = none := by decide

example (choices received : List Bool) : openPairs choices received none = none := rfl
example (b : Bool) : openPairs [] [] (some (b, [])) = some b := rfl

-- The exact bridge handles arbitrary openings, not just honest pairs.
example {k : ℕ} (choices received : Fin k → Bool) (b : Bool) (o : Opening k) :
    openPairs (List.ofFn choices) (List.ofFn received)
      (some (b, List.ofFn fun i => (o i false, o i true))) =
        openResult choices received (some (b, o)) :=
  openPairs_ofFn choices received (some (b, o))

example : ComputableInPolyTime
    (fun input : List Bool × List Bool × Option (Bool × List (Bool × Bool)) =>
      openPairs input.1 input.2.1 input.2.2)
    (encPair encBits (encPair encBits
      (encOption (encPair encBool (encList (encPair encBool encBool))))))
    (encOption encBool) := openPairs_polyTime

end Cslib.Crypto.Protocols.MPC.OTCommitment.Tests
