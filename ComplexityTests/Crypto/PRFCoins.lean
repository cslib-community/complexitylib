/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.PseudorandomFunction.Coins

/-!
# Tests for pseudorandom coins from a pseudorandom function

Concrete paddings: a short request pads to itself, a `true` and `false`s; the empty request pads
to a leading `true`; two distinct short requests pad differently while a request of the full width
loses its terminator. The coins of the toy family that XORs key and input have the requested length
and are the padded input masked by the key.
-/

namespace ComplexityTests.Crypto.PRFCoins

open Cslib Cslib.Crypto

example : padRequest 6 [true, false] = [true, false, true, false, false, false] := by decide
example : padRequest 4 [] = [true, false, false, false] := by decide
example : padRequest 4 [false] ≠ padRequest 4 [false, false] := by decide
-- A request of the full width is cut before its terminator, so padding is not injective there.
example : padRequest 3 [false, false, false] = padRequest 3 [false, false, false, true] := by decide
example : unpadRequest (padRequest 6 [true, false]) = [true, false] := by decide

/-- A toy family: the key masks the input. -/
def xorFamily (key query : List Bool) : List Bool := List.zipWith xor key query

example : prfCoins xorFamily [true, true, false, false] [false] 3 = [true, false, false] := by
  decide

example : (prfCoins xorFamily [true, true, false, false] [false] 3).length = 3 :=
  length_prfCoins (fun _ _ h => by simp [xorFamily, h]) _ _ (by decide)

-- The coin request word of `([false], 3)` decodes back.
example : coinRequestDecoder.decode (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
    Turing.MultiTapeTM.encUnary ([false], 3)) = ([false], 3) :=
  coinRequestDecoder.decode_enc _

-- The transfer theorem, as an instance.
example {F : List Bool → List Bool → List Bool} (hF : PseudorandomFunction F) :
    Game.Indistinguishable (fun A N => ProbComp.eval (coinRealGame F A N))
      (fun A N => ProbComp.eval (coinIdealGame A N))
      (Probability.IsOraclePPT Turing.MultiTapeTM.encBool) :=
  hF.coinIndistinguishable

end ComplexityTests.Crypto.PRFCoins
