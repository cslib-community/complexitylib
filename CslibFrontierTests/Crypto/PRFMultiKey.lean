/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.PseudorandomFunction.MultiKey

/-!
# Tests for several independent keys of a pseudorandom function

Concrete key blocks: a six-bit key splits into three two-bit blocks, a block past the end of the
key is empty, and blocks of a word of `t` blocks have the block length. With no channels the
multi-key bound sums over no reductions, so the real and ideal multi-key experiments coincide;
with one channel the bound is a single PRF advantage.
-/

namespace ComplexityTests.Crypto.PRFMultiKey

open Cslib Cslib.Crypto

example : keyBlock 2 0 [true, false, false, true, true, true] = [true, false] := by decide
example : keyBlock 2 1 [true, false, false, true, true, true] = [false, true] := by decide
example : keyBlock 2 2 [true, false, false, true, true, true] = [true, true] := by decide
-- A block past the end of the key is empty.
example : keyBlock 2 3 [true, false, false, true, true, true] = [] := by decide

example : (keyBlock 2 1 [true, false, false, true, true, true]).length = 2 :=
  length_keyBlock (t := 3) (by decide) (by decide)

-- Without channels, the real and ideal multi-key experiments are indistinguishable outright.
example {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family)
    (adversary : MultiKeyDistinguisher 0) (n : ℕ) :
    Game.advantage (ProbComp.eval (prfMultiRealGame family 0 adversary n))
      (ProbComp.eval (prfMultiIdealGame 0 adversary n)) = 0 :=
  le_antisymm (by simpa using advantage_prfMultiRealGame_prfMultiIdealGame_le hfamily adversary n)
    zero_le

-- With one channel, the bound is the advantage of the single hybrid reduction.
example {family : List Bool → List Bool → List Bool} (hfamily : PseudorandomFunction family)
    (adversary : MultiKeyDistinguisher 1) (n : ℕ) :
    Game.advantage (ProbComp.eval (prfMultiRealGame family 1 adversary n))
        (ProbComp.eval (prfMultiIdealGame 1 adversary n)) ≤
      Game.advantage (ProbComp.eval (prfRealGame family (prfMultiReduction family 1 0 adversary) n))
        (ProbComp.eval (prfIdealGame (prfMultiReduction family 1 0 adversary) n)) := by
  simpa using advantage_prfMultiRealGame_prfMultiIdealGame_le hfamily adversary n

end ComplexityTests.Crypto.PRFMultiKey
