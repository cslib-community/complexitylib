/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.CollisionResistant
import Complexity.Crypto.Computational.MerkleDamgard

/-!
# Tests for collision-resistant hash families and the Merkle–Damgård transform

Provides concrete nonvacuous examples of `merkleDamgardChain`, `mdBlocks`, `merkleDamgard`,
`extractChainCollision`, and `extractMerkleDamgardCollision` on an explicit `2n → n` XOR
compression function, and verifies that `CollisionResistant` rejects a trivial constant
compression function via an explicit zero-coin PPT collision finder.
-/

namespace ComplexityTests.Crypto.MerkleDamgard

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete `2n → n` XOR compression function: split `x` into two `k.length`-bit halves (normalized
via `padOrTake k.length`) and XOR them bitwise. -/
def xorCompress (k x : List Bool) : List Bool :=
  (padOrTake k.length (x.take k.length)).zipWith Bool.xor
    (padOrTake k.length (x.drop k.length))

theorem length_xorCompress (k x : List Bool) : (xorCompress k x).length = k.length := by
  simp [xorCompress]

theorem computableInPolyTime_xorCompress :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorCompress p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold xorCompress padOrTake
  polytime

-- Ordinary importing clients can use the plain `ComputableInPolyTime` certificates for
-- `padOrTake`, `mdBlocks`, `merkleDamgard`, `extractMerkleDamgardCollision`,
-- `validCompressionInput`, and `isCollision` directly:
example : ComputableInPolyTime (fun p : ℕ × List Bool => mdBlocks p.1 (padOrTake p.1 p.2))
    (encPair encUnary encBits) (encList encBits) :=
  computableInPolyTime_mdBlocks.comp
    ((ComputableInPolyTime.fst _ _).prod computableInPolyTime_padOrTake)

example : ComputableInPolyTime
    (fun p : ℕ × List Bool × List Bool × List Bool =>
      isCollision xorCompress validCompressionInput p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encUnary (encPair encBits (encPair encBits encBits))) encBool :=
  computableInPolyTime_isCollision computableInPolyTime_xorCompress
    computableInPolyTime_validCompressionInput

example : ComputableInPolyTime (fun p : List Bool × List Bool => merkleDamgard xorCompress p.1 p.2)
    (encPair encBits encBits) encBits :=
  computableInPolyTime_merkleDamgard computableInPolyTime_xorCompress
    (fun k x _ => length_xorCompress k x)

example : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool =>
      extractMerkleDamgardCollision xorCompress p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) (encPair encBits encBits) :=
  computableInPolyTime_extractMerkleDamgardCollision computableInPolyTime_xorCompress
    (fun k x _ => length_xorCompress k x)

-- Block encoding examples at security parameter n = 2:
example : mdBlocks 2 [] = [[false, false]] := rfl

example : mdBlocks 2 [false, true] =
    [[false, false], [true, false], [true, true]] := rfl

-- Concrete Merkle–Damgård collision on `xorCompress` at key `k = [false, false]` (`n = 2`):
-- both `[]` and `[false, false]` hash to `[false, false]`.
example : merkleDamgard xorCompress [false, false] [] = [false, false] := rfl

example : merkleDamgard xorCompress [false, false] [false, false] = [false, false] := rfl

-- `extractMerkleDamgardCollision` deterministically recovers the 4-bit compression collision
-- `([false, false, false, false], [true, false, true, false])`.
example : extractMerkleDamgardCollision xorCompress [false, false] [] [false, false] =
    ([false, false, false, false], [true, false, true, false]) := rfl

example : isCollision xorCompress validCompressionInput 2 [false, false]
    (extractMerkleDamgardCollision xorCompress [false, false] [] [false, false]).1
    (extractMerkleDamgardCollision xorCompress [false, false] [] [false, false]).2 = true :=
  isCollision_extractMerkleDamgardCollision (fun x _ => length_xorCompress [false, false] x)
    (by decide) (by decide) rfl

-- Block-chain collision extraction when the final blocks differ (Boneh–Shoup Theorem 8.3 Case 1):
example : isCollision xorCompress validCompressionInput 2 [false, false]
    (extractChainCollision xorCompress [false, false] [false, false]
      [[false, false]] [[true, false], [true, false]]).1
    (extractChainCollision xorCompress [false, false] [false, false]
      [[false, false]] [[true, false], [true, false]]).2 = true :=
  isCollision_extractChainCollision_of_getLast?_ne
    (fun x _ => length_xorCompress [false, false] x) rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl

-- Block-chain collision extraction when the block lengths are equal (Theorem 8.3 Case 2):
example : isCollision xorCompress validCompressionInput 2 [false, false]
    (extractChainCollision xorCompress [false, false] [false, false]
      [[false, false], [false, false]] [[true, false], [true, false]]).1
    (extractChainCollision xorCompress [false, false] [false, false]
      [[false, false], [false, false]] [[true, false], [true, false]]).2 = true :=
  isCollision_extractChainCollision_of_length_eq
    (fun x _ => length_xorCompress [false, false] x) rfl
    (by decide) (by decide) rfl (by decide) rfl

/-- Trivial keyed hash family that ignores its message and returns the key `k`. -/
def constHash (k _ : List Bool) : List Bool := k

/-- `constHash` is not collision-resistant: outputting `([false], [true])` succeeds with
probability `1` at every security parameter. -/
theorem not_collisionResistant_constHash : ¬ CollisionResistant constHash := by
  let finder : CollisionFinder := fun _ _ => pure ([false], [true])
  have hPPT : IsPPT (encPair encBits encBits) finder := by
    change IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun _ => pure ([false], [true]))
    exact (ComputableInPolyTime.const ([false], [true])).isPPTOn
  refine not_collisionResistantOn_of_le_succProbability one_ne_zero finder hPPT fun n => ?_
  have heval : ProbComp.eval (collisionGame constHash (fun _ _ => true) finder n) =
      PMF.pure true := by
    have hbne : ([false] != [true]) = true := rfl
    simp only [collisionGame, finder, constHash, isCollision, hbne, Bool.and_self,
      beq_self_eq_true, pure_bind, ProbComp.eval_bind, BitString.eval_sampleList,
      ProbComp.eval_pure, PMF.bind_const]
  rw [Game.succProbability, heval, PMF.pure_apply_self, ENNReal.toNNReal_one]

end ComplexityTests.Crypto.MerkleDamgard
