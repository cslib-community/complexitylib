/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.MerkleTree
import Complexity.Tactic.PolyTime

/-!
# Tests for Merkle trees

Concrete runs of `merkleRoot`, `merklePath` and `merkleRootOfPath` on a three-leaf tree, padded to
four leaves, under a truncating keyed hash; the two openings a verifier must reject by checking the
path length and the position range; and collision extraction from two forged openings of one
position, at the leaf level and one level up.
-/

namespace ComplexityTests.Crypto.MerkleTree

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- A toy keyed hash: the first `k.length` bits of the input, padded with `false`. It has many
collisions, which the extraction tests below use. -/
def truncHash (k x : List Bool) : List Bool :=
  (x ++ List.replicate k.length false).take k.length

theorem length_truncHash (k x : List Bool) : (truncHash k x).length = k.length := by
  simp [truncHash]

theorem computableInPolyTime_truncHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => truncHash p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold truncHash
  polytime

/-- The certificates apply to the toy hash. -/
example : ComputableInPolyTime (fun p : List Bool × List (List Bool) × ℕ =>
    merklePath truncHash p.1 p.2.1 p.2.2) (encPair encBits (encPair (encList encBits) encUnary))
    (encList encBits) :=
  computableInPolyTime_merklePath computableInPolyTime_truncHash length_truncHash

/-- A three-leaf tree has depth two; the missing fourth leaf reads as `[]`. -/
def key : List Bool := [true, false, true]
def leaves : List (List Bool) := [[true], [false, true], [true, true, false]]

example : (merkleLevel truncHash key leaves 0).length = 4 := by decide
example : merkleLeafLevel truncHash key leaves =
    [[true, false, false], [false, true, false], [true, true, false], [false, false, false]] := by
  decide
example : (merklePath truncHash key leaves 2).length = 2 := by decide

-- Every position, including the padding position `3`, opens to the root.
example : ∀ i < 4,
    merkleRootOfPath truncHash key (leaves.getD i []) i (merklePath truncHash key leaves i) =
      merkleRoot truncHash key leaves := by
  decide

/-! ### What a verifier must check -/

-- Without a fixed path length, the hash input of an internal node opens as a leaf: here the
-- root's own input at position `0` with the empty path.
example : merkleRootOfPath truncHash key
    (encPair encBits encBits ((merkleLevel truncHash key leaves 1).getD 0 [],
      (merkleLevel truncHash key leaves 1).getD 1 [])) 0 [] = merkleRoot truncHash key leaves := by
  decide

-- Without a range check, position `1 + 4` reuses the opening of position `1`.
example : merkleRootOfPath truncHash key (leaves.getD 1 []) (1 + 4)
    (merklePath truncHash key leaves 1) = merkleRoot truncHash key leaves := by
  decide

/-! ### Collision extraction -/

-- Two leaves that agree on their first two bits collide under `truncHash` with a two-bit key.
example : extractMerkleCollision truncHash [false, false] [true, true, false] [true, true, true] 0
    [[false, true]] [[false, true]] = ([true, true, false], [true, true, true]) := by
  decide

-- Different leaf nodes `[true, false]` and `[true, true]` whose paired inputs collide one level up:
-- the extracted pair is the two level-one inputs.
example : merkleRootOfPath truncHash [false, false] [true, false] 0 [[false, false]] =
    merkleRootOfPath truncHash [false, false] [true, true] 0 [[false, false]] := by
  decide

example : isCollision truncHash (fun _ _ => true) 2 [false, false]
    (extractMerkleCollision truncHash [false, false] [true, false] [true, true] 0
      [[false, false]] [[false, false]]).1
    (extractMerkleCollision truncHash [false, false] [true, false] [true, true] 0
      [[false, false]] [[false, false]]).2 = true :=
  isCollision_extractMerkleCollision 2 rfl (by decide) (by decide)

example : (extractMerkleCollision truncHash [false, false] [true, false] [true, true] 0
    [[false, false]] [[false, false]]).1 ≠ [true, false] := by
  decide

end ComplexityTests.Crypto.MerkleTree
