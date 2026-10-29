/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.MerkleDamgard
import Complexity.Crypto.Computational.MerkleTree.Binding
import Complexity.Tactic.PPT

/-!
# Tests for Merkle-tree verification and position binding

Under a hash that returns its message, the three-leaf tree's honest openings are accepted, while a
wrong leaf, a short path and an out-of-range position are rejected, and the length check rejects a
pair of child labels posing as a leaf one level up. Under a toy XOR hash, which
reads only a prefix of its input, an honest path also opens a position to a wrong leaf; this
binding break yields a collision through the reduction. Under a hash that ignores its message, an
efficient adversary breaks position binding at every parameter, so `MerklePositionBinding` is not
vacuous.
-/

namespace ComplexityTests.Crypto.MerkleBinding

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- Three leaves of different lengths, in a tree of depth two. -/
abbrev leaves : List (List Bool) := [[true], [false, true], [true, true]]

/-- The key at security parameter `2`. -/
abbrev key : List Bool := [false, true]

/-! ### Verification under an injective hash -/

/-- A hash that returns its message: no collisions, so only honest openings are accepted. -/
def idHash (_ x : List Bool) : List Bool := x

-- All four positions of the padded depth-two tree are accepted with their computed paths.
example : ∀ i : Fin 4,
    merkleVerify idHash key 2 (merkleRoot idHash key leaves) i (leaves.getD i [])
      (merklePath idHash key leaves i) = true := by decide

-- A wrong leaf at position `1` is rejected.
example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 1 [true, true]
    (merklePath idHash key leaves 1) = false := by decide

-- A truncated path is rejected (its recomputed root differs too; `pairLeaf` below isolates the
-- length check).
example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 1 [false, true]
    (merklePath idHash key leaves 1).tail = false := by decide

-- A position outside the depth-two tree is rejected, though its path recomputes the root.
example : merkleRootOfPath idHash key [true] 4 (merklePath idHash key leaves 0) =
    merkleRoot idHash key leaves := by decide

example : merkleVerify idHash key 2 (merkleRoot idHash key leaves) 4 [true]
    (merklePath idHash key leaves 0) = false := by decide

/-- The pair of the two leaf labels of the tree over `[[true], [false]]`, as one word. -/
abbrev pairLeaf : List Bool := encPair encBits encBits (idHash key [true], idHash key [false])

-- Leaves and internal nodes share the hash, so this pair, as a leaf with the empty path,
-- recomputes the root of the depth-one tree over `[[true], [false]]`.
example : merkleRootOfPath idHash key pairLeaf 0 [] = merkleRoot idHash key [[true], [false]] := by
  decide

-- The length check rejects it at depth one, the depth of that tree.
example : merkleVerify idHash key 1 (merkleRoot idHash key [[true], [false]]) 0 pairLeaf [] =
    false := by decide

/-! ### A binding break and its collision -/

/-- A toy keyed hash, the XOR of the first two `k.length`-bit blocks of its input (each padded or
truncated to `k.length` bits). It ignores the rest of its input. -/
def xorHash (k x : List Bool) : List Bool :=
  (padOrTake k.length (x.take k.length)).zipWith Bool.xor
    (padOrTake k.length (x.drop k.length))

theorem length_xorHash (k x : List Bool) : (xorHash k x).length = k.length := by
  simp [xorHash]

theorem computableInPolyTime_xorHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => xorHash p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold xorHash padOrTake
  polytime

/-- Position `1` of the tree over `leaves` under `xorHash`, opened by its honest path both to its
leaf `[false, true]` and to `[true, true]`. -/
abbrev breakOut : MerkleBindingOutput :=
  ((merkleRoot xorHash key leaves, 1), ([false, true], merklePath xorHash key leaves 1),
    ([true, true], merklePath xorHash key leaves 1))

example : merkleBreaksBinding xorHash key breakOut = true := by decide

-- The two openings first differ in the hash inputs one level below the root.
example : extractMerkleCollision xorHash key [false, true] [true, true] 1
    (merklePath xorHash key leaves 1) (merklePath xorHash key leaves 1) =
      ([true, true, true, false, false, false, true],
        [true, true, true, false, false, true, true]) := by decide

example : isCollision xorHash (fun _ _ => true) 2 key
    (extractMerkleCollision xorHash key [false, true] [true, true] 1
      (merklePath xorHash key leaves 1) (merklePath xorHash key leaves 1)).1
    (extractMerkleCollision xorHash key [false, true] [true, true] 1
      (merklePath xorHash key leaves 1) (merklePath xorHash key leaves 1)).2 = true :=
  isCollision_of_merkleBreaksBinding (out := breakOut) (by decide) 2

/-! ### Position binding is not vacuous -/

/-- A keyed hash that ignores its message. -/
def constHash (k _ : List Bool) : List Bool := k

/-- The adversary that opens position `0` of the depth-zero tree with root `k` to `[false]` and to
`[true]`. -/
def constBreaker : MerkleBindingAdversary := fun _ k => pure ((k, 0), ([false], []), ([true], []))

theorem isPPT_constBreaker : IsPPT encMerkleBindingOutput constBreaker := by
  unfold constBreaker
  ppt

-- The reduction applies to this adversary for an efficient length-preserving hash.
example : IsPPT (encPair encBits encBits) (merkleCollisionFinder xorHash constBreaker) :=
  isPPT_merkleCollisionFinder computableInPolyTime_xorHash length_xorHash isPPT_constBreaker

/-- Merkle trees over `constHash` are not position-binding: `constBreaker` wins at every
parameter. -/
theorem not_merklePositionBinding_constHash : ¬ MerklePositionBinding constHash := by
  intro h
  have hwin (n : ℕ) :
      1 ≤ Game.succProbability (ProbComp.eval (merkleBindingGame constHash constBreaker n)) := by
    have hbne : ([false] != [true]) = true := rfl
    have heval :
        ProbComp.eval (merkleBindingGame constHash constBreaker n) = PMF.pure true := by
      simp only [merkleBindingGame, constBreaker, merkleBreaksBinding, merkleVerify,
        merkleRootOfPath, constHash, pure_bind,
        ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure]
      simp [hbne]
    rw [Game.succProbability, heval, PMF.pure_apply_self, ENNReal.toNNReal_one]
  exact not_negligible_const one_ne_zero
    (negligible_of_le (h.negligible constBreaker isPPT_constBreaker) hwin)

-- Compression families give position-binding Merkle trees and PPT collision finders
-- through Merkle–Damgård.
example {h : List Bool → List Bool → List Bool} (hh : CompressionFamily h) :
    MerklePositionBinding (merkleDamgard h) ∧
      IsPPT (encPair encBits encBits)
        (merkleCollisionFinder (merkleDamgard h) constBreaker) :=
  ⟨hh.hashFamily_merkleDamgard.merklePositionBinding,
    isPPT_merkleCollisionFinder hh.hashFamily_merkleDamgard.polyTime
      hh.hashFamily_merkleDamgard.length_eq isPPT_constBreaker⟩

end ComplexityTests.Crypto.MerkleBinding
