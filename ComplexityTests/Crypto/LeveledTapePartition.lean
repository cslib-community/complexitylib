/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Crypto.Computational.Homomorphic.Leveled.GuessCoinTape

/-!
# Linear partition of the actual adaptive encryption-game tape

The input contains a raw tape and two variable unary cutoffs. The three resulting blocks are
exactly those read by `publicKeyGameCoins`. This is a charged tape-partition certificate, not a
runtime bound for the callbacks or the complete reduction.
-/

namespace ComplexityTests.Crypto.LeveledTapePartition

open Turing.MultiTapeTM Cslib.Crypto.Homomorphic

private abbrev inputEncoding := encPair encBits (encPair encUnary encUnary)

private def partition (p : List Bool × ℕ × ℕ) : List Bool × List Bool × List Bool :=
  (p.1.take p.2.1, (p.1.drop p.2.1).take p.2.2, (p.1.drop p.2.1).drop p.2.2)

private theorem partition_linear : ComputableInDegree partition inputEncoding
    (encPair encBits (encPair encBits encBits)) 1 1 := by
  have hw := ComputableInDegree.fst encBits (encPair encUnary encUnary)
  have hc := (ComputableInDegree.fst encUnary encUnary).comp
    (ComputableInDegree.snd encBits (encPair encUnary encUnary))
  have he := (ComputableInDegree.snd encUnary encUnary).comp
    (ComputableInDegree.snd encBits (encPair encUnary encUnary))
  have hrest := ComputableInDegree.bitsDrop.comp (hw.prod hc)
  exact (ComputableInDegree.bitsTake.comp (hw.prod hc)).prod
    ((ComputableInDegree.bitsTake.comp (hrest.prod he)).prod
      (ComputableInDegree.bitsDrop.comp (hrest.prod he)))

-- No fixed cutoff or tape-length bound: every unary count and raw word is charged linearly.
example : ComputableInO partition inputEncoding (encPair encBits (encPair encBits encBits))
    (fun p => p.1.length + p.2.1 + p.2.2 + 1)
    (fun p => p.1.length + p.2.1 + p.2.2 + 1) := by
  apply (ComputableInO.of_linear partition_linear).mono 2 <;>
    intro p <;>
    simp only [inputEncoding, length_encPair, encBits_apply, encUnary_apply,
      List.length_replicate] <;> omega

-- This equality checks the real consumer, including the selected message and false tag.
example (choose : (ℕ × List Bool) → List Bool → (Bool × Bool) × List Bool)
    (encrypt : (ℕ × List Bool × Bool) → List Bool → List Bool)
    (guess : (ℕ × List Bool × List Bool) → List Bool → Bool)
    (bit : Bool) (n chooseCoins encCoins : ℕ)
    (artifact : List (List Bool) × List (List (List Bool))) (tape : List Bool) :
    Leveled.publicKeyGameCoins choose encrypt guess bit chooseCoins encCoins (n, artifact) tape =
      let blocks := partition (tape, chooseCoins, encCoins)
      let choice := choose (n, Leveled.encPublicKey artifact) blocks.1
      let ct := encrypt (n, artifact.1.getD 0 [], if bit then choice.1.2 else choice.1.1)
        blocks.2.1
      guess (n, choice.2, false :: ct) blocks.2.2 := rfl

example (tape : List Bool) (chooseCoins encCoins : ℕ) :
    let blocks := partition (tape, chooseCoins, encCoins)
    blocks.1 ++ blocks.2.1 ++ blocks.2.2 = tape := by
  simp [partition, List.append_assoc]

example : partition ([true, false, true], 1, 1) = ([true], [false], [true]) := rfl
example : partition ([true, false], 0, 0) = ([], [], [true, false]) := rfl
example : partition ([true, false], 100, 100) = ([true, false], [], []) := by decide
example : partition ([], 100, 100) = ([], [], []) := by decide

end ComplexityTests.Crypto.LeveledTapePartition
