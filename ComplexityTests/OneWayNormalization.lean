/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.OneWay.Normalize
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PPT

/-! Padding and normalization tests, including overlong words and wrong-length candidates. -/

namespace ComplexityTests.OneWayNormalization

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

-- Use exactly the existing pair encoding; there is no second framing convention.
example (bound : ℕ) (word : List Bool) :
    BitString.padWord bound word =
      encPair encBits encBits (word, List.replicate (2 * (bound - word.length)) false) := rfl

example : BitString.padWord 0 [] = [false] ∧
    BitString.padWord 0 [true] = [true, true, false] ∧
    BitString.padWord 1 [] = [false, false, false] ∧
    BitString.padWord 1 [false] = [true, false, false] := by decide

example : BitString.padWord 0 [false] ≠ BitString.padWord 1 [] := by decide

example (word : List Bool) : BitString.padWord 0 word = frame word := by
  simp [BitString.padWord]

-- Computed bounds work with either input encoding, including bounds too small for the word.
example : ComputableInPolyTime
    (fun word : List Bool => BitString.padWord (word.length - 3) word) encBits encBits := by
  fun_prop

example : ComputableInPolyTime
    (fun word : List Bool => BitString.padWord (word.length - 3) word)
    (encList encBool) encBits := by polytime

example : ComputableInPolyTime
    (fun word : List Bool => frame word ++
      List.replicate (2 * ((word.length - 3) - word.length)) false) encBits encBits := by
  fun_prop

-- A function with genuinely variable output length acquires an output width depending only on n.
private def keepTrue (word : List Bool) : List Bool := word.filter id

example : ComputableInPolyTime (OneWayNormalization.normalize keepTrue id)
    encBits encBits := by
  fun_prop [keepTrue]

example : (OneWayNormalization.normalize keepTrue id [true, false]).length = 5 ∧
    (OneWayNormalization.normalize keepTrue id [false, false]).length = 5 := by decide

example (adversary : Inverter) (h : IsPPT encBits adversary) :
    IsPPT encBits (fun n image => adversary n (BitString.padWord (n ^ 2 + 3) image)) := by
  ppt

-- The security transfer is an inequality: wrong-length candidates may fail after normalization
-- even when they invert the original function.
example : Game.succProbability (ProbComp.eval (inversionGame
    (OneWayNormalization.normalize (fun _ => []) id) (fun _ _ => pure []) 1)) = 0 := by
  simp [inversionGame, OneWayNormalization.normalize, BitString.sampleList,
    BitString.padWord, Game.succProbability, frame]

example : Game.succProbability (ProbComp.eval (inversionGame
    (fun _ => []) (fun _ _ => pure []) 1)) = 1 := by
  simp [inversionGame, Game.succProbability]

example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), OneWay g ∧
      (∀ input, (g input).length = length input.length) ∧
      ComputableInPolyTime length encUnary encUnary := hf.exists_fixedOutputLength

end ComplexityTests.OneWayNormalization
