/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.InPlace

/-!
# Doubling bits

`Turing.MultiTapeTM.doubled` is defined with the in-place universal machine, which reads a framed
input through it. This module adds facts about concatenated and replicated words, and the work
space of doubling.

## Main results

* `Turing.MultiTapeTM.doubled_inSpace`: doubling bits uses linear work space.
* `Turing.MultiTapeTM.doubled_flatten`, `Turing.MultiTapeTM.doubled_doubled_replicate`:
  doubling a concatenation or a replicated word.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Doubling one false bit gives its marker followed by `false`. -/
@[simp] theorem doubled_false : doubled [false] = [true, false] := rfl

/-- Doubling commutes with concatenating a list of words. -/
theorem doubled_flatten (L : List (List Bool)) :
    doubled L.flatten = (L.map doubled).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

/-- Two layers of doubling turn each true bit into four true bits. -/
theorem doubled_doubled_replicate (n : ℕ) :
    doubled (doubled (List.replicate n true)) =
      (List.replicate n [true, true, true, true]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, doubled, ← ih]

private def doubledTransducer : Transducer Bool Unit :=
  { Encodings.frameT with final := fun _ => [], length_final_le := fun _ => by simp }

private theorem doubledTransducer_run (l : List Bool) :
    doubledTransducer.run () l = doubled l := by
  induction l with
  | nil => rfl
  | cons b l ih => exact congrArg (true :: b :: ·) ih

/-- Doubling the bits with framing markers uses linear work space. -/
theorem doubled_inSpace :
    ComputableTidilyInSpace doubled encBits encBits fun l => (encBits l).length :=
  ComputableTidilyInSpace.of_inO (.of_linear
    (doubledTransducer.computableTidilyInLinearTimeAndSpace fun l =>
      (doubledTransducer_run l).symm))

end Turing.MultiTapeTM
