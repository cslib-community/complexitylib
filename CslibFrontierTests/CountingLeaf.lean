/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.CountingLeaf

open Cslib Cslib.CountingLeaf Turing.MultiTapeTM

-- The predicate reads both its explicit context and the decoded candidate index.
private def predicate (p : List Bool × ℕ) : Bool := decide (p.1 = [true] ∧ p.2 = 5)

example : run predicate ⟨[true], 6, 4, [true, false, true], false, 0⟩ = true := by decide
example : run predicate ⟨[true], 6, 4, [false, false, true, false, true], false, 0⟩ = true := by
  decide
example : run predicate ⟨[], 6, 4, [true, false, true], false, 0⟩ = false := by decide
example : run predicate ⟨[true], 5, 4, [true, false, true], false, 0⟩ = false := by decide
example : run predicate ⟨[true], 6, 0, [true, false, true], false, 0⟩ = false := by decide
example : run predicate ⟨[true], 6, 4, [true, false, true], true, 0⟩ = false := by decide
example : run predicate ⟨[true], 6, 4, [true, false, true], false, 1⟩ = false := by decide

example {predicate : List Bool × ℕ → Bool}
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ComputableInPolyTime (run predicate) encInput encBool := computableInPolyTime_run predicate hp

private theorem predicate_native :
    ComputableInPolyTime predicate (encPair encBits encNat) encBool := by
  have hc := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.fst encBits encNat) (ComputableInPolyTime.const [true])
  have hi := ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.snd encBits encNat) (ComputableInPolyTime.const 5)
  exact .of_tidy (ComputableTidilyInPolyTime.decide_and hc.tidy hi.tidy)

example : ComputableInPolyTime (run predicate) encInput encBool :=
  computableInPolyTime_run predicate predicate_native

-- Precision zero and all padding cases are included in the semantic bridge.
example (predicate : List Bool × ℕ → Bool) (q : Input) :
    run predicate q = Circuits.Boolean.CarrySaveQuery.value
      (fun path => Circuits.Boolean.CarrySaveQuery.Counting.leafPair q.count q.width
        (fun j => predicate (q.context, j)) (BitString.binaryValue path))
      ⟨q.path, 0, q.carry, q.bit⟩ := run_eq_value predicate q

-- Framing and the selector bit are included in the serialized length.
example : (encInput ⟨[true], 6, 4, [true, false, true], false, 0⟩).length = 27 := by decide

example : (encInput ⟨[true], 6, 4, [true, false, true], false,
    BitString.lsbValue [false, false]⟩).length ≤ 29 := by
  exact length_encInput_of_counter_le [true] [true, false, true] [false, false] 6 4 false
