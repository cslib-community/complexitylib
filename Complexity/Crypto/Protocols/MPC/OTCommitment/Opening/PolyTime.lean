/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.Opening
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Native polynomial-time checking of list openings

## Main results

* `OTCommitment.openPairs_polyTime`: the total checker is polynomial time with raw choice/answer
  bit strings and a framed list of opening pairs. All inputs and the optional result are charged.

The certificate is uniform in the list lengths and rejects malformed lengths without any
well-formedness hypothesis. It is not a certificate for an arbitrary sender or simulator.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Turing.MultiTapeTM Turing.MultiTapeTM.Encodings

/-- Native polynomial-time verification of explicit openings, including exact-length rejection. -/
theorem openPairs_polyTime :
    ComputableInPolyTime
      (fun input : List Bool × List Bool × Option (Bool × List (Bool × Bool)) =>
        openPairs input.1 input.2.1 input.2.2)
      (encPair encBits (encPair encBits
        (encOption (encPair encBool (encList (encPair encBool encBool))))))
      (encOption encBool) := by
  let encPairs := encList (encPair encBool encBool)
  let encSubmission := encPair encBool encPairs
  let encInput := encPair encBits (encPair encBits (encOption encSubmission))
  have hinput := ComputableInPolyTime.fst encInput encSubmission
  have hvalue := ComputableInPolyTime.snd encInput encSubmission
  have hchoices := (ComputableInPolyTime.fst encBits
    (encPair encBits (encOption encSubmission))).comp hinput
  have hreceived := ((ComputableInPolyTime.fst encBits (encOption encSubmission)).comp
    (ComputableInPolyTime.snd encBits (encPair encBits (encOption encSubmission)))).comp hinput
  have hbit := (ComputableInPolyTime.fst encBool encPairs).comp hvalue
  have hpairs := (ComputableInPolyTime.snd encBool encPairs).comp hvalue
  have hzip := (ComputableInPolyTime.zip encBool encBool).comp
    (((bits_encList_polyTime encBool).1.comp hchoices).prod
      ((bits_encList_polyTime encBool).1.comp hreceived))
  have hrows := (ComputableInPolyTime.zip (encPair encBool encBool)
    (encPair encBool encBool)).comp (hzip.prod hpairs)
  have htest : ComputableInPolyTime
      (fun p : Bool × ((Bool × Bool) × (Bool × Bool)) =>
        (p.2.2.1 ^^ p.2.2.2) == p.1 &&
          (if p.2.1.1 then p.2.2.2 else p.2.2.1) == p.2.1.2)
      (encPair encBool (encPair (encPair encBool encBool) (encPair encBool encBool)))
      encBool := ComputableInPolyTime.of_finite _
  have hall := ComputableInPolyTime.allWithEncoding htest hbit hrows
  have hlen := ((ComputableInPolyTime.length_bits.comp hchoices).beq
      (ComputableInPolyTime.length_bits.comp hreceived)).bool_and'
    ((ComputableInPolyTime.length_bits.comp hchoices).beq
      ((ComputableInPolyTime.length_list (encPair encBool encBool)).comp hpairs))
  have hbody := (hlen.bool_and' hall).ite
    ((ComputableInPolyTime.optionSome encBool).comp hbit) (ComputableInPolyTime.const none)
  unfold openPairs
  exact ComputableInPolyTime.optionElimWithInput
    ((ComputableInPolyTime.snd encBits (encOption encSubmission)).comp
      (ComputableInPolyTime.snd encBits (encPair encBits (encOption encSubmission))))
    (ComputableInPolyTime.const none) hbody

end Cslib.Crypto.Protocols.MPC.OTCommitment
