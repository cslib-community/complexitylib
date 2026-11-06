/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives

/-!
# Linear conversion between raw and framed Boolean lists

The values are unchanged: only the existing encodings differ. Framing followed by a finite-state
transducer inserts a delimiter after each bit; a second transducer removes those delimiters.
Both directions have linear time, workspace and output length, without a fold over growing words.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.bitsToList`: raw bits to framed Boolean elements.
* `Turing.MultiTapeTM.ComputableInDegree.listToBits`: framed Boolean elements to raw bits.
-/

namespace Turing.MultiTapeTM.ComputableInDegree

/-- Convert one framed word into a list of framed one-bit words. -/
private def frameBitsT : Transducer Bool Bool where
  q₀ := false
  step q b := if q then (false, [b, false]) else (b, if b then [true] else [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> decide
  length_final_le _ := by decide

private theorem frameBitsT_run (word : List Bool) :
    frameBitsT.run false (frame word) = encList encBool word := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    change true :: b :: false :: frameBitsT.run false (frame word) = _
    rw [ih]
    rfl

/-- Read the payload of each three-symbol Boolean element. -/
private def listBitsT : Transducer Bool (Fin 3) where
  q₀ := 0
  step q b := if q = 0 then (1, []) else if q = 1 then (2, [b]) else (0, [])
  final _ := []
  length_step_le q b := by split_ifs <;> simp
  length_final_le _ := by decide

private theorem listBitsT_run (word : List Bool) :
    listBitsT.run 0 (encList encBool word) = word := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    change b :: listBitsT.run 0 (encList encBool word) = _
    rw [ih]

/-- Convert raw bits to the existing framed Boolean-list encoding in linear time and space. -/
public theorem bitsToList : ComputableInDegree (fun word => word)
    encBits (encList encBool) 1 1 := by
  have hframe : ComputableInDegree (fun word : List Bool => word)
      encBits (encFramed encBits) 1 1 := of_frame fun _ => rfl
  have hconvert : ComputableInDegree (fun word : List Bool => word)
      (encFramed encBits) (encList encBool) 1 1 :=
    of_transducer frameBitsT fun word => (frameBitsT_run word).symm
  exact hconvert.comp hframe

/-- Remove Boolean-element framing in linear time and space, leaving the list unchanged. -/
public theorem listToBits : ComputableInDegree (fun word => word)
    (encList encBool) encBits 1 1 :=
  of_transducer listBitsT fun word => (listBitsT_run word).symm

end Turing.MultiTapeTM.ComputableInDegree
