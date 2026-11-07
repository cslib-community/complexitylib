/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! The stronger certificates preserve both encodings and the existing polynomial clients. -/

open Turing.MultiTapeTM

example : ComputableInDegree (fun word : List Bool => word)
    encBits (encList encBool) 1 1 := ComputableInDegree.bitsToList

example : ComputableInDegree (fun word : List Bool => word)
    (encList encBool) encBits 1 1 := ComputableInDegree.listToBits

example : ComputableInDegree (fun p : List Bool × ℕ => p.1.take p.2)
    (encPair encBits encUnary) encBits 1 1 := ComputableInDegree.bitsTake

example : ComputableInDegree (fun p : List Bool × ℕ => p.1.drop p.2)
    (encPair encBits encUnary) encBits 1 1 := ComputableInDegree.bitsDrop

example : encList encBool [false, true] = [true, false, false, true, true, false] := rfl

example : ([] : List Bool).take 100 = [] ∧ ([] : List Bool).drop 100 = [] := by decide

example : [false, true].take 0 = [] ∧ [false, true].drop 0 = [false, true] := by decide

example : [false, true].take 100 = [false, true] ∧ [false, true].drop 100 = [] := by decide

example : [false, true, false].take 2 = [false, true] ∧
    [false, true, false].drop 2 = [false] := by decide

example {α : Type} {input : α ↪ List Bool} {word : α → List Bool} {count : α → ℕ}
    (hw : ComputableInPolyTime word input encBits)
    (hc : ComputableInPolyTime count input encUnary) :
    ComputableInPolyTime (fun a => ((word a).take (count a), (word a).drop (count a)))
      input (encPair encBits encBits) :=
  (ComputableInPolyTime.bitsTakeWithInput hw hc).prod
    (ComputableInPolyTime.bitsDropWithInput hw hc)
