/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Tactic.PolyTime

/-! Unary indexed enumeration of lists, including empty and repeated entries. -/

namespace ComplexityTests.ListZipIdx

open Turing.MultiTapeTM

example : ([] : List Bool).zipIdx = [] := rfl
example : [false, true, false].zipIdx = [(false, 0), (true, 1), (false, 2)] := rfl

example (empty : Empty ↪ List Bool) : ComputableTidilyInPolyTime
    (fun list : List Empty => list.zipIdx) (encList empty)
    (encList (encPair empty encUnary)) := by fun_prop

example {α Input : Type} (enc : α ↪ List Bool) (input : Input ↪ List Bool)
    (list : Input → List α) (hlist : ComputableTidilyInPolyTime list input (encList enc)) :
    ComputableTidilyInPolyTime (fun x => let values := list x; values.zipIdx)
      input (encList (encPair enc encUnary)) := by
  fail_if_success (clear hlist; fun_prop)
  polytime

-- Framing supplies the length; no element decoder or computational hypothesis is needed.
example {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun list : List α => list.length) (encList enc) encUnary := by
  fun_prop

example (empty : Empty ↪ List Bool) :
    ComputableInPolyTime (fun list : List Empty => list.length) (encList empty) encUnary := by
  fun_prop

-- The list may be computed from the complete caller context.
example {α Input : Type} (enc : α ↪ List Bool) (input : Input ↪ List Bool)
    (list : Input → List α) (hlist : ComputableInPolyTime list input (encList enc)) :
    ComputableInPolyTime (fun x => (list x).length) input encUnary := by
  fail_if_success (clear hlist; fun_prop)
  fun_prop

end ComplexityTests.ListZipIdx
