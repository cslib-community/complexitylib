/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTakeDropUnary

/-!
# Taking and dropping list elements in linear time

Taking or dropping the first `n` elements of a list encoded by `Turing.MultiTapeTM.encList`, with
`n` in unary, has cost and output degree one. Both are computed by the one-tape machine
`Turing.MultiTapeTM.TakeDropUnary.toTM`, which copies the count to its work tape and then streams
the encoded list once, moving the work head at every element boundary. Folding over the count or
over the list would cost quadratic time.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.takeUnary`: the first `n` elements.
* `Turing.MultiTapeTM.ComputableInDegree.dropUnary`: all but the first `n` elements.
-/

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α : Type}

/-- Taking (`keep = true`) or dropping (`keep = false`) a unary number of elements has cost and
output degree one. -/
private theorem cut (keep : Bool) (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × ℕ => if keep then p.1.take p.2 else p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  of_bounds ⟨5, fun p => by
      dsimp only
      rw [pow_one]
      omega⟩
    ⟨2, fun p => by
      have h := length_le_encPair_right (encList enc) encUnary p
      rw [encUnary_apply, List.length_replicate] at h
      dsimp only
      rw [pow_one]
      omega⟩
    (TakeDropUnary.computableInTimeAndSpace keep enc)

/-- Taking the first `n` elements, with `n` in unary, in linear time. -/
public theorem takeUnary (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × ℕ => p.1.take p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  cut true enc

/-- Dropping the first `n` elements, with `n` in unary, in linear time. -/
public theorem dropUnary (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × ℕ => p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  cut false enc

end Turing.MultiTapeTM.ComputableInDegree
