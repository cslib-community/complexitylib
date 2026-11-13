/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Foundations.Data.BitString.List.Dot
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Polynomial-time inner products of bit lists

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.bitsListDot`,
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsListDot`: the inner product of two computed
  raw words is polynomial time.
-/

public section

/-- The inner product of two tidily computed raw words is tidily polynomial time. -/
@[fun_prop]
theorem Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsListDot {α : Type}
    {input : α ↪ List Bool} {left right : α → List Bool}
    (hleft : ComputableTidilyInPolyTime left input encBits)
    (hright : ComputableTidilyInPolyTime right input encBits) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listDot (left a) (right a)) input
      encBool := by
  unfold Cslib.BitString.listDot
  fun_prop

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- The inner product of two computed raw words is polynomial time. -/
@[fun_prop]
theorem bitsListDot {α : Type} {input : α ↪ List Bool} {left right : α → List Bool}
    (hleft : ComputableInPolyTime left input encBits)
    (hright : ComputableInPolyTime right input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.listDot (left a) (right a)) input encBool := by
  unfold Cslib.BitString.listDot
  polytime

end Turing.MultiTapeTM.ComputableInPolyTime
