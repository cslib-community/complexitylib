/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Plain comparison rules for signed-binary integers

Composition rules for the order of two computed integers in the signed-binary encoding
`encIntBin`. They are plain `ComputableInPolyTime` statements, proved by `fun_prop` on the pair
comparison and `ComputableInPolyTime.comp`, so clients outside the machine layer can compare
integers without a local tidy bridge.

## Main results

* `ComputableInPolyTime.intBin_le'`, `ComputableInPolyTime.intBin_lt'`: compare two computed
  signed-binary integers.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Compare two computed signed-binary integers with `≤`. -/
@[fun_prop]
theorem intBin_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  (show ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 ≤ p.2)) (encPair encIntBin encIntBin)
    encBool by fun_prop).comp (hleft.prod hright)

/-- Compare two computed signed-binary integers with `<`. -/
@[fun_prop]
theorem intBin_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool :=
  (show ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 < p.2)) (encPair encIntBin encIntBin)
    encBool by fun_prop).comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime
