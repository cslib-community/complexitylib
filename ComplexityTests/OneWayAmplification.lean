/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Computational.OneWay.Amplification

/-!
# Tests for `Complexity.Crypto.Computational.OneWay.Amplification`

Concrete evaluation tests for `parallelCore`, `BitString.replaceRow`, and `plantedImage`, and
type-checking tests for Yao's weak-to-strong one-way function hardness amplification
(`WeakOneWay.exists_oneWay`, `exists_oneWay_of_exists_weakOneWay`,
`exists_oneWay_iff_exists_weakOneWay`).
-/

@[expose] public section

namespace Cslib.Crypto.OneWayAmplificationTests

open Cslib Cslib.BitString Cslib.Crypto Cslib.Crypto.OneWayAmplification

/-- Concrete evaluation of `parallelCore` on `k n = 2` blocks of width `w n = 2` under bit-reversal:
`[true, false, false, true]` splits into `[true, false]` and `[false, true]`, whose reversals
concatenate to `[false, true, true, false]`. -/
example :
    parallelCore (fun _ => 2) (fun _ => 2) List.reverse 0 [true, false, false, true] =
      [false, true, true, false] := by
  decide

/-- Concrete evaluation of `replaceRow` and `plantedImage`: replacing block `1` of
`[true, false, false, true]` with `[true, true]` yields `[true, false, true, true]`, and planting
`List.reverse [true, true]` in slot `1` matches `parallelCore` on the replaced word. -/
example :
    replaceRow 2 2 1 [true, true] [true, false, false, true] = [true, false, true, true] ∧
      plantedImage (fun _ => 2) (fun _ => 2) List.reverse 0
        1 (List.reverse [true, true]) [true, false, false, true] =
        parallelCore (fun _ => 2) (fun _ => 2) List.reverse 0 [true, false, true, true] := by
  decide

/-- Yao's hardness amplification: weak and strong one-way functions are existentially equivalent,
and any concrete weak one-way function amplifies to a polynomial-time computable strong one-way
function. -/
example (f : List Bool → List Bool) (hf : WeakOneWay f) :
    (∃ F : List Bool → List Bool,
      OneWay F ∧ Turing.MultiTapeTM.ComputableInPolyTime F
        Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits) ∧
      ((∃ F : List Bool → List Bool, OneWay F) ↔ (∃ g : List Bool → List Bool, WeakOneWay g)) := by
  obtain ⟨F, hF⟩ := hf.exists_oneWay
  exact ⟨⟨F, hF, hF.polyTime⟩, exists_oneWay_iff_exists_weakOneWay⟩

end Cslib.Crypto.OneWayAmplificationTests
