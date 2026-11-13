/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.List.OfFn

/-!
# Raw encoding of fixed-width bit strings

A fixed-width bit string `Cslib.BitString k = Fin k → Bool` is stored as its `k` bits in index
order, without framing: the width is fixed by the type, so no length marker is needed.

## Main definitions

* `Turing.MultiTapeTM.encBitString`: a fixed-width bit string as its raw bit list.

## Main results

* `Turing.MultiTapeTM.encBitString_apply`: the code of `c` is `List.ofFn c`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Encode a fixed-width bit string `BitString k` as its raw bit list `List.ofFn`. -/
def encBitString (k : ℕ) : Cslib.BitString k ↪ List Bool :=
  ⟨List.ofFn, List.ofFn_injective⟩

@[simp]
theorem encBitString_apply (k : ℕ) (c : Cslib.BitString k) :
    encBitString k c = List.ofFn c := rfl

end Turing.MultiTapeTM
