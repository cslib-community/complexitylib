/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.Data.BitString.Threshold

/-!
# Parity and Hamming weight

The parity of a bit string is the parity of its Hamming weight (`Cslib.parity_eq_decide_weight`),
so parity is a symmetric Boolean function (`Cslib.isSymmetric_parity`). This bridge is kept apart
from both `BitString.Parity` and `BitString.Threshold`, so that neither of them imports the other.

## Main results

* `Cslib.parity_eq_decide_weight`: parity is the parity of the weight.
* `Cslib.isSymmetric_parity`: parity is symmetric.
-/

@[expose] public section

namespace Cslib

/-- Parity is the parity of the weight. -/
theorem parity_eq_decide_weight {n : ℕ} (x : BitString n) :
    parity n x = decide (BitString.weight x % 2 = 1) :=
  rfl

/-- Parity is symmetric. -/
theorem isSymmetric_parity {n : ℕ} : (parity n).IsSymmetric := fun x y h => by
  simp only [BitString.weight] at h
  simp only [parity, parityOn, h]

end Cslib
