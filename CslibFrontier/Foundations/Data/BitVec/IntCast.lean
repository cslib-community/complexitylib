/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.BitVec

/-!
# Truncation of integer word casts

A Mathlib-bound extension of the core natural-cast truncation API. The signed
integer case also handles negative representatives of modular state intervals.
-/

public section
namespace BitVec

/-- Casting an integer modulo a wider word and then truncating is the narrower cast. -/
theorem setWidth_ofInt_of_le {m p : ℕ} (hp : p ≤ m) (x : ℤ) :
    (BitVec.ofInt m x).setWidth p = BitVec.ofInt p x := by
  cases x with
  | ofNat n => simp [BitVec.ofInt_natCast, BitVec.setWidth_ofNat_of_le hp]
  | negSucc n =>
    simp only [BitVec.ofInt_negSucc_eq_not_ofNat, BitVec.setWidth_not hp,
      BitVec.setWidth_ofNat_of_le hp]

end BitVec
