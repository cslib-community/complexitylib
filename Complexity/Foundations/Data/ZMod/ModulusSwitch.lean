/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Floor

/-!
# Nearest-integer modulus switching

Scale the canonical centered integer representative by the rational ratio of target to source
modulus, round to the nearest integer, and reduce modulo the target. Half-integer ties round
toward positive infinity, as in Mathlib's `round`.

## Main definitions

* `ZMod.modulusSwitch`: the canonical coefficient conversion.

## Main results

* `ZMod.modulusSwitch_intCast`: for nonzero source modulus, any integer representative gives
  the same converted residue, including negative representatives and half-integer ties.

This is a numerical conversion, not a ring homomorphism. The intended source and target moduli
are positive; the definition is total, and representative independence is stated for nonzero
source modulus.
No statement about plaintext preservation, hardness, or computational complexity is made.
-/

public section

namespace ZMod

/-- Nearest-integer scaling from modulus `q` to modulus `p`, using the canonical centered lift.
The rational division is total; representative independence is stated for nonzero source modulus. -/
@[expose] def modulusSwitch (p : ℕ) {q : ℕ} (x : ZMod q) : ZMod p :=
  (round ((p : ℚ) / q * x.valMinAbs) : ℤ)

/-- Rounding after scaling gives the same residue from every integer representative. -/
theorem modulusSwitch_intCast {q p : ℕ} (hq : q ≠ 0) (x : ℤ) :
    modulusSwitch p (x : ZMod q) = (round ((p : ℚ) / q * x) : ℤ) := by
  obtain ⟨k, hk⟩ := (intCast_eq_intCast_iff_dvd_sub _ _ q).mp
    (coe_valMinAbs (x : ZMod q))
  have hx : x = (x : ZMod q).valMinAbs + q * k := by omega
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hs : (p : ℚ) / q * x =
      (p : ℚ) / q * (x : ZMod q).valMinAbs + ((p : ℤ) * k : ℤ) := by
    conv_lhs => rw [hx]
    push_cast
    field_simp
  rw [hs, round_add_intCast]
  simp [modulusSwitch]

end ZMod
