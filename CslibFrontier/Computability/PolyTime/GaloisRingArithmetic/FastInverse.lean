/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.GaloisRingArithmetic
public import Mathlib.Data.Nat.Log

/-!
# Logarithmically many Newton rounds

The existing coefficient-list arithmetic uses `p` Newton rounds for precision `p`. Defect
squaring only needs `Nat.clog 2 p` rounds. This module supplies that implementation and reuses
the general Newton invariant to prove it has the same ring value as the existing inverse.
The seed hypothesis is unchanged, including at precisions zero and one.

This counts Newton rounds, not machine steps or Boolean-query depth. The seed, ring
multiplication, and local arithmetic evaluation still require their own resource certificates.
-/

@[expose] public section

namespace Cslib.GaloisRingArith

/-- Inversion with ceiling-logarithmically many Newton rounds, from the existing seed. -/
def fastInv (p : ℕ) (fl x : List ℕ) : List ℕ :=
  (List.range (Nat.clog 2 p)).foldl (fun y _ => newton p fl x y) (seed p fl x)

/-- Logarithmically many Newton rounds suffice under the existing modulo-two seed condition. -/
theorem val_mul_fastInv {p : ℕ} {fl : List ℕ} (x : List ℕ) {w : Ring p fl}
    (h : val p fl x * val p fl x ^ (2 ^ fl.length - 2) = 1 + 2 * w) :
    val p fl x * val p fl (fastInv p fl x) = 1 :=
  val_mul_newton_rounds_eq_one x h (Nat.clog 2 p) (Nat.le_pow_clog (by decide) p)

/-- The accelerated and original implementations represent the same inverse. -/
theorem val_fastInv_eq_inv {p : ℕ} {fl : List ℕ} (x : List ℕ) {w : Ring p fl}
    (h : val p fl x * val p fl x ^ (2 ^ fl.length - 2) = 1 + 2 * w) :
    val p fl (fastInv p fl x) = val p fl (inv p fl x) := by
  calc
    val p fl (fastInv p fl x) = val p fl (fastInv p fl x) *
        (val p fl x * val p fl (inv p fl x)) := by rw [val_mul_inv x h, mul_one]
    _ = (val p fl x * val p fl (fastInv p fl x)) * val p fl (inv p fl x) := by ring
    _ = val p fl (inv p fl x) := by rw [val_mul_fastInv x h, one_mul]

end Cslib.GaloisRingArith
