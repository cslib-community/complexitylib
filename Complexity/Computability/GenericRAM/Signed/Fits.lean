/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Signed
import Mathlib.Algebra.Order.Group.Abs

/-!
# Signed fits from magnitude envelopes

A representable nonnegative envelope covers every integer whose absolute value is at most it.
The envelope itself must fit: the asymmetric signed range still excludes its positive endpoint.

## Main results

* `Fits.of_natAbs_le`: derive signed fitting from a representable natural magnitude envelope.

This elementary bound is original.
-/

@[expose] public section

namespace Cslib.GenericRAM.Signed

/-- A signed fit for a nonnegative envelope also covers every integer bounded by it. -/
theorem Fits.of_natAbs_le {w B : ℕ} (hfit : Fits w (B : ℤ))
    {z : ℤ} (hz : z.natAbs ≤ B) : Fits w z := by
  obtain ⟨hw, hlo, hhi⟩ := hfit
  have habs := abs_le.mp (show |z| ≤ (B : ℤ) by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz)
  exact ⟨hw, by omega, by omega⟩

end Cslib.GenericRAM.Signed
