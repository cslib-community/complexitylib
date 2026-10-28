/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Bounds

/-!
# Uniform logarithmic-square native frontend cost

The bound includes the complete parameter program, explicit-bit radix sorting, full
multiplicities, every compact scan, all descriptor/payload setup and writes, and the final halt.
It is uniform over all admitted sufficiently wide words, including empty input.

## Main results

* `cost_bound`: an explicit `Oκ((n+1) clog₂(n+2)²)` instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

/-- Explicit uniform coefficient; deliberately coarse and independent of physical word width. -/
def costCoefficient (κ : ℕ) : ℕ := 2000 * (20 * κ + 121) ^ 2 + 400 * κ + 4000

/-- Concrete derivation from the actual charged instruction formula to logarithmic-square cost. -/
theorem cost_bound (κ n : ℕ) :
    cost κ n ≤ costCoefficient κ * (n + 1) * Nat.clog 2 (n + 2) ^ 2 := by
  let L := Nat.clog 2 (n + 2)
  let K := 20 * κ + 121
  let Λ := (layout κ n).digits
  let A := (layout κ n).arrays
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (show 1 < n + 2 by omega)
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hΛ : Λ ≤ K * L := digits_bound κ n
  have hKL : 1 ≤ K * L := by nlinarith
  have hKLsq : K * L ≤ (K * L) ^ 2 := by nlinarith
  have hAs : A ≤ 12 * (K * L) ^ 2 := by
    have hs := Nat.pow_le_pow_left hΛ 2
    dsimp only [A, Layout.arrays, Layout.count, Layout.splits, Λ]
    nlinarith
  have hRad : RadixSort.deduplicateTime n Λ ≤ (37 * Λ + 43) * (n + 1) := by
    dsimp only [RadixSort.deduplicateTime]
    nlinarith
  have hRcoef : 37 * Λ + 43 ≤ 80 * (K * L) ^ 2 := by nlinarith
  have hR := hRad.trans (Nat.mul_le_mul_right (n + 1) hRcoef)
  have hA := Nat.mul_le_mul hAs (show 43 * n + 32 ≤ 75 * (n + 1) by omega)
  have hParams := ChanHe.Parameters.time_bound κ n
  have hsqrt := Nat.sqrt_le_self n
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hLN : L ≤ (n + 1) * L ^ 2 := by nlinarith
  have hN : n + 1 ≤ (n + 1) * L ^ 2 := by nlinarith
  have hC := Nat.mul_le_mul_left (400 * κ + 3000) hLN
  change ChanHe.Parameters.time κ n ((n + 2) ^ κ) + RadixSort.deduplicateTime n Λ +
    A * (43 * n + 32) + 38 ≤ _
  dsimp only [costCoefficient, K, L] at *
  nlinarith

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
