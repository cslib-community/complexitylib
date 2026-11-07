/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Width
import Complexity.Foundations.Data.Nat.Log

/-!
# Numerical word envelope for fixed-prime native prefixes

The admission remains logarithmic for polynomial original weights and bounded scalar headers.
The envelope is independent of the physical width and does not instruct the machine to clear
or snapshot that range. Execution-specific prefix certificates belong to the one-slot solver.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A fixed original-input bound for all prefix words and memory support. -/
@[expose] def wordBound (n D g p A : ℕ) : ℕ := 2 ^ admissionWidth n D g p A

/-- The fixed-prime solver retains an explicit polynomial envelope for each weight exponent. -/
theorem wordBound_le_pow {n D g p A κ : ℕ} (hn : 1 ≤ n)
    (hD : D ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11818) := by
  let b := n + 2
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hbase : 2 ^ Nat.clog 2 b ≤ b ^ 2 :=
    (Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) (by omega : b ≠ 0)).trans
      (by nlinarith only [hb])
  have hw := admissionWidth_le_log hn hD hg hp hA
  change 2 ^ admissionWidth n D g p A ≤ _
  calc
    _ ≤ 2 ^ ((257 * κ + 5909) * Nat.clog 2 b) := Nat.pow_le_pow_right (by decide) hw
    _ = (2 ^ Nat.clog 2 b) ^ (257 * κ + 5909) := by rw [← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (b ^ 2) ^ (257 * κ + 5909) := Nat.pow_le_pow_left hbase _
    _ = b ^ (514 * κ + 11818) := by
      rw [← Nat.pow_mul]
      exact congrArg (fun j : ℕ => b ^ j) (by omega : 2 * (257 * κ + 5909) = 514 * κ + 11818)

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
