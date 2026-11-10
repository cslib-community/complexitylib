/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.FixedPrime.Width
import CslibFrontier.Foundations.Data.Nat.ClogPow

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
    wordBound n D g p A ≤ (n + 2) ^ (514 * κ + 11818) :=
  (Nat.pow_le_pow_right (by decide) (admissionWidth_le_log hn hD hg hp hA)).trans
    (Nat.two_pow_mul_clog_le_pow (by omega) (by omega))

end Cslib.Algorithms.WordRAM.ExactTriangle.FixedPrime
