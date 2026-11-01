/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Core
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.InputSpec
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Setup
import Complexity.Foundations.Data.Nat.Log

/-!
# Original-parameter caller admission

The physical threshold includes the caller's raw old-word bound P, so dirty words before
their actual remainder instructions fit the physical machine. P is a bound on original
caller data, not a computed layout, source execution or algorithm argument. Source width
and its actual runtime modulus depend only on original scalars and the copied word sum.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Positive physical width for original caller words, source addresses and every setup fit. -/
@[expose] def admissionWidth (n D g p total b P : ℕ) : ℕ :=
  Nat.clog 2 (b + 4 * windowSize n D g p total + P + 1024) + 1

/-- A physical-width-independent bound for prefix words and new address support. -/
@[expose] def wordBound (n D g p total b P : ℕ) : ℕ :=
  4 * (b + 4 * windowSize n D g p total + P + 1024)

/-- Caller admission is positive even without geometric assumptions. -/
theorem admissionWidth_pos (n D g p total b P : ℕ) : 0 < admissionWidth n D g p total b P := by
  unfold admissionWidth
  omega

/-- Every wider width contains the caller's raw dirty words and the actual source reservation. -/
theorem admission_fits {W n D g p total b P : ℕ}
    (hW : admissionWidth n D g p total b P ≤ W) :
    Fits W (b + 4 * windowSize n D g p total + P + 1024) := by
  have hw : Nat.clog 2 (b + 4 * windowSize n D g p total + P + 1024) < W := by
    unfold admissionWidth at hW
    omega
  exact (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hw)

/-- The real copied input span fits the computed source window before the solver begins. -/
theorem inputEnd_le_window {m n g p : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) :
    5 + 3 * (n * n) ≤ windowSize n (D m) g p (rawTotal n values) := by
  have hi := input_fits_source (m := m) (g := g) (p := p) values hlen
    (natAbs_le_rawTotal values hlen)
  have h := hi.1
  simp only [PreparationInput.input, List.length_append, List.length_cons, List.length_nil,
    List.length_map, hlen, Nat.reduceAdd] at h
  change _ < windowSize n (D m) g p (rawTotal n values) at h
  omega

/-- The width's power of two is bounded by a fixed original-input numerical envelope. -/
theorem pow_admissionWidth_le (n D g p total b P : ℕ) :
    2 ^ admissionWidth n D g p total b P ≤ wordBound n D g p total b P := by
  let E := b + 4 * windowSize n D g p total + P + 1024
  have he : E ≠ 0 := by dsimp only [E]; omega
  have hp := Nat.pow_clog_le_mul (by decide : 1 < (2 : ℕ)) he
  change 2 ^ (Nat.clog 2 E + 1) ≤ 4 * E
  rw [pow_succ]
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
