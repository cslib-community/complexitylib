/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Fast
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Slow
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Parameters

/-!
# Original-input admission for the assembled solver

One numerical envelope covers original pointer arithmetic, actual parameter preparation,
all candidate counter calls, selector control, the computed callable window and exhaustive
small-input arithmetic. Its inputs are only original scalar/pointer data and original matrix
values. It does not assume an intermediate execution, layout, selection or time certificate.

Execution admission is separate from whole-data word bounds: the general host callee may
have arbitrary unused old words. Numerical prefix bounds additionally require the original
raw-word bound, before any actual dirty-memory remainder is executed.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Common original-input numerical envelope for both actual execution branches. -/
@[expose] def envelope (n F b ap bp cp : ℕ) (values : List ℤ) : ℕ :=
  let d := ParameterChoice.window n
  let g := ParameterChoice.groups n
  let cap := Nat.sqrt d
  b + 4 * CallableFixedPrime.windowSize n d g cap (CallableFixedPrime.rawTotal n values) + 1024 +
    CountPrime.addressBudget n cap (Nat.clog 2 n) b ap bp cp +
    CountPrime.magnitudeBudget cap (Nat.clog 2 n) F +
    (4 * (d + 2) * (d + 2) + 4) + DyadicParameters.wordBudget n +
    (b + n * (n * n) + 6 * F + 10) + 1

/-- Positive original-input execution threshold, independent of old unused words. -/
@[expose] def executionWidth (n F b ap bp cp : ℕ) (values : List ℤ) : ℕ :=
  Nat.clog 2 (envelope n F b ap bp cp values) + 3

/-- The composed execution threshold is positive even for empty original matrices. -/
theorem executionWidth_pos (n F b ap bp cp : ℕ) (values : List ℤ) :
    0 < executionWidth n F b ap bp cp values := by unfold executionWidth; omega

/-- Every larger physical width contains the entire original-input numerical envelope. -/
theorem envelope_fits {W n F b ap bp cp : ℕ} (values : List ℤ)
    (hW : executionWidth n F b ap bp cp values ≤ W) : Fits W (envelope n F b ap bp cp values) := by
  have hpow := Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (envelope n F b ap bp cp values)
  exact hpow.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
    (by unfold executionWidth at hW; omega))

/-- Existing signed counter arithmetic fits from the original-input envelope alone. -/
theorem counter_magnitude_fits {n F b ap bp cp : ℕ} (values : List ℤ) :
    GenericRAM.Signed.Fits (Nat.clog 2 (envelope n F b ap bp cp values) + 1)
      (CountPrime.magnitudeBudget (Nat.sqrt (ParameterChoice.window n)) (Nat.clog 2 n) F : ℤ) := by
  have hle : CountPrime.magnitudeBudget (Nat.sqrt (ParameterChoice.window n)) (Nat.clog 2 n) F <
      envelope n F b ap bp cp values := by dsimp only [envelope]; omega
  have hp := hle.trans_le (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _)
  refine ⟨by omega, ?_, ?_⟩
  · simp only [Nat.add_sub_cancel]
    exact (neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _)
  · simp only [Nat.add_sub_cancel]
    exact_mod_cast hp

/-- Actual counter addresses fit at the two-bit extension used by native signed kernels. -/
theorem counter_address_fits {n F b ap bp cp : ℕ} (values : List ℤ) :
    Fits (Nat.clog 2 (envelope n F b ap bp cp values) + 1 + 2)
      (CountPrime.addressBudget n (Nat.sqrt (ParameterChoice.window n)) (Nat.clog 2 n)
        b ap bp cp) := by
  exact (envelope_fits (n := n) (F := F) (b := b) (ap := ap) (bp := bp) (cp := cp)
    values (by unfold executionWidth; omega)).of_le (by dsimp only [envelope]; omega)

/-- Every native parameter logarithm, power, counter and fixed constant fits. -/
theorem parameter_fits {W n F b ap bp cp : ℕ} (values : List ℤ)
    (hW : executionWidth n F b ap bp cp values ≤ W) : Fits W (DyadicParameters.wordBudget n) :=
  (envelope_fits values hW).of_le (by dsimp only [envelope]; omega)

/-- Selector square tests fit without a supplied prime or intermediate counter bound. -/
theorem controller_fits {W n F b ap bp cp : ℕ} (values : List ℤ)
    (hW : executionWidth n F b ap bp cp values ≤ W) :
    Fits W (4 * (ParameterChoice.window n + 2) * (ParameterChoice.window n + 2) + 4) :=
  (envelope_fits values hW).of_le (by dsimp only [envelope]; omega)

/-- The maximum candidate window admits the real fixed-prime adaptation and computed modulus. -/
theorem callable_fits {W n F b ap bp cp : ℕ} (values : List ℤ)
    (hW : executionWidth n F b ap bp cp values ≤ W) :
    Fits W (b + 4 * CallableFixedPrime.windowSize n (ParameterChoice.window n)
      (ParameterChoice.groups n) (Nat.sqrt (ParameterChoice.window n))
      (CallableFixedPrime.rawTotal n values) + 1024) :=
  (envelope_fits values hW).of_le (by dsimp only [envelope]; omega)

/-- The real exhaustive branch is admitted from original dimension, magnitude and source end. -/
theorem slow_fits {W n F b ap bp cp : ℕ} (values : List ℤ)
    (hW : executionWidth n F b ap bp cp values ≤ W) :
    Fits W (b + n * (n * n) + 6 * F + 10) :=
  (envelope_fits values hW).of_le (by dsimp only [envelope]; omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
