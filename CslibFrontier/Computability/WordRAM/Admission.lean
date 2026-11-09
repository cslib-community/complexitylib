/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Defs
public import Mathlib.Data.Nat.Log

/-!
# Ceiling-logarithm word admission

Two sufficient scalar rules convert ceiling-logarithm width bounds into unsigned word fits.
An envelope itself requires a strict width margin; a value strictly below the envelope needs
only the non-strict logarithmic width bound. Existing `Fits.of_le` and `Fits.mono` transport
these certificates to smaller values and larger physical widths.

## Main results

* `fits_of_clog_lt`: an envelope fits when its ceiling logarithm is strictly below the width.
* `fits_of_lt_clog_le`: every value strictly below an envelope fits at its ceiling logarithm.
-/

public section

namespace Cslib.WordRAM

/-- An envelope fits when its ceiling logarithm is strictly below the word width. -/
theorem fits_of_clog_lt {B W : ℕ} (hW : Nat.clog 2 B < W) : Fits W B :=
  (Nat.le_pow_clog Nat.one_lt_two B).trans_lt
    (Nat.pow_lt_pow_right Nat.one_lt_two hW)

/-- A value strictly below an envelope fits at any width at least its ceiling logarithm. -/
theorem fits_of_lt_clog_le {v B W : ℕ} (hv : v < B) (hW : Nat.clog 2 B ≤ W) : Fits W v :=
  hv.trans_le ((Nat.le_pow_clog Nat.one_lt_two B).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hW))

end Cslib.WordRAM
