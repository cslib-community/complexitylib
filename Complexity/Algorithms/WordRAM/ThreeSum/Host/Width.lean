/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Prepare

/-!
# A logarithmic word width for the Convolution-3SUM host

The existing parameter program's polynomial budget also bounds the host's matrix addresses,
signed indices and filler. Four extra source bits suffice. These bounds cover the host;
the concrete solver must separately prove its own execution at the target width.

## Main definitions

* `Host.width`: a positive logarithmic source-width threshold.

## Main results

* `Host.layout_fits`: all matrix addresses and the encoded filler fit.
* `Host.index_fits`, `Host.filler_fits`: the signed matrix-builder premises.
* `Host.value_fits`: polynomially bounded input values fit the signed source width.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM

/-- Source width; the signed arithmetic kernels use unsigned target words of width `w+2`. -/
def width (κ N : ℕ) : ℕ := (20 * κ + 125) * Nat.clog 2 (N + 2)

/-- The threshold includes the empty input and magnitude exponent zero. -/
theorem width_pos (κ N : ℕ) : 0 < width κ N := by
  have := Nat.clog_pos (b := 2) (by decide) (show 1 < N + 2 by omega)
  dsimp [width]
  positivity

/-- The host has at least four more source bits than the parameter routine requires. -/
theorem parameters_width_le (κ N : ℕ) : ChanHe.Parameters.width κ N + 4 ≤ width κ N := by
  have := Nat.clog_pos (b := 2) (by decide) (show 1 < N + 2 by omega)
  dsimp [width, ChanHe.Parameters.width]
  nlinarith

private theorem margin_fits {κ N w : ℕ} (hw : width κ N ≤ w) :
    Fits (w - 1) (8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ)) := by
  have hf := ChanHe.Parameters.budget_fits (κ := κ) (n := N) (w := ChanHe.Parameters.width κ N)
    (Nat.le_refl _)
  have hwidth := (parameters_width_le κ N).trans hw
  have hmul : 8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) <
      8 * 2 ^ ChanHe.Parameters.width κ N := Nat.mul_lt_mul_of_pos_left hf (by decide)
  apply hmul.trans_le
  calc
    _ = 2 ^ (ChanHe.Parameters.width κ N + 3) := by rw [pow_add]; norm_num; omega
    _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem signed_fits {κ N w : ℕ} (hw : width κ N ≤ w) (z : ℤ)
    (hz : |z| ≤ (8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) : ℕ)) :
    GenericRAM.Signed.Fits w z := by
  have hf := margin_fits hw
  have hwpos := width_pos κ N
  have hpow : (8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) : ℤ) <
      2 ^ (w - 1) := by exact_mod_cast hf
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  exact ⟨by omega, by omega, by omega⟩

/-- A linear bound for the number of entries per generated matrix. -/
theorem area_le (N : ℕ) : sideLength N * sideLength N ≤ 3 * N + 1 := by
  have := Nat.sqrt_le N
  have := Nat.sqrt_le_self N
  dsimp [sideLength]
  nlinarith

/-- All three matrix blocks and their one-past-end addresses fit at the source width. -/
theorem layout_fits {κ N w : ℕ} (hw : width κ N ≤ w) :
    Fits w (N + 1 + 3 * (sideLength N * sideLength N)) ∧
      Fits w (4 * (N + 2) ^ κ + 2) := by
  have hf := (margin_fits hw).mono (show w - 1 ≤ w by omega)
  have ha := area_le N
  constructor <;> apply hf.of_le <;> dsimp [ChanHe.Parameters.Math.budget] <;> omega

/-- The builder's positive and negative filler fit the signed source range. -/
theorem filler_fits {κ N w : ℕ} (hw : width κ N ≤ w) :
    GenericRAM.Signed.Fits w (2 * ((N + 2) ^ κ : ℕ) + 1) ∧
      GenericRAM.Signed.Fits w (-(2 * ((N + 2) ^ κ : ℕ) + 1)) := by
  have hbound : |(2 * ((N + 2) ^ κ : ℕ) + 1 : ℤ)| ≤
      (8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) : ℕ) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (show 2 * (N + 2) ^ κ + 1 ≤
      8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) from by
        dsimp [ChanHe.Parameters.Math.budget]
        omega)
  exact ⟨signed_fits hw _ hbound, signed_fits hw _ (by simpa only [abs_neg] using hbound)⟩

/-- Every signed input index computed in a generated instance fits. -/
theorem index_fits {κ N w s : ℕ} (hw : width κ N ≤ w) (hs : s < 2 * sideLength N) :
    GenericRAM.Signed.Fits w ((2 * (sideLength N * sideLength N) + s + 1 : ℕ) : ℤ) := by
  apply signed_fits hw
  rw [abs_of_nonneg (by positivity)]
  have ha := area_le N
  have ht := Nat.sqrt_le_self N
  dsimp only [sideLength] at hs
  exact_mod_cast (show 2 * (sideLength N * sideLength N) + s + 1 ≤
    8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) from by
      dsimp [ChanHe.Parameters.Math.budget]
      omega)

/-- A polynomial magnitude bound implies the signed source fit premise. -/
theorem value_fits {κ N w : ℕ} (hw : width κ N ≤ w) {z : ℤ}
    (hz : |z| ≤ ((N + 2) ^ κ : ℕ)) : GenericRAM.Signed.Fits w z := by
  apply signed_fits hw z
  have hb : (N + 2) ^ κ ≤ 8 * ChanHe.Parameters.Math.budget N ((N + 2) ^ κ) := by
    dsimp [ChanHe.Parameters.Math.budget]
    omega
  exact hz.trans (by exact_mod_cast hb)

end Cslib.Algorithms.WordRAM.ThreeSum.Host
