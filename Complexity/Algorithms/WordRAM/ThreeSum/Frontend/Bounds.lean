/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Execute

/-!
# Derived native frontend word width and charged cost

The physical unsigned width is four times the existing complete parameter width. This coarse
positive logarithmic threshold covers all descriptor/payload addresses and native intermediates.
The bit budget passed to radix is the explicit magnitude-derived label count, never physical width.

## Main definitions

* `layout`: concrete runtime layout at fixed exponent and input length.
* `width`: positive logarithmic physical word-width threshold.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

/-- Layout computed from the actual unsigned input-length header and polynomial promise. -/
def layout (κ n : ℕ) : Layout :=
  ⟨n, Cslib.Algorithms.ThreeSum.labelBits (2 * (n + 2) ^ κ)⟩

/-- Physical unsigned width, including the two bits reserved when composing signed kernels. -/
def width (κ n : ℕ) : ℕ := 4 * ChanHe.Parameters.width κ n

/-- Concrete charged instruction bound, including the final halt. -/
def cost (κ n : ℕ) : ℕ :=
  let U := (n + 2) ^ κ
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  ChanHe.Parameters.time κ n U + RadixSort.deduplicateTime n Λ +
    (layout κ n).arrays * (43 * n + 32) + 38

/-- The width coefficient is positive, including exponent zero and empty input. -/
theorem width_pos (κ n : ℕ) : 0 < width κ n := by
  have := ChanHe.Parameters.width_pos κ n
  dsimp only [width]
  omega

/-- The physical width is explicitly `Cκ * clog₂(n+2)` with a positive coefficient. -/
theorem width_eq (κ n : ℕ) :
    width κ n = (80 * κ + 484) * Nat.clog 2 (n + 2) := by
  dsimp only [width, ChanHe.Parameters.width]
  ring

/-- All frontend arithmetic is bounded by the fourth power of the existing parameter budget. -/
theorem array_budget_le (n U : ℕ) :
    Arrays.budget ⟨n, Cslib.Algorithms.ThreeSum.labelBits (2 * U)⟩ U ≤
      ChanHe.Parameters.Math.budget n U ^ 4 := by
  let P := ChanHe.Parameters.Math.budget n U
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let A := 3 * (2 * Λ ^ 2 + 2)
  have hP : 8 * U + 4 * n + 64 ≤ P := by dsimp [P, ChanHe.Parameters.Math.budget]; omega
  have h64 : 64 ≤ P := by omega
  have hn : n + 3 ≤ P := by omega
  have hΛ : Λ ≤ P := by
    have hlog := Nat.log_le_self 2 (4 * U)
    dsimp only [Λ, Cslib.Algorithms.ThreeSum.labelBits]
    rw [show 2 * (2 * U) = 4 * U by omega]
    omega
  have hsq : Λ ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left hΛ 2
  have hA : A ≤ 12 * P ^ 2 := by dsimp only [A]; nlinarith
  have hm := Nat.mul_le_mul hn hA
  have hbudget : Arrays.budget ⟨n, Λ⟩ U = 1 + 4 * n + (n + 3) * A + 8 * U + 8 * Λ + 64 := by
    dsimp only [Arrays.budget, Layout.endpoint, Layout.pointer, Layout.payloads,
      Layout.descriptors, Layout.capacity, Layout.arrays, Layout.count, Layout.splits, A]
    ring
  have hP3 : P ≤ P ^ 3 := by nlinarith
  have hP4 : 64 * P ^ 3 ≤ P ^ 4 := by
    have := Nat.mul_le_mul_right (P ^ 3) h64
    nlinarith
  change Arrays.budget ⟨n, Λ⟩ U ≤ P ^ 4
  rw [hbudget]
  nlinarith

/-- The derived physical width discharges the complete native frontend budget. -/
theorem array_budget_fits {κ n w : ℕ} (hw : width κ n ≤ w) :
    Fits w (Arrays.budget (layout κ n) ((n + 2) ^ κ)) := by
  have hp : Fits (ChanHe.Parameters.width κ n)
      (ChanHe.Parameters.Math.budget n ((n + 2) ^ κ)) := ChanHe.Parameters.budget_fits le_rfl
  have hpow := Nat.pow_lt_pow_left hp (by decide : (4 : ℕ) ≠ 0)
  have hf : Fits (width κ n) (ChanHe.Parameters.Math.budget n ((n + 2) ^ κ) ^ 4) := by
    simpa only [Fits, width, ← pow_mul, Nat.mul_comm] using hpow
  exact (hf.of_le (array_budget_le n ((n + 2) ^ κ))).mono hw

/-- Input/header fitting follows from the same global magnitude and width promises. -/
theorem input_fits {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    InputFits w (input.map Signed.encode) := by
  apply ChanHe.Parameters.inputFits input (le_trans ?_ hw) hvalues
  dsimp only [width]
  omega

/-- The lower-level radix bit bound includes the largest signed key, even when `κ=0`. -/
theorem key_lt_two_pow {U : ℕ} (hU : 1 ≤ U) {z : ℤ} (hz : |z| ≤ (U : ℤ)) :
    Signed.encode z < 2 ^ Cslib.Algorithms.ThreeSum.labelBits (2 * U) := by
  have hk := (Math.key_bounds hz).1
  have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (4 * U)
  change Signed.encode z < 2 ^ (Nat.log 2 (2 * (2 * U)) + 1)
  rw [show 2 * (2 * U) = 4 * U by omega]
  exact lt_of_le_of_lt (show Signed.encode z ≤ 4 * U by omega) hp

/-- The explicit radix bit count has a logarithmic bound independent of admitted physical width. -/
theorem digits_bound (κ n : ℕ) :
    (layout κ n).digits ≤ (20 * κ + 121) * Nat.clog 2 (n + 2) := by
  let E := 20 * κ + 120
  let L := Nat.clog 2 (n + 2)
  let U := (n + 2) ^ κ
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (show 1 < n + 2 by omega)
  have hp : ChanHe.Parameters.Math.budget n U ≤ 2 ^ (E * L) := by
    calc
      _ ≤ (n + 2) ^ E := ChanHe.Parameters.Math.budget_polynomial κ n
      _ ≤ (2 ^ L) ^ E := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have h4 : 4 * U ≤ ChanHe.Parameters.Math.budget n U := by
    dsimp only [ChanHe.Parameters.Math.budget]
    omega
  have hlog : Nat.log 2 (4 * U) ≤ E * L := by
    calc
      _ ≤ Nat.log 2 (2 ^ (E * L)) := Nat.log_mono_right (h4.trans hp)
      _ = _ := Nat.log_pow (by decide) _
  change Cslib.Algorithms.ThreeSum.labelBits (2 * U) ≤ _
  dsimp only [Cslib.Algorithms.ThreeSum.labelBits]
  rw [show 2 * (2 * U) = 4 * U by omega]
  dsimp only [E, L] at *
  nlinarith

/-- The entire allocated region and arithmetic budget are polynomial in actual input length. -/
theorem array_budget_polynomial (κ n : ℕ) :
    Arrays.budget (layout κ n) ((n + 2) ^ κ) ≤ (n + 2) ^ (80 * κ + 480) := by
  calc
    _ ≤ ChanHe.Parameters.Math.budget n ((n + 2) ^ κ) ^ 4 := array_budget_le _ _
    _ ≤ ((n + 2) ^ (20 * κ + 120)) ^ 4 :=
      Nat.pow_le_pow_left (ChanHe.Parameters.Math.budget_polynomial κ n) 4
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- Every compact output integer fits the parent's signed kernel width `physicalWidth-2`.
Thus the parent's native signed arithmetic compiler runs at exactly the physical width here. -/
theorem signed_output_fits {κ n w : ℕ} (hw : width κ n ≤ w) {z : ℤ}
    (hz : |z| ≤ (2 * (n + 2) ^ κ : ℕ)) : GenericRAM.Signed.Fits (w - 2) z := by
  have hP := ChanHe.Parameters.budget_fits (κ := κ) (n := n) (w := ChanHe.Parameters.width κ n)
    le_rfl
  have hpos := ChanHe.Parameters.width_pos κ n
  have hW : ChanHe.Parameters.width κ n + 3 ≤ w := by dsimp only [width] at hw; omega
  have hfit : 2 * (n + 2) ^ κ < 2 ^ (w - 3) := by
    have hmag : 2 * (n + 2) ^ κ ≤ ChanHe.Parameters.Math.budget n ((n + 2) ^ κ) := by
      dsimp only [ChanHe.Parameters.Math.budget]; omega
    exact (hmag.trans_lt hP).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have habs := abs_le.mp hz
  have hfi : ((2 * (n + 2) ^ κ : ℕ) : ℤ) < (2 : ℤ) ^ (w - 3) := by exact_mod_cast hfit
  refine ⟨by omega, ?_, ?_⟩
  all_goals rw [show w - 2 - 1 = w - 3 by omega]
  all_goals omega

/-- A word at the canonical physical width has polynomial magnitude. -/
theorem two_pow_width_le (κ n : ℕ) : 2 ^ width κ n ≤ (n + 2) ^ (160 * κ + 968) := by
  let L := Nat.clog 2 (n + 2)
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hp : 2 ^ (L - 1) < n + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := n + 2) (by decide) (by omega)
  have heq : 2 ^ L = 2 * 2 ^ (L - 1) := by
    conv_lhs => rw [show L = (L - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have hceil : 2 ^ L ≤ (n + 2) ^ 2 := by rw [heq]; nlinarith
  rw [width_eq]
  calc
    _ = (2 ^ L) ^ (80 * κ + 484) := by rw [← pow_mul]; congr 1; ring
    _ ≤ ((n + 2) ^ 2) ^ (80 * κ + 484) := Nat.pow_le_pow_left hceil _
    _ = _ := by
      rw [← pow_mul]
      exact congrArg (fun e : ℕ => (n + 2) ^ e) (by omega)

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
