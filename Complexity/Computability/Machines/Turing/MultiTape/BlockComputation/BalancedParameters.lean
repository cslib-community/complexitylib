/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
public import Mathlib.Algebra.Order.Floor.Div
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Native dyadic parameters for block simulation

The block width is a power of two near the square root of the time guess times its binary
length. The horizon is ceiling division by this positive width. Computing these parameters
uses space linear in the actual binary time guess and does not require a time-constructibility
hypothesis. The square inequalities state the approximation without real-valued square roots.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.BalancedParameters

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- A dyadic approximation to the square root of time times binary time length. -/
@[expose] def blockWidth (T : ℕ) : ℕ := 2 ^ ((T.size + T.size.size) / 2)

/-- The number of blocks needed to cover the complete time guess. -/
@[expose] def horizon (T : ℕ) : ℕ := T ⌈/⌉ blockWidth T

/-- The width is positive even at a zero time guess. -/
theorem blockWidth_pos (T : ℕ) : 0 < blockWidth T := by
  exact Nat.pow_pos (by decide)

/-- The selected horizon covers every step of the time guess. -/
theorem coverage (T : ℕ) : T ≤ horizon T * blockWidth T :=
  by simpa only [horizon, smul_eq_mul, Nat.mul_comm] using
    (le_smul_ceilDiv (α := ℕ) (b := T) (blockWidth_pos T))

/-- Rounding the horizon adds less than one block. -/
theorem horizon_mul_lt (T : ℕ) : horizon T * blockWidth T < T + blockWidth T :=
  by
    have h := Nat.div_mul_le_self (T + blockWidth T - 1) (blockWidth T)
    have hp := blockWidth_pos T
    change (T + blockWidth T - 1) / blockWidth T * blockWidth T < _
    omega

/-- A positive time guess gives a nonzero schedule horizon. -/
theorem horizon_pos {T : ℕ} (hT : 0 < T) : 0 < horizon T := by
  have h := coverage T
  by_contra hn
  have hz : horizon T = 0 := by omega
  rw [hz, Nat.zero_mul] at h
  omega

private theorem pow_size_le_twice {n : ℕ} (hn : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  have hs : 0 < n.size := Nat.size_pos.mpr hn
  have hlo : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
  calc
    2 ^ n.size = 2 ^ (n.size - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    _ ≤ n * 2 := Nat.mul_le_mul_right 2 hlo
    _ = 2 * n := Nat.mul_comm _ _

/-- The chosen block square is at most four times the intended time-length product. -/
theorem blockWidth_sq_le {T : ℕ} (hT : 0 < T) :
    blockWidth T ^ 2 ≤ 4 * (T * T.size) := by
  have hs : 0 < T.size := Nat.size_pos.mpr hT
  have h₁ := pow_size_le_twice hT
  have h₂ := pow_size_le_twice hs
  have hexp : 2 * ((T.size + T.size.size) / 2) ≤ T.size + T.size.size := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hexp
  have hsq : 2 ^ (2 * ((T.size + T.size.size) / 2)) = blockWidth T ^ 2 := by
    rw [blockWidth, ← pow_mul]
    congr 1
    omega
  rw [hsq, pow_add] at hp
  have hmul := Nat.mul_le_mul h₁ h₂
  nlinarith

/-- The chosen block square is never smaller than half the intended time-length product. -/
theorem time_mul_size_lt_twice_blockWidth_sq (T : ℕ) :
    T * T.size < 2 * blockWidth T ^ 2 := by
  have h₁ := Nat.lt_size_self T
  have h₂ := Nat.lt_size_self T.size
  have hprod : T * T.size < 2 ^ T.size * 2 ^ T.size.size := by
    calc
      T * T.size ≤ T * 2 ^ T.size.size := Nat.mul_le_mul_left T h₂.le
      _ < 2 ^ T.size * 2 ^ T.size.size :=
        Nat.mul_lt_mul_of_pos_right h₁ (Nat.pow_pos (by decide))
  have hexp : T.size + T.size.size ≤ 2 * ((T.size + T.size.size) / 2) + 1 := by omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hexp
  have hsq : 2 ^ (2 * ((T.size + T.size.size) / 2)) = blockWidth T ^ 2 := by
    rw [blockWidth, ← pow_mul]
    congr 1
    omega
  simp only [pow_add, pow_one, hsq] at hp
  nlinarith

/-- The selected width itself has only a linear number of binary digits. -/
theorem blockWidth_size_le (T : ℕ) : (blockWidth T).size ≤ T.size + 1 := by
  have h := length_encNat_le_self T.size
  rw [length_encNat_eq_size] at h
  rw [blockWidth, Nat.size_pow]
  omega

/-- The binary time length is smaller than twice the selected block width. -/
theorem size_lt_twice_blockWidth (T : ℕ) : T.size < 2 * blockWidth T := by
  have hsize := length_encNat_le_self T
  rw [length_encNat_eq_size] at hsize
  have hsq := Nat.mul_le_mul_right T.size hsize
  have hbalance := time_mul_size_lt_twice_blockWidth_sq T
  nlinarith

/-- Horizon overhead times binary time length is paid by the selected block and one length. -/
theorem horizon_mul_size_lt {T : ℕ} (hT : 0 < T) :
    horizon T * T.size < 2 * blockWidth T + T.size := by
  have hs : 0 < T.size := Nat.size_pos.mpr hT
  have hround := Nat.mul_lt_mul_of_pos_right (horizon_mul_lt T) hs
  have hbalance := time_mul_size_lt_twice_blockWidth_sq T
  apply Nat.lt_of_mul_lt_mul_left (a := blockWidth T)
  nlinarith

/-- Block storage and horizon times binary time length balance within a fixed constant. -/
theorem combined_le (T : ℕ) :
    blockWidth T + horizon T * T.size ≤ 5 * blockWidth T := by
  by_cases hz : T = 0
  · subst T
    simp only [Nat.size_zero, Nat.mul_zero, Nat.add_zero]
    omega
  · have hq := horizon_mul_size_lt (Nat.pos_of_ne_zero hz)
    have hs := size_lt_twice_blockWidth T
    omega

/-- An integer square bound for the complete balanced storage term. -/
theorem combined_sq_le {T : ℕ} (hT : 0 < T) :
    (blockWidth T + horizon T * T.size) ^ 2 ≤ 100 * (T * T.size) := by
  have h := combined_le T
  have hmul := Nat.mul_le_mul h h
  have hsq := blockWidth_sq_le hT
  nlinarith

/-- Increasing the time guess never decreases the dyadic block width. -/
theorem blockWidth_mono {T U : ℕ} (h : T ≤ U) : blockWidth T ≤ blockWidth U := by
  have hs := Nat.size_le_size h
  have hss := Nat.size_le_size hs
  exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)

/-- The binary-width stack cost is bounded by a constant times the selected block width. -/
theorem storage_le (T : ℕ) :
    blockWidth T + horizon T * ((blockWidth T).size + 1) ≤ 15 * blockWidth T := by
  by_cases hz : T = 0
  · subst T
    decide
  · have hs : 0 < T.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hz)
    have hbits := blockWidth_size_le T
    have hscalar : (blockWidth T).size + 1 ≤ 3 * T.size := by omega
    have hmul := Nat.mul_le_mul_left (horizon T) hscalar
    have hcombined := combined_le T
    nlinarith

/-- The dyadic exponent and its output bits fit the actual binary time storage. -/
theorem blockWidth_inSpace : ComputableInSpace blockWidth encNat encNat
    (fun T => (encNat T).length) := by
  have hid : ComputableInSpace (fun T : ℕ => T) encNat encNat
      (fun T => (encNat T).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hsize := budget_comp_linear natSize hid
  have hsizeSize := budget_comp_linear natSize hsize
  have hexp := budget_natDiv (budget_natAdd hsize hsizeSize)
    (budget_const (encB := encNat) 2 (.refl _))
  refine (budget_natPow_variable (budget_const (encB := encNat) 2 (.refl _)) hexp
    (.of_le_linear 4 4 fun T => ?_)).of_enc_eq fun _ => rfl
  have hsize_le := length_encNat_le_self T.size
  have hexp_le : (T.size + T.size.size) / 2 ≤ T.size := by
    rw [length_encNat_eq_size] at hsize_le
    omega
  have hbits := (length_encNat_le_self ((T.size + T.size.size) / 2)).trans hexp_le
  have htwo : (encNat 2).length = 2 := rfl
  simp only [htwo, length_encNat_eq_size] at hbits ⊢
  omega

/-- Ceiling division computes the horizon in actual binary-input-linear space. -/
theorem horizon_inSpace : ComputableInSpace horizon encNat encNat
    (fun T => (encNat T).length) := by
  have hid : ComputableInSpace (fun T : ℕ => T) encNat encNat
      (fun T => (encNat T).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  exact (budget_natDiv (budget_natPred (budget_natAdd hid blockWidth_inSpace))
    blockWidth_inSpace).of_enc_eq fun T => by rw [horizon, Nat.ceilDiv_eq_add_pred_div]

end Turing.MultiTapePTM.BlockComputation.BalancedParameters
