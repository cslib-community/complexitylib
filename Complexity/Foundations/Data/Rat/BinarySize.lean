/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, binary rational operand bounds)

public import Complexity.Foundations.Data.Rat.Basic
public import Complexity.Foundations.Data.Nat.BinarySize
public import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Binary operand bounds for rational arithmetic

The representation is a signed binary numerator and a positive binary denominator,
with the fraction reduced. `Rat.binaryWidth` bounds each magnitude separately;
framing and the sign bit add only constant overhead per field. The arithmetic
bounds include reduction, rather than treating a rational as one fixed-size word.
They assert operand sizes, not a machine running time.

## Main results

* `Rat.binaryWidth_mul_le`: multiplication adds operand widths.
* `Rat.binaryWidth_add_le`: addition adds widths with one carry bit.
* `Rat.binaryWidth_div_le`: division adds operand widths.
* `Rat.binaryWidth_prod_le`: products have linearly bounded binary operands.
* `Rat.binaryWidth_sum_le`: sums have linearly bounded binary operands.
-/

public section
namespace Rat

/-- Maximum magnitude width in the canonical signed-numerator/positive-denominator
binary representation. A sign bit and field framing are charged separately. -/
@[expose] def binaryWidth (q : ℚ) : ℕ := max q.num.natAbs.size q.den.size

private theorem width_divInt {n d : ℤ} (hd : d ≠ 0) :
    binaryWidth (n /. d) ≤ max n.natAbs.size d.natAbs.size := by
  apply max_le
  · exact (Nat.size_le_size (natAbs_num_divInt_le n d hd)).trans (le_max_left ..)
  · exact (Nat.size_le_size (den_divInt_le n d hd)).trans (le_max_right ..)

/-- Multiplication and normalization do not increase the sum of operand widths. -/
theorem binaryWidth_mul_le (a b : ℚ) :
    binaryWidth (a * b) ≤ binaryWidth a + binaryWidth b := by
  rw [mul_def', mkRat_eq_divInt]
  apply (width_divInt (by exact_mod_cast Nat.mul_ne_zero a.den_nz b.den_nz)).trans
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  apply max_le
  · exact (Nat.size_mul_le _ _).trans
      (Nat.add_le_add (le_max_left ..) (le_max_left ..))
  · exact (Nat.size_mul_le _ _).trans
      (Nat.add_le_add (le_max_right ..) (le_max_right ..))

/-- Addition pays a carry bit as well as the two operand widths. -/
theorem binaryWidth_add_le (a b : ℚ) :
    binaryWidth (a + b) ≤ binaryWidth a + binaryWidth b + 1 := by
  rw [add_num_den]
  apply (width_divInt (by exact_mod_cast Nat.mul_ne_zero a.den_nz b.den_nz)).trans
  apply max_le
  · have hab := Nat.size_le_size (Int.natAbs_add_le (a.num * b.den) (a.den * b.num))
    apply hab.trans ((Nat.size_add_le_max _ _).trans _)
    simp only [Int.natAbs_mul, Int.natAbs_natCast]
    have h₁ : (a.num.natAbs * b.den).size ≤ binaryWidth a + binaryWidth b :=
      (Nat.size_mul_le a.num.natAbs b.den).trans
      (Nat.add_le_add (le_max_left _ _) (le_max_right _ _))
    have h₂ : (a.den * b.num.natAbs).size ≤ binaryWidth a + binaryWidth b :=
      (Nat.size_mul_le a.den b.num.natAbs).trans
      (Nat.add_le_add (le_max_right _ _) (le_max_left _ _))
    exact Nat.add_le_add_right (max_le h₁ h₂) 1
  · simp only [Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.size_mul_le a.den b.den).trans (by
      unfold binaryWidth
      omega)

/-- Negation leaves binary magnitudes unchanged. -/
@[simp] theorem binaryWidth_neg (a : ℚ) : binaryWidth (-a) = binaryWidth a := by
  simp [binaryWidth]

/-- Subtraction has the same width bound as addition. -/
theorem binaryWidth_sub_le (a b : ℚ) :
    binaryWidth (a - b) ≤ binaryWidth a + binaryWidth b + 1 := by
  simpa only [sub_eq_add_neg, binaryWidth_neg] using binaryWidth_add_le a (-b)

/-- Inversion exchanges numerator and denominator, except that zero remains zero. -/
@[simp] theorem binaryWidth_inv (a : ℚ) : binaryWidth a⁻¹ = binaryWidth a := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [binaryWidth, Rat.num_inv, Rat.den_inv, ha, Int.natAbs_mul,
      Int.natAbs_sign_of_ne_zero (Rat.num_ne_zero.mpr ha), max_comm]

/-- Division includes the binary sizes of both operands. -/
theorem binaryWidth_div_le (a b : ℚ) :
    binaryWidth (a / b) ≤ binaryWidth a + binaryWidth b := by
  simpa only [div_eq_mul_inv, binaryWidth_inv] using binaryWidth_mul_le a b⁻¹

@[simp] theorem binaryWidth_zero : binaryWidth 0 = 1 := by decide
@[simp] theorem binaryWidth_one : binaryWidth 1 = 1 := by decide

/-- A natural-number counter uses its binary digits and a unit denominator. -/
theorem binaryWidth_natCast_le (n : ℕ) : binaryWidth (n : ℚ) ≤ n.size + 1 := by
  simp [binaryWidth]

/-- Flooring a rational to a natural table key cannot exceed the numerator's
magnitude width. Positive denominators and truncation at zero are both covered. -/
theorem size_floor_le (q : ℚ) : (⌊q⌋₊ : ℕ).size ≤ binaryWidth q := by
  have hq : q ≤ (q.num.natAbs : ℚ) := by
    have hn : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by
      have h : (q.num : ℚ) ≤ ((q.num.natAbs : ℤ) : ℚ) :=
        Int.cast_le.mpr Int.le_natAbs
      simpa only [Int.cast_natCast] using h
    have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    have heq : q = (q.num : ℚ) / q.den := by
      have h := Rat.divInt_eq_div q.num (q.den : ℤ)
      simpa only [Rat.num_divInt_den, Int.cast_natCast] using h
    conv_lhs => rw [heq]
    apply (div_le_iff₀ (by exact_mod_cast q.den_pos)).mpr
    have hnon : (0 : ℚ) ≤ q.num.natAbs := Nat.cast_nonneg _
    nlinarith
  exact (Nat.size_le_size (Nat.floor_le_of_le hq)).trans (le_max_left ..)

/-- Multiplying an arbitrary list of rational factors has linear operand growth,
including the empty product. -/
theorem binaryWidth_prod_le (xs : List ℚ) :
    binaryWidth xs.prod ≤ (xs.map binaryWidth).sum + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    exact (binaryWidth_mul_le x xs.prod).trans (by omega)

/-- Adding an arbitrary list of rational costs has linear operand growth,
including carry bits and the empty sum. -/
theorem binaryWidth_sum_le (xs : List ℚ) :
    binaryWidth xs.sum ≤ (xs.map (fun q => binaryWidth q + 1)).sum + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, List.sum_cons]
    exact (binaryWidth_add_le x xs.sum).trans (by omega)

end Rat
