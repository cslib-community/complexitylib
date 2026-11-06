/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Morton indexing for square matrices

`Nat.Morton.index a b` interleaves the binary row and column digits, with the row digit in
the higher bit of each pair. Its inverse projections are `row` and `column`. For a square
of side `2^k`, the four contiguous blocks of length `4^k` are exactly its four quadrants.

These elementary digit identities adapt Spec/Sec3/Theorem17/ZOrder.lean, lines 39–151, at
anthropics/formal-math revision 16a5ce41304fcdaea4e0be7c132e1c361dc26da5. The native counter
will compute the spread table in memory; these definitions do not supply a table oracle.
-/

public section

namespace Nat.Morton

/-- Move each binary digit to an even position, preserving its least-significant-first order. -/
@[expose] def spread (i : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 2 i)

/-- Interleaved row and column number, with row bits above column bits. -/
@[expose] def index (a b : ℕ) : ℕ := 2 * spread a + spread b

/-- Recover row bits from a Morton position. -/
@[expose] def row (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· / 2))

/-- Recover column bits from a Morton position. -/
@[expose] def column (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· % 2))

/-- The native spread-table recurrence needs only an earlier entry and the last binary bit. -/
theorem spread_eq (i : ℕ) : spread i = i % 2 + 4 * spread (i / 2) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [spread]
  · unfold spread
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hi.ne', Nat.ofDigits_cons]

/-- No bits are set in the spread of zero. -/
@[simp] theorem spread_zero : spread 0 = 0 := by simp [spread]

/-- Extract the last row bit and recurse on the remaining base-four digits. -/
theorem row_eq (z : ℕ) : row z = z % 4 / 2 + 2 * row (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [row]
  · unfold row
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- Extract the last column bit and recurse on the remaining base-four digits. -/
theorem column_eq (z : ℕ) : column z = z % 4 % 2 + 2 * column (z / 4) := by
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [column]
  · unfold column
    rw [Nat.digits_eq_cons_digits_div (by norm_num) hz.ne', List.map_cons, Nat.ofDigits_cons]

/-- Position zero has row zero. -/
@[simp] theorem row_zero : row 0 = 0 := by simp [row]

/-- Position zero has column zero. -/
@[simp] theorem column_zero : column 0 = 0 := by simp [column]

/-- The paired last binary bits form the last base-four digit. -/
theorem index_eq (a b : ℕ) :
    index a b = (2 * (a % 2) + b % 2) + 4 * index (a / 2) (b / 2) := by
  unfold index
  rw [spread_eq a, spread_eq b]
  ring

/-- A side-`2^k` square occupies exactly the first `4^k` Morton positions. -/
theorem index_lt {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : index a b < 4 ^ k := by
  induction k generalizing a b with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : b = 0 := by simpa using hb
    simp [index]
  | succ k ih =>
    rw [pow_succ] at ha hb
    have h := ih (a := a / 2) (b := b / 2) (by omega) (by omega)
    rw [index_eq, pow_succ]
    omega

/-- Each computed spread-table entry fits in the corresponding base-four square span. -/
theorem spread_lt {k i : ℕ} (hi : i < 2 ^ k) : spread i < 4 ^ k := by
  have h := index_lt hi (show 0 < 2 ^ k by positivity)
  simp only [index, spread_zero, Nat.add_zero] at h
  omega

private theorem row_column_index (a b : ℕ) : row (index a b) = a ∧ column (index a b) = b := by
  induction hm : a + b using Nat.strong_induction_on generalizing a b with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
      simp [index]
    · obtain ⟨hr, hc⟩ := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
      rw [row_eq, column_eq, index_eq]
      generalize index (a / 2) (b / 2) = z at hr hc
      rw [show (2 * (a % 2) + b % 2 + 4 * z) / 4 = z by omega, hr, hc]
      omega

/-- Row projection inverts the interleaved position. -/
@[simp] theorem row_index (a b : ℕ) : row (index a b) = a := (row_column_index a b).1

/-- Column projection inverts the interleaved position. -/
@[simp] theorem column_index (a b : ℕ) : column (index a b) = b := (row_column_index a b).2

/-- Re-interleaving the projections recovers every original position. -/
@[simp] theorem index_row_column (z : ℕ) : index (row z) (column z) = z := by
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp [index]
    · have h := ih (z / 4) (by omega)
      rw [index_eq, row_eq z, column_eq z]
      generalize row (z / 4) = a at h
      generalize column (z / 4) = b at h
      rw [show (z % 4 / 2 + 2 * a) / 2 = a by omega,
        show (z % 4 % 2 + 2 * b) / 2 = b by omega, h]
      omega

/-- Reading a contiguous quadrant is the same as shifting its row and column by half a side. -/
theorem row_column_quadrant {k t z : ℕ} (ht : t < 4) (hz : z < 4 ^ k) :
    row (t * 4 ^ k + z) = row z + t / 2 * 2 ^ k ∧
      column (t * 4 ^ k + z) = column z + t % 2 * 2 ^ k := by
  induction k generalizing z with
  | zero =>
    obtain rfl : z = 0 := by simpa using hz
    rw [row_eq, column_eq, pow_zero, pow_zero, Nat.mul_one, Nat.add_zero,
      Nat.mod_eq_of_lt ht, Nat.div_eq_of_lt ht, row_zero, column_zero]
    omega
  | succ k ih =>
    obtain ⟨hr, hc⟩ := ih (z := z / 4) (by rw [pow_succ] at hz; omega)
    have hp : t * 4 ^ (k + 1) = 4 * (t * 4 ^ k) := by rw [pow_succ]; ring
    rw [row_eq, column_eq, row_eq z, column_eq z, hp,
      show (4 * (t * 4 ^ k) + z) % 4 = z % 4 by omega,
      show (4 * (t * 4 ^ k) + z) / 4 = t * 4 ^ k + z / 4 by omega, hr, hc, pow_succ 2]
    constructor <;> ring

/-- Projection of an admitted Morton position remains inside the corresponding square. -/
theorem row_column_lt {k z : ℕ} (hz : z < 4 ^ k) : row z < 2 ^ k ∧ column z < 2 ^ k := by
  induction k generalizing z with
  | zero =>
    obtain rfl : z = 0 := by simpa using hz
    simp
  | succ k ih =>
    have h := ih (z := z / 4) (by rw [pow_succ] at hz; omega)
    rw [row_eq, column_eq, pow_succ]
    omega

end Nat.Morton
