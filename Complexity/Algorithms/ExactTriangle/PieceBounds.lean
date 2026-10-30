/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Splitting

/-!
# Numeric coordinates of ExactTriangle pieces

These bounds connect the existing finite pieces with the truncated original-vertex intervals
used by both native matrix preparation and witness recovery. They expose the same coordinate
facts previously private to the prepared-adjacency consumer, without changing the finite pieces.
-/

public section

namespace Cslib.Algorithms.ExactTriangle

/-- The active piece/label rectangle fits in the source middle dimension. -/
theorem pieceLength_mul_le_of_mem_sqrtPrimeWindow {D g p n k : ℕ} (hg : 1 ≤ g)
    (hp : p ∈ Nat.sqrtPrimeWindow D) :
    min (pieceSize D g) (n - k * pieceSize D g) * p ≤ D := by
  have hpS : p ≤ sOf D := Nat.le_sqrt'.mpr (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).2.2.le
  have hlen : min (pieceSize D g) (n - k * pieceSize D g) ≤ sOf D :=
    (min_le_left _ _).trans (pieceSize_le_sOf hg)
  exact (Nat.mul_le_mul hlen hpS).trans (Nat.sqrt_le D)

/-- An original piece vertex has its computed local coordinate in the actual truncated interval. -/
theorem piece_coordinate {n D g k : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g)
    (c : Fin n) (hc : c ∈ piece n D g k) :
    k * pieceSize D g + c.val % pieceSize D g = c.val ∧
      c.val % pieceSize D g < min (pieceSize D g) (n - k * pieceSize D g) := by
  have hB := pieceSize_pos hD hg
  have hdiv := (mem_piece c).mp hc
  have hsplit := Nat.div_add_mod c.val (pieceSize D g)
  rw [hdiv, Nat.mul_comm] at hsplit
  have hmod := Nat.mod_lt c.val hB
  exact ⟨hsplit, lt_min hmod (by have := c.isLt; omega)⟩

/-- The finite piece is precisely its original-coordinate truncated interval. -/
theorem mem_piece_iff_interval {n D g k : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) (c : Fin n) :
    c ∈ piece n D g k ↔ k * pieceSize D g ≤ c.val ∧
      c.val < k * pieceSize D g + min (pieceSize D g) (n - k * pieceSize D g) := by
  constructor
  · intro hc
    obtain ⟨he, hv⟩ := piece_coordinate hD hg c hc
    omega
  · rintro ⟨hlo, hhi⟩
    apply (mem_piece c).mpr
    have hB := pieceSize_pos hD hg
    have hsmall : c.val - k * pieceSize D g < pieceSize D g := by
      have := min_le_left (pieceSize D g) (n - k * pieceSize D g)
      omega
    have he : c.val = k * pieceSize D g + (c.val - k * pieceSize D g) := by omega
    have hsmall' : c.val - pieceSize D g * k < pieceSize D g := by
      simpa only [Nat.mul_comm k (pieceSize D g)] using hsmall
    rw [he, Nat.mul_comm k (pieceSize D g), Nat.mul_add_div hB,
      Nat.div_eq_of_lt hsmall', Nat.add_zero]

end Cslib.Algorithms.ExactTriangle
