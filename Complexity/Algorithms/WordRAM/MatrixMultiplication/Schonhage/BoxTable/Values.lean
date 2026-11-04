/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Children

/-!
# Compact box values and original-array magnitude bounds

The stored value uses the existing finite `boxValue` recurrence. Its magnitude
bound covers every child partial sum as well as the final value, including cancellation.
The input arrays are arbitrary signed leaf functions, so encoded matrix arrays specialize
the same construction without changing its machine semantics.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The existing finite value associated to one actual directory slot. -/
@[expose] def slotValue {L : ℕ} (a b : Leaf L → ℤ) (s : ℕ) : ℤ :=
  boxValue a b (recordStars L s) (slotCube L s)

/-- Original-array bounds cover the complete finite recurrence at every cube. -/
theorem natAbs_boxValue_le {L A B : ℕ} (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (e : ℕ) (π : Cube L) : (boxValue a b e π).natAbs ≤ 10 ^ e * (A * B) := by
  induction e generalizing π with
  | zero =>
    simpa only [boxValue, pow_zero, one_mul, Int.natAbs_mul] using
      Nat.mul_le_mul (ha π.starsToP0) (hb π.starsToP0)
  | succ e ih =>
    rw [boxValue]
    split
    · calc
        _ ≤ ∑ lam : Term, (boxValue a b e (π.replace _ lam)).natAbs := Int.natAbs_sum_le _ _
        _ ≤ ∑ _lam : Term, 10 ^ e * (A * B) := sum_le_sum fun _ _ => ih _
        _ = 10 ^ (e + 1) * (A * B) := by
          simp only [sum_const, card_univ, card_term, smul_eq_mul]
          ring
    · simp

/-- Every eligible slot's value fits the original full-depth magnitude envelope. -/
theorem natAbs_slotValue_le {L H A B s : ℕ} (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hs : Eligible L H s) : (slotValue a b s).natAbs ≤ 10 ^ L * (A * B) := by
  have he : recordStars L s ≤ L := hs.1.trans (population_le _ _)
  exact (natAbs_boxValue_le a b ha hb _ _).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) he))

/-- With the existing tensor encodings, the stored recurrence is the original signed cube sum. -/
theorem slotValue_encoding {L m t s : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (hs : Eligible L (m - t) s) :
    slotValue (encodingL a) (encodingR b) s = Cube.val a b (slotCube L s) := by
  apply boxValue_eq_val
  exact mem_boxesWithStars.mpr ⟨slotCube_isBox hs, slotCube_star_count hs⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
