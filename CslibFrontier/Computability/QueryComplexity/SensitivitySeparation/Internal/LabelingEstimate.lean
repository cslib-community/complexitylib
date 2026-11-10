/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.LabelingBounds

/-!
# Superquadratic sensitivity separation: labeling estimate

Numerical estimates showing that the union bound over sixteen-vertex labeling events succeeds. For
`3 ≤ M` and `M ≤ r ^ 2`, a tournament on `k = 2 * M ^ 2 + 1` vertices satisfies `k ^ 16 < r ^ 104`,
which is exactly what is needed to beat the number of bad labelings.

## Main results

* `labeling_power_bound`: `(2 * M ^ 2 + 1) ^ 16 < r ^ 104` whenever `3 ≤ M ≤ r ^ 2`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/LabelingEstimate.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

namespace Internal

/-- If `3 ≤ M` and `M ≤ r ^ 2`, then `(2 * M ^ 2 + 1) ^ 16 * M ^ 20 ≤ 3 ^ 16 * r ^ 104`. -/
private theorem labeling_union_bound_numerator {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r ^ 2) :
    (2 * M ^ 2 + 1) ^ 16 * M ^ 20 ≤ 3 ^ 16 * r ^ 104 := by
  have hk : 2 * M ^ 2 + 1 ≤ 3 * M ^ 2 := by nlinarith
  have hp : M ^ 52 ≤ r ^ 104 := by
    calc
      M ^ 52 ≤ (r ^ 2) ^ 52 := Nat.pow_le_pow_left hMr 52
      _ = r ^ 104 := by rw [← pow_mul]
  calc
    (2 * M ^ 2 + 1) ^ 16 * M ^ 20 ≤ (3 * M ^ 2) ^ 16 * M ^ 20 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk 16)
    _ = 3 ^ 16 * M ^ 52 := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
    _ ≤ 3 ^ 16 * r ^ 104 := Nat.mul_le_mul_left _ hp

/-- For `3 ≤ M`, `3 ^ 16 < M ^ 20`. -/
private theorem labeling_union_bound_constant {M : ℕ} (hM : 3 ≤ M) :
    3 ^ 16 < M ^ 20 := by
  calc
    3 ^ 16 ≤ M ^ 16 := Nat.pow_le_pow_left hM 16
    _ < M ^ 20 := Nat.pow_lt_pow_right (by omega) (by omega)

/-- If `3 ≤ M` and `M ≤ r ^ 2`, then `(2 * M ^ 2 + 1) ^ 16 < r ^ 104`. -/
theorem labeling_power_bound {M r : ℕ} (hM : 3 ≤ M) (hMr : M ≤ r ^ 2) :
    (2 * M ^ 2 + 1) ^ 16 < r ^ 104 := by
  have hr : 0 < r := (Nat.pow_pos_iff.mp
    (lt_of_lt_of_le (show 0 < M by omega) hMr)).resolve_right (by omega)
  apply Nat.lt_of_mul_lt_mul_right (a := M ^ 20)
  calc
    (2 * M ^ 2 + 1) ^ 16 * M ^ 20 ≤ 3 ^ 16 * r ^ 104 := labeling_union_bound_numerator hM hMr
    _ < M ^ 20 * r ^ 104 := Nat.mul_lt_mul_of_pos_right (labeling_union_bound_constant hM)
      (pow_pos hr 104)
    _ = r ^ 104 * M ^ 20 := Nat.mul_comm _ _

end Internal

end Cslib.QueryComplexity.SensitivitySeparation
