/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.Convolution

/-!
# Packing three convolution arrays into one

Adapted from Anthropic's `PaperStatements.lean` and
[FromNumbers.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem21a/ChanHe/FromNumbers.lean), at
`formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. Three-array convolution uses
Definition 2.2 of [ChanHe2020]. The four-way packing is an additional elementary step in that
formalization, not part of the Chan–He proof.

## Main definitions

* `HasConvolutionSolution`: three arrays with zero-based indices and `i + j < N`.
* `oneArray`: four-way interleaving with magnitude tags.

## Main results

* `oneArray_correct`: equivalence with the existing one-array `Convolution` predicate.
* `abs_oneArray_le`: packed magnitudes are at most `30W + 10`.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum

/-- Three-array convolution, with zero-based indices and the requirement `i + j < N`. -/
def HasConvolutionSolution (N : ℕ) (X Y Z : ℕ → ℤ) : Prop :=
  ∃ i j, i + j < N ∧ X i + Y j = Z (i + j)

/-! ### Three arrays in one -/

/-- **Three arrays in one.**  With `G = 3W + 1`, where `W` bounds the entries of the three arrays,
cell `4i + 1` holds `X i + G`, cell `4i + 2` holds `Y i + 3G`, cell `4i + 3` holds `Z i + 4G`, and
cell `4i` holds `10G`.  In an equation `y_u + y_v = y_{u+v}` the multiples of `G` have to cancel,
and they do so only when `u` and `v` have the remainders 1 and 2 modulo 4. -/
def oneArray (W : ℕ) (X Y Z : ℕ → ℤ) (u : ℕ) : ℤ :=
  let G : ℤ := 3 * W + 1
  if u % 4 = 1 then X (u / 4) + G else if u % 4 = 2 then Y (u / 4) + 3 * G
  else if u % 4 = 3 then Z (u / 4) + 4 * G else 10 * G


/-! ## Three arrays in one -/

section oneArray

variable {N W : ℕ} {X Y Z : ℕ → ℤ}

/-- The definition of `oneArray` with `G` written out. -/
private theorem oneArray_val (W : ℕ) (X Y Z : ℕ → ℤ) (u : ℕ) :
    oneArray W X Y Z u = if u % 4 = 1 then X (u / 4) + (3 * W + 1)
      else if u % 4 = 2 then Y (u / 4) + 3 * (3 * W + 1)
      else if u % 4 = 3 then Z (u / 4) + 4 * (3 * W + 1) else 10 * (3 * W + 1) := rfl

/-- A solution `(i, j)` of the three arrays gives the solution `(4i + 1, 4j + 2)` of the one
array. -/
private theorem oneArray_sol (W : ℕ) {i j : ℕ} (h : X i + Y j = Z (i + j)) :
    oneArray W X Y Z (4 * i + 1) + oneArray W X Y Z (4 * j + 2) =
      oneArray W X Y Z (4 * i + 1 + (4 * j + 2)) := by
  simp only [oneArray_val, show (4 * i + 1) % 4 = 1 by omega, show (4 * j + 2) % 4 = 2 by omega,
    show (4 * i + 1 + (4 * j + 2)) % 4 = 3 by omega, ↓reduceIte, Nat.reduceEqDiff]
  rw [show (4 * i + 1) / 4 = i by omega, show (4 * j + 2) / 4 = j by omega,
    show (4 * i + 1 + (4 * j + 2)) / 4 = i + j by omega]
  omega

/-- A solution of the one array is a solution of the three arrays: the multiples of `G = 3W + 1`
cancel only if the two indices have the remainders 1 and 2 modulo 4. -/
private theorem convSol_of_oneArray (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ)) {u v : ℕ} (huv : u + v < 4 * N)
    (h : oneArray W X Y Z u + oneArray W X Y Z v = oneArray W X Y Z (u + v)) :
    HasConvolutionSolution N X Y Z := by
  have hW : ∀ i < N, (-(W : ℤ) ≤ X i ∧ X i ≤ W) ∧ (-(W : ℤ) ≤ Y i ∧ Y i ≤ W) ∧
      (-(W : ℤ) ≤ Z i ∧ Z i ≤ W) :=
    fun i hi => ⟨abs_le.mp (hX i hi), abs_le.mp (hY i hi), abs_le.mp (hZ i hi)⟩
  have hWu := hW (u / 4) (by omega)
  have hWv := hW (v / 4) (by omega)
  have hWuv := hW ((u + v) / 4) (by omega)
  simp only [oneArray_val] at h
  by_cases h12 : u % 4 = 1 ∧ v % 4 = 2
  · refine ⟨u / 4, v / 4, by omega, ?_⟩
    rw [show u / 4 + v / 4 = (u + v) / 4 by omega]
    simp only [h12.1, h12.2, show (u + v) % 4 = 3 by omega, ↓reduceIte, Nat.reduceEqDiff] at h
    omega
  by_cases h21 : u % 4 = 2 ∧ v % 4 = 1
  · refine ⟨v / 4, u / 4, by omega, ?_⟩
    rw [show v / 4 + u / 4 = (u + v) / 4 by omega]
    simp only [h21.1, h21.2, show (u + v) % 4 = 3 by omega, ↓reduceIte, Nat.reduceEqDiff] at h
    omega
  · split_ifs at h <;> omega

/-- Three arrays to one, of four times the length. Here `W` bounds the entries below `N`. -/
theorem oneArray_correct (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ)) : HasConvolutionSolution N X Y Z ↔
      Convolution (4 * N) (oneArray W X Y Z) :=
  ⟨fun ⟨i, j, _, h⟩ => ⟨4 * i + 1, 4 * j + 2, by omega, oneArray_sol W h⟩,
    fun ⟨_, _, huv, h⟩ => convSol_of_oneArray hX hY hZ huv h⟩

/-- The entries of the one array have absolute value at most `30W + 10`. -/
theorem abs_oneArray_le (hX : ∀ i < N, |X i| ≤ (W : ℤ)) (hY : ∀ i < N, |Y i| ≤ (W : ℤ))
    (hZ : ∀ i < N, |Z i| ≤ (W : ℤ)) {u : ℕ} (hu : u < 4 * N) :
    |oneArray W X Y Z u| ≤ 30 * (W : ℤ) + 10 := by
  have := abs_le.mp (hX (u / 4) (by omega))
  have := abs_le.mp (hY (u / 4) (by omega))
  have := abs_le.mp (hZ (u / 4) (by omega))
  rw [oneArray_val, abs_le]
  split_ifs <;> constructor <;> omega

end oneArray

end Cslib.Algorithms.ThreeSum
