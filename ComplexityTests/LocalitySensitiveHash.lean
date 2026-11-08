/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.LocalitySensitiveHash.BitSampling
public import Complexity.Probability.LocalitySensitiveHash.MinHash
import Mathlib.Tactic.NormNum

/-!
# Tests for MinHash and locality-sensitive hashing

1. Concrete Jaccard similarities, including the conventions `J(∅, ∅) = 1` and disjoint sets.
2. Broder's theorem on `Fin 4`: exact MinHash collision probabilities `1/2`, `0` and `1`, and a
   concrete MinHash value under a transposition.
3. Exact AND/OR/banding laws on MinHash: two rows collide with probability `J²`.
4. Banding numerics in the setting `r = 5`, `b = 20` of [LeskovecRajaramanUllman2020],
   Section 3.4.2: pairs of similarity `0.8` are caught with probability above `0.9996`, pairs of
   similarity `0.2` with probability below `0.007`.
5. Nonvacuity of `IsLocalitySensitive`: bit sampling on `Fin 8 → Bool` is
   `(1, 4, 7/8, 1/2)`-sensitive, its banding with `k = 4`, `L = 10` separates near and far pairs
   (`≥ 0.9965` versus `≤ 0.48`), `exists_banded` applies, and a family failing the far bound.
6. Separation (`jaccard_eq_one_iff`) and the Jaccard triangle inequality on `Fin 4` and on
   `Finset ℕ`.
-/

public section

namespace ComplexityTests.LocalitySensitiveHash

open Cslib.Probability

/-! ### Jaccard similarity -/

example : jaccard ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 2 := by decide +kernel
example : jaccard ({0} : Finset (Fin 4)) {0, 1, 2, 3} = 1 / 4 := by decide +kernel
example : jaccard (∅ : Finset (Fin 4)) ∅ = 1 := by decide +kernel
example : jaccard ({0} : Finset (Fin 4)) {1} = 0 := by decide +kernel
example : jaccard (∅ : Finset (Fin 4)) {1} = 0 := by decide +kernel

/-! ### Broder's theorem on a concrete universe -/

/-- A uniformly random permutation of `Fin 4` gives `{0, 1, 2}` and `{1, 2, 3}` the same MinHash
with probability exactly `1/2`. -/
example : collisionProb (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) minHash
    ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 2 := by
  rw [collisionProb_minHash]
  have : jaccard ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 2 := by decide +kernel
  rw [this]
  norm_num

/-- Disjoint nonempty sets never collide. -/
example : collisionProb (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) minHash
    ({0} : Finset (Fin 4)) {1} = 0 := by
  rw [collisionProb_minHash]
  have : jaccard ({0} : Finset (Fin 4)) {1} = 0 := by decide +kernel
  rw [this, Rat.cast_zero]

/-- The empty set collides with itself, under the convention `J(∅, ∅) = 1`. -/
example : collisionProb (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) minHash
    (∅ : Finset (Fin 4)) ∅ = 1 := collisionProb_self _ _ _

/-- The transposition of `0` and `3` gives `{0, 1}` the least rank `1` and `{2, 3}` the least
rank `0`, so this permutation separates them. -/
example : minHash (Equiv.swap (0 : Fin 4) 3) {0, 1} = (1 : Fin 4) ∧
    minHash (Equiv.swap (0 : Fin 4) 3) {2, 3} = (0 : Fin 4) := by decide

/-! ### AND, OR and banding on MinHash -/

/-- Two independent MinHash rows of `{0, 1, 2}` and `{1, 2, 3}` both agree with probability
`(1/2)² = 1/4`. -/
example : collisionProb (PMF.iid (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) 2)
    (andHash minHash 2) ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 4 := by
  rw [collisionProb_andHash, collisionProb_minHash]
  have : jaccard ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 2 := by decide +kernel
  rw [this]
  norm_num

/-- Three independent MinHash rows of the same pair: some row agrees with probability
`1 - (1/2)³ = 7/8`. -/
example : orCollisionProb (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) minHash 3
    ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 7 / 8 := by
  rw [orCollisionProb_eq, collisionProb_minHash]
  have : jaccard ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 2 := by decide +kernel
  rw [this]
  norm_num

/-- Two bands of two MinHash rows: `1 - (1 - (1/2)²)² = 7/16`. -/
example : orCollisionProb (PMF.iid (PMF.uniformOfFintype (Equiv.Perm (Fin 4))) 2)
    (andHash minHash 2) 2 ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 7 / 16 := by
  rw [orCollisionProb_andHash_minHash]
  have : jaccard ({0, 1, 2} : Finset (Fin 4)) {1, 2, 3} = 1 / 2 := by decide +kernel
  rw [this, sCurve]
  norm_num

/-! ### Banding numerics ([LeskovecRajaramanUllman2020], Section 3.4.2) -/

/-- With `20` bands of `5` rows, pairs of similarity `0.8` become candidates with probability
above `0.9996`. -/
example : (0.9996 : ℝ) < sCurve 5 20 0.8 := by norm_num [sCurve]

/-- With `20` bands of `5` rows, pairs of similarity `0.2` become candidates with probability
below `0.007`. -/
example : sCurve 5 20 (0.2 : ℝ) < 0.007 := by norm_num [sCurve]

/-- The far-pair union bound `L p₂ ^ k` at similarity `0.2`: `20 · 0.2⁵ = 0.0064`. -/
example : sCurve 5 20 (0.2 : ℝ) ≤ 0.0064 :=
  (sCurve_le (by norm_num) le_rfl (by norm_num)).trans_eq (by norm_num)

/-! ### Bit sampling and nonvacuity of `IsLocalitySensitive` -/

/-- Bit sampling on `Fin 8 → Bool`, the coordinate projection with a uniform index. -/
noncomputable abbrev bitProb : (Fin 8 → Bool) → (Fin 8 → Bool) → ℝ :=
  collisionProb (PMF.uniformOfFintype (Fin 8)) fun i (z : Fin 8 → Bool) => z i

/-- Two words at Hamming distance `3` collide under bit sampling with probability `5/8`. -/
example : bitProb (fun i => decide (i.val < 3)) (fun _ => false) = 5 / 8 := by
  rw [bitProb, collisionProb_bitSampling]
  have : hammingDist (fun i : Fin 8 => decide (i.val < 3)) (fun _ => false) = 3 := by decide
  rw [this]
  norm_num

/-- Bit sampling on `8` coordinates is `(1, 4, 7/8, 1/2)`-sensitive for the Hamming distance. -/
theorem bitSampling_sensitive :
    IsLocalitySensitive bitProb (fun x y => (hammingDist x y : ℝ) ≤ 1)
      (fun x y => 4 ≤ (hammingDist x y : ℝ)) (7 / 8) (1 / 2) := by
  have h := isLocalitySensitive_bitSampling (n := Fin 8) (β := Bool) 1 4
  have e₁ : (1 : ℝ) - 1 / Fintype.card (Fin 8) = 7 / 8 := by norm_num
  have e₂ : (1 : ℝ) - 4 / Fintype.card (Fin 8) = 1 / 2 := by norm_num
  rw [e₁, e₂] at h
  exact h

/-- Banding with `4` rows and `10` bands separates the same pairs: near pairs collide with
probability at least `0.9965`, far pairs with probability at most `0.48`. -/
example : IsLocalitySensitive
    (orCollisionProb (PMF.iid (PMF.uniformOfFintype (Fin 8)) 4)
      (andHash (fun i (z : Fin 8 → Bool) => z i) 4) 10)
    (fun x y => (hammingDist x y : ℝ) ≤ 1) (fun x y => 4 ≤ (hammingDist x y : ℝ))
    0.9965 0.48 := by
  have h := bitSampling_sensitive.banded (by norm_num) (by norm_num) 4 10
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · exact le_trans (by norm_num [sCurve]) (h.le_of_near x y hxy)
  · exact (h.le_of_far x y hxy).trans (by norm_num [sCurve])

/-- `exists_banded` applies to bit sampling: some banding catches pairs at distance at most `1`
with probability at least `0.99` and pairs at distance at least `4` with probability at most
`0.01`. -/
example : ∃ k L : ℕ, IsLocalitySensitive
    (orCollisionProb (PMF.iid (PMF.uniformOfFintype (Fin 8)) k)
      (andHash (fun i (z : Fin 8 → Bool) => z i) k) L)
    (fun x y => (hammingDist x y : ℝ) ≤ 1) (fun x y => 4 ≤ (hammingDist x y : ℝ))
    (1 - 0.01) 0.01 := by
  obtain ⟨k, L, -, h⟩ := bitSampling_sensitive.exists_banded (δ := 0.01) (δ' := 0.01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨k, L, h⟩

/-- The sensitivity bounds are not automatic: bit sampling is not `(1, 4, 7/8, 1/4)`-sensitive,
because two words at distance `4` collide with probability `1/2 > 1/4`. -/
example : ¬ IsLocalitySensitive bitProb (fun x y => (hammingDist x y : ℝ) ≤ 1)
    (fun x y => 4 ≤ (hammingDist x y : ℝ)) (7 / 8) (1 / 4) := by
  intro h
  have hd : hammingDist (fun i : Fin 8 => decide (i.val < 4)) (fun _ => false) = 4 := by decide
  have hfar := h.le_of_far (fun i : Fin 8 => decide (i.val < 4)) (fun _ => false)
    (by rw [hd]; norm_num)
  rw [bitProb, collisionProb_bitSampling, hd] at hfar
  norm_num at hfar

/-- Charikar's triangle inequality for the Jaccard distance on a concrete triple. -/
example : 1 - jaccard ({0} : Finset (Fin 4)) {2} ≤
    (1 - jaccard ({0} : Finset (Fin 4)) {0, 1, 2}) +
      (1 - jaccard ({0, 1, 2} : Finset (Fin 4)) {2}) :=
  jaccard_triangle _ _ _

/-- Distinct sets have Jaccard similarity below `1`. -/
example : jaccard ({0, 1} : Finset (Fin 4)) {0, 1, 2} ≠ 1 := by
  rw [Ne, jaccard_eq_one_iff]
  decide

/-- The triangle inequality needs no order or finiteness on the ambient type: here sets of
naturals. -/
example : 1 - jaccard ({0} : Finset ℕ) {5} ≤
    (1 - jaccard ({0} : Finset ℕ) {0, 5}) + (1 - jaccard ({0, 5} : Finset ℕ) {5}) :=
  jaccard_triangle _ _ _

end ComplexityTests.LocalitySensitiveHash
