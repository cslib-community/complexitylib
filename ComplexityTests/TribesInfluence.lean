/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.BooleanAnalysis.TribesJunta
import Complexity.Foundations.Data.Finset.ExpectPi

/-!
# The influences of Tribes, and Tribes far from small juntas

Concrete values and instances for `Complexity.Foundations.BooleanAnalysis.TribesInfluence` and
`Complexity.Foundations.BooleanAnalysis.TribesJunta`. `Tribes_{2,2}` on four bits is the nearly
balanced Tribes for `w = 2` (`tribesSize 2 = 2`); each bit has influence `3 / 8`, its total
influence is `3 / 2` and its variance is `63 / 64`. `Tribes_{1,3}`, the `OR` of three bits, has
influences `1 / 4`. Every function of three of the four bits is `1 / 256`-far from `Tribes_{2,2}`,
while the `3 n / 4` hypothesis cannot be dropped, since Tribes is a function of all its bits. The
sharpness of KKL and the necessity of Friedgut's exponential are instantiated at `c = 9` and
`K = 4`.
-/

namespace ComplexityTests.TribesInfluence

open Finset Function Cslib Cslib.BitString
open scoped BigOperators

/-! ### Independent bits -/

-- Some of two uniformly random bits is `false` with probability `3 / 4`.
example : 𝔼 x : Fin 2 → Bool, (if ∃ i ∈ univ, x i = false then (1 : ℝ) else 0) = 3 / 4 := by
  rw [expect_ite_exists_mem_eq, card_univ, Fintype.card_fin]
  norm_num

-- Two independent uniformly random bits are both `true` with probability `1 / 4`.
example : 𝔼 y : Fin 2 → Bool, ∏ j, (if y j = true then (1 : ℝ) else 0) = 1 / 4 := by
  rw [← Fintype.prod_expect fun (_ : Fin 2) (b : Bool) => if b = true then (1 : ℝ) else 0]
  simp only [Fintype.expect_bool, prod_const, card_univ, Fintype.card_fin]
  norm_num

/-! ### Exact influences -/

-- Each bit of `Tribes_{2,2}` has influence `2 ^ (-1) (3 / 4) = 3 / 8`.
example (k : Fin (2 * 2)) : influence k (fun x => signVal (tribes 2 2 x)) = 3 / 8 := by
  rw [influence_tribes]
  norm_num

-- `Tribes_{2,2}` has total influence `4 · 3 / 8 = 3 / 2`.
example : totalInfluence (fun x => signVal (tribes 2 2 x)) = 3 / 2 := by
  rw [totalInfluence_tribes]
  norm_num

-- `Tribes_{1,3}` is the `OR` of three bits; each has influence `1 / 4`.
example (k : Fin (3 * 1)) : influence k (fun x => signVal (tribes 1 3 x)) = 1 / 4 := by
  rw [influence_tribes]
  norm_num

/-- The nearly balanced number of tribes of width `2` is `2`. -/
theorem tribesSize_two : tribesSize 2 = 2 := by
  have h1 := two_pow_sub_one_le_tribesSize (w := 2) (by norm_num)
  have h2 := tribesSize_lt_two_pow 2
  have h3 := one_div_two_le_pow_tribesSize 2
  norm_num at h1 h2
  interval_cases h : tribesSize 2
  · rfl
  · norm_num at h3

-- `Tribes_{2,2}` has variance `1 - (1 - 2 · 7 / 16) ^ 2 = 63 / 64`, above the bound `3 / 4`.
example : 𝔼 x, (signVal (tribes 2 2 x) - 𝔼 y, signVal (tribes 2 2 y)) ^ 2 = 63 / 64 := by
  rw [expect_sub_expect_sq_signVal]
  simp only [signVal_eq_one_sub_two_mul_bitVal]
  rw [expect_sub_distrib, Fintype.expect_const, ← mul_expect, expect_bitVal_tribes]
  norm_num

/-! ### Explicit bounds and the sharpness of KKL -/

-- At `w = 2`, on `n = 4` bits: `log 4 / 16 ≤ 3 / 8 ≤ 6 log 4 / 4`.
example (k : Fin (tribesSize 2 * 2)) :
    Real.log (tribesSize 2 * 2 : ℕ) / (4 * (tribesSize 2 * 2 : ℕ)) ≤
        influence k (fun x => signVal (tribes 2 (tribesSize 2) x)) ∧
      influence k (fun x => signVal (tribes 2 (tribesSize 2) x)) ≤
        6 * Real.log (tribesSize 2 * 2 : ℕ) / (tribesSize 2 * 2 : ℕ) :=
  ⟨log_div_le_influence_tribes (by norm_num) k, influence_tribes_le le_rfl k⟩

-- No constant `c = 9 > 8` works in KKL for all large `n`: beyond `n₀ = 100` there is a function
-- all of whose influences are below `9 Var log n / n`.
example : ∃ (n : ℕ) (f : BitString n → Bool), 100 ≤ n ∧ ∀ k,
    influence k (fun x => signVal (f x)) <
      9 * (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * Real.log n / n :=
  exists_forall_influence_lt_mul_log_div (by norm_num) 100

/-! ### Tribes is far from every small junta -/

-- Every function of at most three of the four bits of `Tribes_{2,2}` is `1 / 256`-far from it.
example {J : Finset (Fin (tribesSize 2 * 2))} {g : BitString (tribesSize 2 * 2) → Bool}
    (hJ : #J ≤ 3) (hg : DependsOn g (J : Set (Fin (tribesSize 2 * 2)))) :
    1 / 256 ≤ (hammingDist (tribes 2 (tribesSize 2)) g : ℝ) / 2 ^ (tribesSize 2 * 2) :=
  one_div_256_le_hammingDist_tribes_div (by norm_num) (by have := tribesSize_two; omega) hg

-- The `3 n / 4` hypothesis cannot be dropped: Tribes is a function of all of its bits and is at
-- distance `0` from itself.
example : DependsOn (tribes 2 2) ((univ : Finset (Fin (2 * 2))) : Set (Fin (2 * 2))) ∧
    ¬1 / 256 ≤ (hammingDist (tribes 2 2) (tribes 2 2) : ℝ) / 2 ^ (2 * 2) :=
  ⟨fun _ _ h => congrArg (tribes 2 2) (funext fun i => h i (mem_univ i)), by simp⟩

-- Friedgut's exponential is necessary, at `K = 4`: some function of total influence at most `4`
-- is `1 / 256`-close to no function of at most `(3 / 16) 2 ^ 2 = 3 / 4` coordinates.
example : ∃ (n : ℕ) (f : BitString n → Bool), totalInfluence (fun x => signVal (f x)) ≤ 4 ∧
    ∀ (J : Finset (Fin n)) (g : BitString n → Bool), DependsOn g (J : Set (Fin n)) →
      (hammingDist f g : ℝ) / 2 ^ n < 1 / 256 → 3 / 16 * (2 : ℝ) ^ ((4 : ℝ) / 2) < #J :=
  exists_totalInfluence_le_lt_card_of_dependsOn le_rfl

end ComplexityTests.TribesInfluence
