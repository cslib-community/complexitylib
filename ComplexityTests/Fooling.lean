/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Probability.Fooling.OneSided
import Complexity.Foundations.BooleanAnalysis.FourierBitVal

/-! Tests for fooling by `k`-wise independent distributions: the xor sample space on three bits is
pairwise independent, fools a degree-`2` polynomial exactly, and does not fool the parity of all
three bits, which has degree `3`. -/

namespace ComplexityTests.Fooling

open Finset Cslib Cslib.BitString Cslib.Probability
open scoped BigOperators

/-- The xor sample space: two random bits and their sum. -/
private def xorSample : (Fin 2 → Bool) →+ Fin 3 → Bool where
  toFun s := ![s 0, s 1, s 0 + s 1]
  map_zero' := by decide
  map_add' := by decide

/-- The xor sample space is a pairwise independent family of bit strings. -/
private theorem isKWiseIndependentHash_xorSample :
    IsKWiseIndependentHash 2 fun s => xorSample s :=
  isKWiseIndependentHash_of_surjective xorSample (by decide)

/-- The distribution of the xor sample. -/
private noncomputable def X : PMF (Fin 3 → Bool) :=
  (PMF.uniformOfFintype (Fin 2 → Bool)).map fun s => xorSample s

/-- The xor sample is a pairwise independent distribution. -/
private theorem isKWiseIndependent_X : IsKWiseIndependent 2 X :=
  isKWiseIndependentHash_xorSample.isKWiseIndependent_map

/-- The degree-`2` polynomial `x₀ x₂ + x₁`. -/
private noncomputable def P (x : Fin 3 → Bool) : ℝ :=
  bitVal ℝ (x 0) * bitVal ℝ (x 2) + bitVal ℝ (x 1)

private theorem P_mem_lowDegree : P ∈ lowDegree ℝ (Fin 3) 2 := by
  have h02 := mul_mem_lowDegree (bitVal_mem_lowDegree (R := ℝ) (0 : Fin 3))
    (bitVal_mem_lowDegree (R := ℝ) (2 : Fin 3))
  rw [show (1 + 1 : ℕ) = 2 from rfl] at h02
  have h1 : (fun x : Fin 3 → Bool => bitVal ℝ (x 1)) ∈ lowDegree ℝ (Fin 3) 2 :=
    lowDegree_mono one_le_two (bitVal_mem_lowDegree 1)
  exact add_mem h02 h1

-- Pairwise independence fools the degree-`2` polynomial `x₀ x₂ + x₁` exactly.
example : Fools X 0 P :=
  isKWiseIndependent_X.fools_of_mem_lowDegree P_mem_lowDegree

-- The hypotheses of the one-sided bound are satisfiable: approximating the first bit by itself
-- (`F = F'`, so `a = 0`, and `b = 0`) under pairwise independence.
example : 𝔼 x : Fin 3 → Bool, bitVal ℝ (x 0) - 2 * 0 - 0 ≤
    ∑ x, (X x).toReal * bitVal ℝ (x 0) :=
  isKWiseIndependent_X.expect_bitVal_sub_le_of_eq_zero (F' := fun x => x 0)
    (bitVal_mem_lowDegree 0) le_rfl (fun x h => by simp [h]) (by simp) (by simp) (by simp)

/-- A real sum of bits counts the true ones. -/
private theorem sum_bitVal {α : Type*} [Fintype α] (b : α → Bool) :
    ∑ a, bitVal ℝ (b a) = #{a | b a = true} := by
  simp only [bitVal, sum_boole]

-- The non-example: every sample has even parity, so the expectation of the parity of all three
-- bits is `0` under the xor sample, while it is `1 / 2` under the uniform distribution. Pairwise
-- independence therefore does not `1 / 4`-fool this degree-`3` function.
example : ¬Fools X (1 / 4) fun x => bitVal ℝ (parityOn univ x) := by
  have hX : ∑ x, (X x).toReal * bitVal ℝ (parityOn univ x) = 0 := by
    rw [X, PMF.sum_map_mul]
    refine sum_eq_zero fun s _ => ?_
    rw [show parityOn univ (xorSample s) = false by revert s; decide, bitVal_false, mul_zero]
  have hU : 𝔼 x : Fin 3 → Bool, bitVal ℝ (parityOn univ x) = 1 / 2 := by
    rw [Fintype.expect_eq_sum_div_card, sum_bitVal,
      show #{x : Fin 3 → Bool | parityOn univ x = true} = 4 by decide]
    norm_num
  rw [Fools, hX, hU]
  norm_num

end ComplexityTests.Fooling
