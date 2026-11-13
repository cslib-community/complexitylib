/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.HardDistribution
import Mathlib.Tactic

/-! The hard-distribution steps of Lemma 6.3 of submission 865 on a function that needs them. -/

namespace CslibFrontierTests.CircuitHardDistribution
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Formula

/-- `(4 · 60 + 4)^{2^42} < 2 · 2^{2^60}`: `244 < 2^8`, so the left side is below `2^{2^45}`. -/
private theorem pow_lt_two_mul_two_pow {a b c : ℕ} (ha : a ≤ 2 ^ 8) (hbc : 8 * b ≤ c) :
    a ^ b < 2 * 2 ^ c := by
  have h₁ : a ^ b ≤ 2 ^ c :=
    (Nat.pow_le_pow_left ha b).trans ((pow_mul 2 8 b).symm.le.trans
      (Nat.pow_le_pow_right two_pos hbc))
  have h₂ : 0 < 2 ^ c := pow_pos two_pos c
  omega

private theorem count_lt : (4 * 60 + 4) ^ 2 ^ 42 < 2 * 2 ^ 2 ^ 60 :=
  pow_lt_two_mul_two_pow (by norm_num) (by norm_num)

/-- Some function on `60` bits has formula depth above `42`. -/
private theorem exists_deep : ∃ g : BooleanFunction 60, 42 < formulaDepth g :=
  exists_lt_formulaDepth count_lt

/-- **A nonvacuous instance.** For that function and `K = 1`, both steps apply: some distribution
puts weight below `1/7` on every point and defeats every formula of depth at most
`⌈log₂ 60⌉ + ⌈log₂ 1⌉ = 6` with accuracy below `9/14`. -/
example : ∃ g : BooleanFunction 60, ∃ ν : PMF (BitString 60),
    (∀ x, 7 * (1 : ℕ) * (ν x).toReal < 1) ∧ ∀ F : Formula signature 60,
      F.depthWith binaryCost ≤ Nat.clog 2 60 + Nat.clog 2 1 → accuracy ν g F < 9 / 14 := by
  obtain ⟨g, hg⟩ := exists_deep
  have h60 : Nat.clog 2 60 = 6 := by decide
  have h1 : Nat.clog 2 1 = 0 := by decide
  exact ⟨g, exists_spread_hardDistribution_of_lt_formulaDepth (K := 1) g (by omega)⟩

/-- The minimax-and-amplification step applied to the first bit, which some depth-0 formula
predicts with accuracy one under every distribution: it computes the first bit in depth at most
`0 + 18 + 3 ⌈log₂ 2⌉ = 21`. -/
example : ∃ G : Formula signature 2, G.Computes interpretation (fun x => x 0) ∧
    G.depthWith binaryCost ≤ 0 + 18 + 3 * Nat.clog 2 2 :=
  exists_computes_of_forall_exists_accuracy_ge _ 0 fun ν => ⟨.input 0, by simp, by
    have := Cslib.Probability.PMF.sum_toReal ν
    simp only [accuracy, eval_input, ite_true, mul_one]
    linarith⟩

end CslibFrontierTests.CircuitHardDistribution
