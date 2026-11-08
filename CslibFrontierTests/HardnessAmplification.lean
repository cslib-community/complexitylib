/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.Circuit.Boolean.XorLemma

/-! Impagliazzo's hard-core lemma and Yao's XOR lemma: a concrete hard-core measure, the
parameters of the hard-core lemma, the `k`-fold XOR on concrete inputs, and the combinatorial XOR
lemma on a tight instance. -/

namespace ComplexityTests.HardnessAmplification

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Finset

/-! ### A concrete hard-core measure -/

/-- Against circuits without gates, which compute coordinate projections, the uniform measure is
a hard-core measure of density `1` and advantage `0` for parity on two bits: each projection
agrees with parity on exactly half of the inputs. -/
example : IsHardCoreMeasure (parity 2) 0 1 0 fun _ => 1 := by
  refine ⟨fun _ => ⟨zero_le_one, le_rfl⟩, by norm_num, fun g hg => ?_⟩
  have hproj : ∃ i, g = fun x => x i := by
    by_contra! h
    exact absurd (one_le_complexity_single (I := interpretation) h) (by omega)
  obtain ⟨i, rfl⟩ := hproj
  have hcount : ∀ i : Fin 2, #{x : BitString 2 | x i = parity 2 x} = 2 := by decide
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, hcount i, BitString.card]
  norm_num

/-! ### The parameters of the hard-core lemma -/

/-- With `δ = ε = 1 / 2`, six rounds suffice (`3 ε² δ² 6 = 9 / 8 ≥ 1`): hardness for size
`6 s + 98` gives a hard-core measure of density `1 / 2` against size `s` with advantage `1 / 2`. -/
example {n s : ℕ} (f : BooleanFunction n)
    (hf : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ 6 * s + 98 →
      (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - 1 / 2) :
    ∃ M, IsHardCoreMeasure f s (1 / 2) (1 / 2) M :=
  exists_isHardCoreMeasure (T := 6) (by norm_num) (by norm_num) (by norm_num) hf

/-- Yao's XOR lemma with `δ = 1 / 2`, `ε = 1 / 4` and twenty-four rounds
(`3 ε² δ² 24 = 9 / 8 ≥ 1`). -/
example {n s : ℕ} (f : BooleanFunction n)
    (hf : ∀ g : BooleanFunction n,
      complexity interpretation (single g) ≤ 24 * (s + 3) + (2 + 24 * (2 * (24 + 2))) →
        (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - 1 / 2)
    (k : ℕ) (g : BooleanFunction (k * n)) (hg : complexity interpretation (single g) ≤ s) :
    (#{x | g x = xorPower f k x} : ℝ) / 2 ^ (k * n) ≤
      1 / 2 + 1 / 4 + (1 / 2 - 1 / 4) * (1 - 1 / 2) ^ k :=
  card_eq_xorPower_div_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) hf k hg

/-! ### The `k`-fold XOR -/

/-- The three-fold XOR of the identity on one bit is the parity of three bits. -/
example : xorPower (fun x : BitString 1 => x 0) 3 ![true, false, true] = false := by decide

example : xorPower (fun x : BitString 1 => x 0) 3 ![true, true, true] = true := by decide

/-- The two-fold XOR of the conjunction of two bits. -/
example : xorPower (fun x : BitString 2 => x 0 && x 1) 2 ![true, true, true, false] = true := by
  decide

/-! ### The combinatorial XOR lemma is tight -/

/-- A constant function agrees with the identity on half of the bits, and with the XOR of two
bits on half of the pairs, which is exactly the bound `(1 / 2) 2 ^ 2 + (1 / 2) (2 - 2) ^ 2`. -/
example : (#{t : Fin 2 → Bool | false = ∑ i, id (t i)} : ℝ) ≤
    (1 / 2 + 0) * Fintype.card Bool ^ 2 +
      (1 / 2 - 0) * (Fintype.card Bool - ∑ _y : Bool, (1 : ℝ)) ^ 2 :=
  card_eq_sum_le id (M := fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) 2 (fun _ => false)
    fun _ _ b => by cases b <;> norm_num [filter_eq, filter_eq']

/-- The bound above is attained: the constant `false` agrees with the XOR on two of four pairs. -/
example : #{t : Fin 2 → Bool | false = ∑ i, id (t i)} = 2 := by decide

end ComplexityTests.HardnessAmplification
