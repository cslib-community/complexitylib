/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.Arithmetic.BitComposition
import CslibFrontier.Crypto.Primitives.Garbling.Arithmetic.CRT

/-! # Arithmetic garbling foundations: checked instances

Free operations and the multiplication gadget over `ℤ/5` with two-coordinate labels; bit
decomposition over `ℤ/9`; the linear bit-composition gadget with three input bits; exact
remainder by `3` in `ℤ/2^7`; and CRT reconstruction for the coprime moduli `4` and `9` inside
`ℤ/2^23`. Each instance checks that the hypotheses of the general theorems are satisfiable. -/

namespace CslibFrontierTests.GarblingArithmetic

open Cslib Cslib.Crypto.Garbling.Arithmetic

/-- A slope over `ℤ/5` whose last coordinate is the unit `1`, as in Li and Liu's offsets. -/
def slope : Fin 2 → ZMod 5 := ![3, 1]

-- Free addition and constant multiplication, by computation.
example : affineLabel ![1, 2] slope 2 + affineLabel ![4, 4] slope 4 =
    affineLabel ![0, 1] slope 1 := by
  decide

example : (3 : ZMod 5) • affineLabel ![1, 2] slope 2 = affineLabel ![3, 1] slope 1 := by
  decide

-- The unit coordinate makes the label injective.
example (k : Fin 2 → ZMod 5) : Function.Injective (affineLabel k slope) :=
  affineLabel_injective k slope (j := 1) isUnit_one

-- The multiplication gadget decodes to the product's label for every choice of coins.
example (r : ZMod 5) (b₁ b₀ : Fin 2 → ZMod 5) :
    (mulEncodeWith slope ![2, 0] r b₁ b₀ 3 4).decode = affineLabel ![2, 0] slope 2 :=
  decode_mulEncodeWith slope ![2, 0] r b₁ b₀ 3 4

-- Perfect privacy over `ℤ/5`: the encoding of `3 * 4` is simulated from the label of `2`.
example :
    (mulEncode slope ![2, 0] 3 4).eval = (mulSimulate (affineLabel ![2, 0] slope 2)).eval := by
  rw [eval_mulEncode, show (3 : ZMod 5) * 4 = 2 by decide]

-- Base-`3` digits of `7 = 1 + 2 * 3`, each written with `⌈log₂ 3⌉ = 2` bits.
example : digitWidth 3 = 2 := by decide

example : Radix.digit 3 7 0 = 1 ∧ Radix.digit 3 7 1 = 2 := by decide

-- Composition inverts decomposition on `ℤ/9`.
example (x : ZMod (3 ^ 2)) : bitComp 3 2 (bitDecomp 3 2 x) = x := bitComp_bitDecomp x

-- The linear bit-composition gadget with weights `1, 2, 4` over `ℤ/8` evaluates to the label of
-- the weighted sum of its input bits, for every choice of keys, permutation bits and pads.
example (s : Fin 2 → ZMod 8) (b : Fin 3 → Fin 2 → ZMod 8) (α : Fin 3 → Bool)
    (pad : Fin 3 → Bool → Fin 2 → ZMod 8) (z : Fin 3 → Bool) :
    linCompEval (linCompTable ![1, 2, 4] s b α pad) (fun i => z i ^^ α i)
        (fun i => pad i (z i)) =
      affineLabel (∑ i, b i) s (∑ i, ![1, 2, 4] i * ((z i).toNat : ZMod 8)) :=
  linCompEval_linCompTable _ s b α pad z

-- The active rows of three input bits are a uniform sharing of the output label.
example (s key : Fin 2 → ZMod 8) (z : Fin 3 → Bool) :
    (do
      let b ← ProbComp.sampleAdditiveShares 3 key
      return activeShares ![1, 2, 4] s z b : ProbComp (Fin 3 → Fin 2 → ZMod 8)).eval =
      (ProbComp.sampleAdditiveShares 3
        (affineLabel key s (∑ i, ![1, 2, 4] i * ((z i).toNat : ZMod 8)))).eval :=
  eval_activeShares _ s z key

-- Remainder by `3` in `ℤ/2^7` on the input `7 < 2^3`.
example : constMod 2 3 3 (7 : ZMod (2 ^ (2 * 3 + 1))) = 1 := by
  rw [constMod_eq_mod (by decide) (by decide) (by decide)]
  rfl

-- The multiplier for `p = 2`, `k = 3`, `N = 3` is `⌈2^5 / 3⌉ = 11 ≤ 2^4`.
example : Nat.constDivMultiplier 2 3 3 = 11 := by decide

/-- Two coprime moduli with product `36`. -/
def moduli : Fin 2 → ℕ := ![4, 9]

theorem moduli_pos : ∀ i, 0 < moduli i := by decide

theorem moduli_coprime : Pairwise (Function.onFun Nat.Coprime moduli) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

example : ∏ i, moduli i = 36 := by simp [moduli, Fin.prod_univ_two]

-- Each CRT coefficient is below `36`, and the residues `3` and `5` of `23` recombine to `23`
-- modulo `36`.
example (i : Fin 2) : crtCoeff moduli i < ∏ j, moduli j := crtCoeff_lt moduli_pos i

example : crtSum moduli 23 ≡ 23 [MOD ∏ i, moduli i] := crtSum_modEq moduli_pos moduli_coprime 23

-- Reconstruction of `23 mod 36` in `ℤ/2^23`, since `36 ^ 2 ≤ 2 ^ 11`.
example : constMod 2 11 (∏ i, moduli i) (crtSum moduli 23 : ZMod (2 ^ (2 * 11 + 1))) =
    ((23 % ∏ i, moduli i : ℕ) : ZMod (2 ^ (2 * 11 + 1))) :=
  constMod_crtSum moduli_pos moduli_coprime (by decide) (by decide) 23

end CslibFrontierTests.GarblingArithmetic
