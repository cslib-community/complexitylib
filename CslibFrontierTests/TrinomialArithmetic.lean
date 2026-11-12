/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.TrinomialArithmetic

open Cslib Cslib.TrinomialArithmetic Turing.MultiTapeTM

-- Carryless multiplication differs from ordinary multiplication.
example : clmul 3 3 = 5 := by
  simp only [clmul_eq_foldr_bits]
  decide
example : clmul 0 23 = 0 := by
  simp only [clmul_eq_foldr_bits]
  decide
example : clmul 19 0 = 0 := by
  simp only [clmul_eq_foldr_bits]
  decide

-- In F4, X² = X + 1; the square of X + 1 is X.
example : mul 1 2 2 = 3 := by
  simp only [mul, reduce, clmul_eq_foldr_bits]
  decide
example : mul 1 3 3 = 2 := by
  simp only [mul, reduce, clmul_eq_foldr_bits]
  decide

-- For t=1, reduction uses X^6 + X^3 + 1, without enumerating F64.
example : mul 3 32 2 = 9 := by
  simp only [mul, reduce, clmul_eq_foldr_bits]
  decide
example : mul 3 63 63 = 58 := by
  simp only [mul, reduce, clmul_eq_foldr_bits]
  decide

example : run ⟨1, 1, 1, 2, 3, 1, 2⟩ = 1 := by
  simp only [run, hash4, eval4, mul, reduce, clmul_eq_foldr_bits]
  decide
example : ComputableInPolyTime run encInput encNat := computableInPolyTime_run

-- The executable F4 computation certifies the original abstract hash, including truncation.
example (c : Fin 4 → Fin 4) (u : Fin 4) :
    (Probability.trinomialPolyHash 0 4 4 1 c u).val =
      hash4 1 1 (c 0).val (c 1).val (c 2).val (c 3).val u.val := by
  exact (hash4_eq 0 4 1 c u u.isLt).symm

example (c : Fin 4 → Fin 64) (u : Fin 64) :
    (Probability.trinomialPolyHash 1 4 64 3 c u).val =
      hash4 3 3 (c 0).val (c 1).val (c 2).val (c 3).val u.val := by
  exact (hash4_eq 1 64 3 c u u.isLt).symm
