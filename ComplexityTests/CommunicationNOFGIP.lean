/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.NOF.GeneralizedInnerProduct

/-!
# Tests for the cube bound and the generalized inner product

Checked instances of `NOF.gip`, its bias, and the Babai–Nisan–Szegedy bound, including the
one-player edge case where no protocol beats error `1 / 2`.
-/

open Cslib Cslib.Communication Cslib.Communication.NOF Finset Probability BitString
open scoped BigOperators

/-! ### The generalized inner product -/

/-- Three players with the strings `11`, `11`, `01`: only position `1` is all ones. -/
example : gip (fun i : Fin 3 => if i = 2 then ![false, true] else ![true, true]) = true := by
  decide

/-- Three players with the strings `11`, `11`, `11`: two positions are all ones. -/
example : gip (fun _ : Fin 3 => ![true, true]) = false := by
  decide

/-- With two players the generalized inner product is the inner product. -/
example (x y : BitString 4) : gip ![x, y] = x ⬝ᵥ y := gip_fin_two ![x, y]

/-! ### The bias -/

/-- With two players and one position the bias is `1 / 2`: `(-1) ^ (x ∧ y)` averages to `1 / 2`. -/
example : 𝔼 c : Fin 2 → BitString 1, signVal (gip c) = 1 / 2 := by
  rw [expect_signVal_gip]
  norm_num

/-- With three players and `n` positions the bias is `(3 / 4) ^ n`. -/
example (n : ℕ) : 𝔼 c : Fin 3 → BitString n, signVal (gip c) = (3 / 4) ^ n := by
  rw [expect_signVal_gip]
  norm_num

/-! ### The Babai–Nisan–Szegedy bound -/

/-- Three players with `1000` bits each need at least `30` bits of communication with public coins
and error `1 / 3`. -/
example {c : ℕ}
    (h : PublicCoin.ecomplexityFun (1 / 3) (gip : (Fin 3 → BitString 1000) → Bool) ≤ c) :
    30 ≤ c := by
  have := PublicCoin.two_mul_le_four_pow_mul_of_ecomplexityFun_gip_le h
  norm_num at this
  omega

/-- The lower bound is consistent with the trivial upper bound: player `1` writes player `0`'s
`n` bits, then player `0` knows everything and announces the value. -/
example (n : ℕ) :
    Protocol.ecomplexityFun (gip : (Fin 3 → BitString n) → Bool) ≤ n + 1 :=
  Protocol.ecomplexityFun_le_succ (X := fun _ : Fin 3 => BitString n) (i := 0) (j := 1)
    (by decide) (fun v => v ⟨0, by decide⟩) id (fun _ => rfl) gip

/-- **One player sees nothing**: a public-coin protocol of a single player for the generalized
inner product of `n ≥ 1` bits cannot have error below `1 / 2`, at any cost. -/
example {n c : ℕ} (hn : n ≠ 0) {γ : ℝ} (hγ : 0 ≤ γ)
    (h : PublicCoin.ecomplexityFun (1 / 2 - γ) (gip : (Fin 1 → BitString n) → Bool) ≤ c) :
    γ = 0 := by
  have hp := PublicCoin.pow_le_of_ecomplexityFun_gip_le hγ h
  norm_num [zero_pow hn] at hp
  linarith
