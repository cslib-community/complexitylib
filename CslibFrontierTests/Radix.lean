/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.Data.Nat.Radix

/-!
# Pure radix clients

Finite-tuple packing and recovery require only the mathematical radix API. The chosen
enumeration is fixed, but no claim about a particular order or native computation is needed.
-/

@[expose] public section

assert_not_exists Turing.MultiTapeNTM
assert_not_exists Turing.MultiTapeTM.ComputableTidilyInSpace

namespace CslibFrontierTests.Radix

open Cslib.Radix

/-- A nonconstant two-register fixture. -/
def values : Bool → ℕ
  | false => 1
  | true => 2

private theorem values_lt (i : Bool) : values i < 3 := by cases i <;> decide

-- A genuinely nonconstant finite tuple, without choosing an implementation or enumeration order.
example (i : Bool) : component 3 (pack 3 values) i = values i :=
  component_pack (by decide) values_lt i

example : pack 3 values < 3 ^ 2 := by
  simpa using pack_lt (by decide : 0 < 3) values_lt

-- List digits use Mathlib's little-endian packing directly.
example : digit 10 (Nat.ofDigits 10 [7, 0, 2]) 1 = 0 :=
  digit_ofDigits (by decide) _ (by simp) _ (by decide)

-- Positive-base capacity includes radix one, whose bounded digits must be zero.
example : Nat.ofDigits 1 [0, 0] < 1 ^ 2 :=
  Nat.ofDigits_lt_base_pow_length_of_pos (by decide) _ (by simp)

example (i : Bool) : component 1 (pack 1 (fun _ : Bool => 0)) i = 0 :=
  component_pack (by decide) (fun _ => by decide) i

-- The total operations retain the original zero-radix and empty-tuple conventions.
example (x : ℕ) : digit 0 x 0 = x := by simp [digit]
example (x i : ℕ) : digit 0 x (i + 1) = 0 := by simp [digit_eq_div_pow_mod]
example (B : ℕ) : pack B (fun i : Fin 0 => i.elim0) = 0 := by simp [pack]
example : pack 1 (fun i : Fin 0 => i.elim0) < 1 ^ 0 :=
  pack_lt (by decide) (fun i => i.elim0)

-- `finFunctionFinEquiv` order and high-zero prefix lemmas.
example (x : Fin 2 → Fin 3) :
    (finFunctionFinEquiv x : ℕ) =
      finFunctionFinEquiv (x ∘ Fin.castSucc) + (x (Fin.last 1) : ℕ) * 3 ^ 1 :=
  finFunctionFinEquiv_snoc x

example :
    (finFunctionFinEquiv (![1, 0] : Fin 2 → Fin 3) : ℕ) =
      finFunctionFinEquiv (fun j : Fin 1 => (![1, 0] : Fin 2 → Fin 3) (Fin.castLE (by decide) j)) :=
  finFunctionFinEquiv_eq_of_high_zero (by decide) (by decide)

example : (finFunctionFinEquiv (![2, 0] : Fin 2 → Fin 3) : ℕ) < 3 ^ 1 :=
  (finFunctionFinEquiv_lt_pow_iff (by decide : 1 ≤ 2) ![2, 0]).2 (by decide)

example : finFunctionFinEquiv (![2, 0] : Fin 2 → Fin 3) < finFunctionFinEquiv ![0, 1] :=
  (finFunctionFinEquiv_lt_iff ![2, 0] ![0, 1]).2
    ⟨1, by decide, fun j hj => absurd (Fin.le_last j) (not_le_of_gt hj)⟩

end CslibFrontierTests.Radix
