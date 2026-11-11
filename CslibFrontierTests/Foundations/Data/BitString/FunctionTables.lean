/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of CslibFrontier.Foundations.Data.BitString.FunctionTables)

public import CslibFrontier.Foundations.Data.BitString.FunctionTables

/-! # Tests for `Cslib.BitString.decodeTables` -/

namespace CslibFrontierTests.BitString.FunctionTables

open Cslib Cslib.BitString Finset

-- 1. Block layout: with blocks of width 2, the table of the second function starts at bit 2.
example : decodeTables 2 (fun _ : Fin 2 => 1) [false, true, true, false] 1 ![false] = true := by
  rw [decodeTables_apply]
  decide

example : decodeTables 2 (fun _ : Fin 2 => 1) [false, true, true, false] 1 ![true] = false := by
  rw [decodeTables_apply]
  decide

-- 2. Missing bits read `false`: a one-bit list leaves the second table all `false`.
example (y : BitString 2) : decodeTables 4 (fun _ : Fin 2 => 2) [true] 1 y = false := by
  rw [decodeTables_apply]
  revert y
  decide

-- 3. Uniformity: one family of a single 1-input function is decoded from exactly two of the
-- `2 ^ 3` strings, since bit 2 is never read.
example : #{r : Fin 3 → Bool | decodeTables 2 (fun _ => 1) (List.ofFn r) ∈
    ({fun _ _ => true} : Finset ((v : Fin 1) → BooleanFunction 1))} = 2 := by
  have h := card_filter_decodeTables_mem_mul (n := 1) (B := 2) (p := 3) (ℓ := fun _ => 1)
    (by decide) (by decide) {fun _ _ => true}
  simp only [Finset.card_singleton, Finset.univ_unique, Finset.sum_singleton] at h
  omega

-- 4. The counting form a randomized reduction uses: if at most a third of the families are bad,
-- at most a third of the random strings decode to a bad family.
example {n B p : ℕ} {ℓ : Fin n → ℕ} (hℓ : ∀ v, 2 ^ ℓ v ≤ B) (hp : n * B ≤ p)
    (S : Finset ((v : Fin n) → BooleanFunction (ℓ v)))
    (hS : 3 * #S ≤ Fintype.card ((v : Fin n) → BooleanFunction (ℓ v))) :
    3 * #{r : Fin p → Bool | decodeTables B ℓ (List.ofFn r) ∈ S} ≤ 2 ^ p := by
  simpa using mul_card_filter_decodeTables_mem_le (b := 1) hℓ hp (by simpa using hS)

end CslibFrontierTests.BitString.FunctionTables
