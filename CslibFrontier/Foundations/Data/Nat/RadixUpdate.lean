/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.Radix
import CslibFrontier.Foundations.Data.Finset.ApplyUpdate

/-!
# Updating one digit of a finite-function radix code

These weighted-digit identities reuse Mathlib's finite-function enumeration and sum
updates. The concrete client computes a child box's native encoding-array index by
replacing a P0 digit with one of the ten term digits, without rebuilding the string.
-/

public section

namespace Nat

open Finset

/-- Replacing one digit changes exactly its weighted contribution to the code. -/
theorem finFunctionFinEquiv_update_add {b L : ℕ} (f : Fin L → Fin b) (i : Fin L)
    (d : Fin b) :
    (finFunctionFinEquiv (Function.update f i d)).val + (f i).val * b ^ i.val =
      (finFunctionFinEquiv f).val + d.val * b ^ i.val := by
  rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply,
    sum_apply_update_of_mem (mem_univ i) (fun j (c : Fin b) => c.val * b ^ j.val),
    ← add_sum_erase univ (fun j => (f j).val * b ^ j.val) (mem_univ i)]
  ac_rfl

/-- Decreasing one digit computes its new code by a single exact natural subtraction. -/
theorem finFunctionFinEquiv_update_of_le {b L : ℕ} (f : Fin L → Fin b) (i : Fin L)
    (d : Fin b) (hd : d.val ≤ (f i).val) :
    (finFunctionFinEquiv (Function.update f i d)).val =
      (finFunctionFinEquiv f).val - ((f i).val - d.val) * b ^ i.val := by
  have h := finFunctionFinEquiv_update_add f i d
  have hm := Nat.mul_le_mul_right (b ^ i.val) hd
  rw [Nat.sub_mul]
  omega

end Nat
