/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Summing Boolean assignments with a forced-zero suffix

## Main results

* `Cslib.BitString.sum_padding_false`: each prefix has exactly one all-false suffix, so forced
  padding contributes one rather than a power of two.
-/

public section

namespace Cslib.BitString

open Classical in
/-- Summing assignments with an all-false padding suffix counts each prefix exactly once. -/
theorem sum_padding_false {R : Type*} [AddCommMonoid R] (M q : ℕ) (f : (Fin M → Bool) → R) :
    (∑ x : Fin (M + q) → Bool,
      if ∀ i : Fin q, x (Fin.natAdd M i) = false then f (fun i => x (Fin.castAdd q i)) else 0) =
        ∑ x : Fin M → Bool, f x := by
  rw [← (Fin.appendEquiv M q).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.appendEquiv_apply, Fin.append_left, Fin.append_right]
  have hiff (y : Fin q → Bool) : (∀ i, y i = false) ↔ y = fun _ => false :=
    ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp [hiff]

end Cslib.BitString
