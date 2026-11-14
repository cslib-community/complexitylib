/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Logic/Equiv/Fin/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Appending tuples in the other order

`finAddFlip : Fin (m + n) ≃ Fin (n + m)` exchanges the two blocks of indices. Reading the tuple
`Fin.append v u` through it gives `Fin.append u v`: swapping the blocks of indices undoes swapping
the tuples.

## Main results

* `Fin.append_comp_finAddFlip`: `Fin.append v u ∘ finAddFlip = Fin.append u v`.
-/

public section

namespace Fin

/-- Reading `Fin.append v u` through `finAddFlip` gives `Fin.append u v`. -/
theorem append_comp_finAddFlip {α : Type*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) :
    Fin.append v u ∘ finAddFlip = Fin.append u v := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, finAddFlip_apply_castAdd, append_right, append_left]
  · simp only [Function.comp_apply, finAddFlip_apply_natAdd, append_right, append_left]

end Fin
