/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Block

/-!
# Prepending a block

## Main results

* `Cslib.BitString.blocksEquiv_symm_cons`: a head block followed by a flattened block array
  is the flattened array with that block prepended.
-/

public section

namespace Cslib.BitString

/-- Prepending a block commutes with flattening, under the canonical dimension cast. -/
theorem blocksEquiv_symm_cons {α : Type*} {count bits : ℕ}
    (a : Fin bits → α) (later : Fin count → Fin bits → α) :
    blocksEquiv.symm (Fin.cons a later) ∘
      Fin.cast (by rw [Nat.add_comm, ← Nat.succ_mul] : bits + count * bits =
        (count + 1) * bits) = Fin.append a (blocksEquiv.symm later) := by
  funext i
  cases i using Fin.addCases with
  | left i =>
    simp only [Function.comp_apply, Fin.append_left]
    rw [show Fin.cast _ (Fin.castAdd (count * bits) i) =
      finProdFinEquiv ((0 : Fin (count + 1)), i) by
        ext
        simp [finProdFinEquiv_apply_val]]
    simp [blocksEquiv_symm_apply]
  | right i =>
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective i
    simp only [Function.comp_apply, Fin.append_right]
    rw [show Fin.cast _ (Fin.natAdd bits (finProdFinEquiv (j, k))) =
      finProdFinEquiv (j.succ, k) by
        ext
        simp only [Fin.val_cast, Fin.val_natAdd, finProdFinEquiv_apply_val, Fin.val_succ,
          Nat.mul_add, Nat.mul_one]
        omega]
    simp [blocksEquiv_symm_apply]

end Cslib.BitString
