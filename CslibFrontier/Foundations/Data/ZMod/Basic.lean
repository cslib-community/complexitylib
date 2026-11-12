/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ZMod/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Properties of `ZMod` residues

Elementary properties of finite residues `ZMod m` for `[NeZero m]`: valuation preservation
under `ZMod.finEquiv`, residue subtraction on values without truncated subtraction below zero,
and equivalence of list range sums with residue sums.

## Main results

* `ZMod.val_finEquiv`: valuation preservation under `ZMod.finEquiv`.
* `ZMod.val_finEquiv_symm`: valuation preservation under `(ZMod.finEquiv m).symm`.
* `ZMod.val_sub_eq_mod`: residue subtraction on values.
* `ZMod.sum_range_eq_sum_zmod`: a sum over `List.range m` is a sum over `ZMod m`.
-/

public section

namespace ZMod

variable {m : ℕ} [NeZero m]

/-- Valuation is preserved under the ring equivalence `ZMod.finEquiv`. -/
lemma val_finEquiv (i : Fin m) : (ZMod.finEquiv m i).val = i.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m => rfl

/-- `(ZMod.finEquiv m).symm` preserves the underlying natural-number value. -/
lemma val_finEquiv_symm (z : ZMod m) :
    ((ZMod.finEquiv m).symm z).val = z.val := by
  rw [← val_finEquiv, RingEquiv.apply_symm_apply]

/-- A sum over `List.range m` is a sum over the residues modulo `m`. -/
lemma sum_range_eq_sum_zmod {A : Type*} [AddCommMonoid A] (m : ℕ) [NeZero m] (f : ℕ → A) :
    ((List.range m).map f).sum = ∑ z : ZMod m, f z.val := by
  rw [List.sum_map_range]
  exact Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ fun i => by
    change f i.val = f (ZMod.finEquiv m i).val
    rw [val_finEquiv]

/-- Residue subtraction on values, without truncated subtraction below zero. -/
lemma val_sub_eq_mod (u v : ZMod m) :
    (u - v).val = (u.val + m - v.val) % m := by
  have hv := v.val_lt
  rw [← ZMod.val_natCast, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, add_zero]

end ZMod
