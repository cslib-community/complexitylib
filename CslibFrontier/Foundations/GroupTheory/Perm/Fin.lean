/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `GroupTheory/Perm/Fin.lean`, next to `isCycle_finRotate_of_le`)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The single cycle of `finRotate`

All points of `Fin n` lie on one cycle of `finRotate n` (`Equiv.Perm.sameCycle_finRotate`): for
`n ≥ 2` it is a cycle with full support, and for `n ≤ 1` there is at most one point. So repeating
`w ↦ w + 1` and `w ↦ w - 1` (modulo `n`) leads from any point to any other, which is what the slot
graph of a simple graph on `Fin n` needs (`Cslib.RotationMap.reachable_slotGraph_iff`).

The values of `finRotate n` and of its inverse are the successor and the predecessor modulo `n`
(`val_finRotate`, `val_finRotate_symm`), the arithmetic a machine stepping along the cycle performs.

## Main results

* `Equiv.Perm.sameCycle_finRotate`: all points lie on the same cycle of `finRotate n`.
* `val_finRotate`, `val_finRotate_symm`: `finRotate n` and its inverse in values.
-/

@[expose] public section

/-- The successor of `finRotate`, in values. -/
theorem val_finRotate {n : ℕ} (i : Fin n) :
    (finRotate n i : ℕ) = if (i : ℕ) + 1 = n then 0 else (i : ℕ) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  rw [coe_finRotate]
  split_ifs with h₁ h₂ h₂ <;> simp_all [Fin.ext_iff]

/-- The predecessor of `finRotate`, in values. -/
theorem val_finRotate_symm {n : ℕ} (i : Fin n) :
    ((finRotate n).symm i : ℕ) = if (i : ℕ) = 0 then n - 1 else (i : ℕ) - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  split_ifs with h
  · have hi : i = 0 := Fin.ext h
    subst hi
    have : (finRotate (m + 1)).symm 0 = Fin.last m := by
      rw [Equiv.symm_apply_eq, finRotate_last]
    rw [this, Fin.val_last]
    rfl
  · exact coe_finRotate_symm_of_ne_zero (Fin.ext_iff.not.2 h)

namespace Equiv.Perm

/-- All points of `Fin n` lie on the single cycle of `finRotate n`. -/
theorem sameCycle_finRotate {n : ℕ} (a b : Fin n) : (finRotate n).SameCycle a b := by
  rcases lt_or_ge n 2 with hn | hn
  · have : Subsingleton (Fin n) := by
      refine ⟨fun x y ↦ Fin.ext ?_⟩
      omega
    rw [Subsingleton.elim a b]
  · have hsupp (x : Fin n) : finRotate n x ≠ x := by
      rw [← Equiv.Perm.mem_support, support_finRotate_of_le hn]
      exact Finset.mem_univ x
    exact (isCycle_finRotate_of_le hn).sameCycle (hsupp a) (hsupp b)

end Equiv.Perm
