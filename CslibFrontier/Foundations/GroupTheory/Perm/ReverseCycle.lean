/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `GroupTheory/Perm/Cycle/Type.lean`)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Reversing one cycle of a permutation

`Equiv.Perm.reverseCycle σ x` is the permutation that runs the cycle of `σ` through `x`
backwards and agrees with `σ` everywhere else: it sends `y` to `σ⁻¹ y` when `y` is on the cycle of
`x` and to `σ y` otherwise. It is `σ * c⁻¹ * c⁻¹` for `c = σ.cycleOf x`, so it has the same sign
as `σ` (`Equiv.Perm.sign_reverseCycle`). It has the same cycles as sets
(`Equiv.Perm.support_cycleOf_reverseCycle`), reversing twice gives back `σ`
(`Equiv.Perm.reverseCycle_reverseCycle`), and it differs from `σ` when the cycle has odd
length (`Equiv.Perm.reverseCycle_ne`), since a cycle equals its reverse only when it has
length `2`.

This is the involution behind the standard cancellation of the permutations with an odd cycle
in the Leibniz expansion of the determinant of a skew-symmetric matrix, the step in the proof of
Tutte's determinant criterion for perfect matchings [Tutte1947]. The last result restates "all
cycles have even length" through `Equiv.Perm.cycleType` (`Equiv.Perm.forall_even_cycleType_iff`).

## Main definitions

* `Equiv.Perm.reverseCycle`: reverse the cycle of `σ` through `x`.

## Main results

* `Equiv.Perm.reverseCycle_apply`: the values of the reversed permutation.
* `Equiv.Perm.sign_reverseCycle`: reversing a cycle preserves the sign.
* `Equiv.Perm.support_cycleOf_reverseCycle`: reversing a cycle preserves every cycle as a set.
* `Equiv.Perm.reverseCycle_reverseCycle`: reversing twice is the identity.
* `Equiv.Perm.reverseCycle_ne`: reversing a cycle of odd length changes the permutation.
* `Equiv.Perm.forall_even_cycleType_iff`: all cycle lengths are even exactly when the support of
  every `cycleOf` has even size.

## References

* [W. T. Tutte, *The factorization of linear graphs*][Tutte1947]
-/

public section

open Finset

namespace Equiv.Perm

variable {α : Type*}

private theorem apply_inv_apply (σ : Perm α) (y : α) : σ (σ⁻¹ y) = y :=
  σ.apply_symm_apply y

private theorem inv_apply_apply (σ : Perm α) (y : α) : σ⁻¹ (σ y) = y :=
  σ.symm_apply_apply y

private theorem sameCycle_inv_apply_right' {σ : Perm α} {x y : α} :
    σ.SameCycle x (σ⁻¹ y) ↔ σ.SameCycle x y :=
  sameCycle_symm_apply_right

/-- If `ρ` moves every point within its `σ`-cycle, then every `ρ`-cycle lies inside a
`σ`-cycle. -/
theorem SameCycle.of_forall_sameCycle_apply {σ ρ : Perm α} (h : ∀ y, σ.SameCycle y (ρ y))
    {y z : α} (hyz : ρ.SameCycle y z) : σ.SameCycle y z := by
  obtain ⟨i, rfl⟩ := hyz
  induction i using Int.induction_on with
  | zero => exact SameCycle.refl _ _
  | succ n ih =>
    rw [add_comm, _root_.zpow_add, zpow_one, Perm.mul_apply]
    exact ih.trans (h _)
  | pred n ih =>
    rw [sub_eq_neg_add, _root_.zpow_add, _root_.zpow_neg_one, Perm.mul_apply]
    refine ih.trans ?_
    have := h (ρ⁻¹ ((ρ ^ (-(n : ℤ))) y))
    rw [apply_inv_apply] at this
    exact this.symm

variable [Fintype α] [DecidableEq α]

private theorem cycleOf_inv_apply_of_sameCycle {σ : Perm α} {x y : α} (h : σ.SameCycle x y) :
    (σ.cycleOf x)⁻¹ y = σ⁻¹ y := by
  rw [Perm.inv_eq_iff_eq, (sameCycle_inv_apply_right'.2 h).cycleOf_apply, apply_inv_apply]

private theorem cycleOf_inv_apply_of_not_sameCycle {σ : Perm α} {x y : α}
    (h : ¬ σ.SameCycle x y) : (σ.cycleOf x)⁻¹ y = y := by
  rw [Perm.inv_eq_iff_eq, cycleOf_apply_of_not_sameCycle h]

/-- Reverse the cycle of `σ` through `x`: the result sends `y` to `σ⁻¹ y` on that cycle and to
`σ y` elsewhere (`Equiv.Perm.reverseCycle_apply`). -/
def reverseCycle (σ : Perm α) (x : α) : Perm α :=
  σ * ((σ.cycleOf x)⁻¹ * (σ.cycleOf x)⁻¹)

theorem reverseCycle_apply (σ : Perm α) (x y : α) :
    reverseCycle σ x y = if σ.SameCycle x y then σ⁻¹ y else σ y := by
  simp only [reverseCycle, Perm.mul_apply]
  split_ifs with h
  · rw [cycleOf_inv_apply_of_sameCycle h,
      cycleOf_inv_apply_of_sameCycle (sameCycle_inv_apply_right'.2 h), apply_inv_apply]
  · rw [cycleOf_inv_apply_of_not_sameCycle h, cycleOf_inv_apply_of_not_sameCycle h]

/-- Reversing a cycle preserves the sign. -/
theorem sign_reverseCycle (σ : Perm α) (x : α) : sign (reverseCycle σ x) = sign σ := by
  rw [reverseCycle, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, Int.units_mul_self, mul_one]

/-- Reversing a cycle preserves the relation of lying on a common cycle. -/
theorem sameCycle_reverseCycle_iff {σ : Perm α} {x y z : α} :
    (reverseCycle σ x).SameCycle y z ↔ σ.SameCycle y z := by
  constructor
  · refine SameCycle.of_forall_sameCycle_apply fun y => ?_
    rw [reverseCycle_apply]
    split_ifs
    · exact sameCycle_inv_apply_right'.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
  · refine SameCycle.of_forall_sameCycle_apply fun y => ?_
    by_cases h : σ.SameCycle x y
    · have hy : reverseCycle σ x (σ y) = y := by
        rw [reverseCycle_apply, ite_eq_left (sameCycle_apply_right.2 h), inv_apply_apply]
      exact ⟨-1, by rw [_root_.zpow_neg_one, Perm.inv_eq_iff_eq, hy]⟩
    · exact ⟨1, by rw [zpow_one, reverseCycle_apply, ite_eq_right h]⟩

/-- Reversing a cycle preserves the support. -/
theorem mem_support_reverseCycle {σ : Perm α} {x y : α} :
    y ∈ (reverseCycle σ x).support ↔ y ∈ σ.support := by
  rw [mem_support, mem_support, reverseCycle_apply]
  split_ifs
  · rw [Ne, Perm.inv_eq_iff_eq, eq_comm]
  · rfl

/-- Reversing a cycle preserves every cycle as a set. -/
theorem support_cycleOf_reverseCycle (σ : Perm α) (x y : α) :
    ((reverseCycle σ x).cycleOf y).support = (σ.cycleOf y).support := by
  ext z
  rw [mem_support_cycleOf_iff, mem_support_cycleOf_iff, sameCycle_reverseCycle_iff,
    mem_support_reverseCycle]

/-- Reversing the same cycle twice gives back the permutation. -/
theorem reverseCycle_reverseCycle (σ : Perm α) (x : α) :
    reverseCycle (reverseCycle σ x) x = σ := by
  ext y
  by_cases h : σ.SameCycle x y
  · rw [reverseCycle_apply, ite_eq_left (sameCycle_reverseCycle_iff.2 h), Perm.inv_eq_iff_eq,
      reverseCycle_apply, ite_eq_left (sameCycle_apply_right.2 h), inv_apply_apply]
  · rw [reverseCycle_apply, ite_eq_right (mt sameCycle_reverseCycle_iff.1 h), reverseCycle_apply,
      ite_eq_right h]

/-- A point on a cycle of odd length is moved: fixed points have empty `cycleOf` support. -/
theorem apply_ne_of_odd_card_support_cycleOf {σ : Perm α} {x : α}
    (hx : Odd #(σ.cycleOf x).support) : σ x ≠ x := by
  intro h
  rw [(cycleOf_eq_one_iff σ).2 h, support_one, card_empty] at hx
  exact Nat.not_odd_zero hx

/-- Reversing a cycle of odd length changes the permutation. -/
theorem reverseCycle_ne {σ : Perm α} {x : α} (hx : Odd #(σ.cycleOf x).support) :
    reverseCycle σ x ≠ σ := by
  intro h
  have hσx := apply_ne_of_odd_card_support_cycleOf hx
  have h1 : σ⁻¹ x = σ x := by
    have := congrArg (· x) h
    simpa only [reverseCycle_apply, ite_eq_left (SameCycle.refl _ _)] using this
  have h2 : (σ ^ (2 : ℤ)) x = (σ ^ (0 : ℤ)) x := by
    rw [zpow_ofNat, pow_two, Perm.mul_apply, ← h1, apply_inv_apply, zpow_zero, one_apply]
  rw [zpow_eq_zpow_on_iff σ hσx] at h2
  have hL := two_le_card_support_cycleOf_iff.2 hσx
  obtain ⟨k, hk⟩ := hx
  rw [Int.zero_emod, Int.emod_eq_of_lt (by norm_num) (by omega)] at h2
  omega

/-- All cycle lengths of `σ` are even exactly when the cycle of every point has a support of even
size (fixed points have empty `cycleOf` support). -/
theorem forall_even_cycleType_iff {σ : Perm α} :
    (∀ n ∈ σ.cycleType, Even n) ↔ ∀ x, Even #(σ.cycleOf x).support := by
  constructor
  · intro h x
    by_cases hx : σ x = x
    · rw [(cycleOf_eq_one_iff σ).2 hx, support_one, card_empty]
      exact Even.zero
    · refine h _ ?_
      rw [cycleType_def]
      exact Multiset.mem_map_of_mem _ (cycleOf_mem_cycleFactorsFinset_iff.2 (mem_support.2 hx))
  · intro h n hn
    rw [cycleType_def, Multiset.mem_map] at hn
    obtain ⟨c, hc, rfl⟩ := hn
    have hcyc := (mem_cycleFactorsFinset_iff.1 hc).1
    obtain ⟨a, ha⟩ := hcyc.nonempty_support
    rw [Function.comp_apply, cycle_is_cycleOf ha hc]
    exact h a

end Equiv.Perm
