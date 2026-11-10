/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Fourier
public import CslibFrontier.Computability.DecisionTree.Leaves
import CslibFrontier.Computability.DecisionTree.Granularity
import CslibFrontier.Foundations.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The spectral norm of decision trees

The *spectral norm* of a function on the cube is the sum `∑ S, |f̂ S|` of the absolute values of its
Fourier coefficients. A function of the output of a decision tree with values in `[-1, 1]` has
spectral norm at most the number of leaves of the tree
(`DecisionTree.sum_abs_fourierCoeff_le_leafCount`) [KushilevitzMansour1993]
[O'Donnell, Section 3.2][ODonnell2014]: each node averages the coefficients of its subtrees on `S`
and on `{i} ∆ S`, and `S ↦ {i} ∆ S` permutes the sets. Since a tree of depth `d` has at most
`2 ^ d` leaves (`DecisionTree.leafCount_le_two_pow_depth`), the spectral norm is also at most
`2 ^ d`. Together with granularity, each nonzero coefficient of a Boolean function of a tree of
depth `d ≥ 1` has absolute value at least `2 ^ (1 - d)`, so such a function has at most
`leafCount * 2 ^ (d - 1)` nonzero coefficients
(`DecisionTree.card_filter_fourierCoeff_signVal_ne_zero_le`) [O'Donnell, Section 3.2][ODonnell2014].
The leaf count and the depth are structural, so unreachable leaves and paths only weaken the bounds.

## Main results

* `Cslib.DecisionTree.sum_abs_fourierCoeff_le_leafCount`: the spectral norm of a `[-1, 1]`-valued
  function of a decision tree is at most its number of leaves.
* `Cslib.DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount`,
  `Cslib.DecisionTree.sum_abs_fourierCoeff_signVal_le_two_pow_depth`: the same for Boolean
  functions, and the bound by `2 ^ depth`.
* `Cslib.DecisionTree.card_filter_fourierCoeff_signVal_ne_zero_le`: the Fourier sparsity of a
  Boolean function of a decision tree is at most `leafCount * 2 ^ (depth - 1)`.

## References

* [E. Kushilevitz and Y. Mansour, *Learning decision trees using the Fourier
  spectrum*][KushilevitzMansour1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.DecisionTree

open Finset BitString

variable {ι β : Type*}

variable [Fintype ι] [DecidableEq ι]

/-- The triangle inequality for one coefficient at a node. -/
private theorem abs_add_div_two_le (a b c e : ℝ) :
    |(a + b) / 2 + (c - e) / 2| ≤ (|a| + |b|) / 2 + (|c| + |e|) / 2 := by
  have := le_abs_self a; have := neg_abs_le a
  have := le_abs_self b; have := neg_abs_le b
  have := le_abs_self c; have := neg_abs_le c
  have := le_abs_self e; have := neg_abs_le e
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The spectral norm of a decision tree is at most its number of leaves**: a function of the
output of a decision tree with values in `[-1, 1]` has Fourier coefficients whose absolute values
sum to at most the number of leaves [KushilevitzMansour1993]. -/
theorem sum_abs_fourierCoeff_le_leafCount (g : β → ℝ) (hg : ∀ b, |g b| ≤ 1)
    (t : DecisionTree ι β) : ∑ S, |fourierCoeff (fun x => g (t.eval x)) S| ≤ t.leafCount := by
  induction t with
  | leaf b =>
    simp only [eval_leaf, fourierCoeff_const, apply_ite abs, abs_zero, sum_ite_eq', mem_univ,
      ite_true, leafCount, Nat.cast_one]
    exact hg b
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [fourierCoeff_eval_node, leafCount, Nat.cast_add]
    set c₀ := fourierCoeff (fun x => g (t₀.eval x))
    set c₁ := fourierCoeff (fun x => g (t₁.eval x))
    calc ∑ S, |(c₀ S + c₁ S) / 2 + (c₀ (symmDiff {i} S) - c₁ (symmDiff {i} S)) / 2|
        ≤ ∑ S, ((|c₀ S| + |c₁ S|) / 2 +
            (|c₀ (symmDiff {i} S)| + |c₁ (symmDiff {i} S)|) / 2) :=
          sum_le_sum fun S _ => abs_add_div_two_le _ _ _ _
      _ = (∑ S, |c₀ S| + ∑ S, |c₁ S|) / 2 +
            (∑ S, |c₀ (symmDiff {i} S)| + ∑ S, |c₁ (symmDiff {i} S)|) / 2 := by
          simp only [sum_add_distrib, ← sum_div]
      _ = ∑ S, |c₀ S| + ∑ S, |c₁ S| := by
          rw [Fintype.sum_symmDiff {i} fun S => |c₀ S|, Fintype.sum_symmDiff {i} fun S => |c₁ S|]
          ring
      _ ≤ t₀.leafCount + t₁.leafCount := add_le_add ih₀ ih₁

/-- **The spectral norm of a Boolean decision tree is at most its number of leaves**: a Boolean
function of the output of a decision tree, read as signs, has Fourier coefficients whose absolute
values sum to at most the number of leaves [O'Donnell, Section 3.2][ODonnell2014]. -/
theorem sum_abs_fourierCoeff_signVal_le_leafCount (g : β → Bool) (t : DecisionTree ι β) :
    ∑ S, |fourierCoeff (fun x => signVal (g (t.eval x))) S| ≤ t.leafCount :=
  sum_abs_fourierCoeff_le_leafCount (fun b => signVal (g b)) (fun b => by cases g b <;> simp) t

/-- A Boolean function of the output of a decision tree of depth `d`, read as signs, has spectral
norm at most `2 ^ d`. -/
theorem sum_abs_fourierCoeff_signVal_le_two_pow_depth (g : β → Bool) (t : DecisionTree ι β) :
    ∑ S, |fourierCoeff (fun x => signVal (g (t.eval x))) S| ≤ 2 ^ t.depth :=
  (sum_abs_fourierCoeff_signVal_le_leafCount g t).trans
    (by exact_mod_cast leafCount_le_two_pow_depth t)

/-- **Fourier sparsity of decision trees**: a Boolean function of the output of a decision tree of
depth `d`, read as signs, has at most `leafCount * 2 ^ (d - 1)` nonzero Fourier coefficients, since
each of them has absolute value at least `2 ^ (1 - d)` (at least `1` when `d = 0`)
[O'Donnell, Section 3.2][ODonnell2014]. -/
theorem card_filter_fourierCoeff_signVal_ne_zero_le (g : β → Bool) (t : DecisionTree ι β) :
    #{S | fourierCoeff (fun x => signVal (g (t.eval x))) S ≠ 0} ≤
      t.leafCount * 2 ^ (t.depth - 1) := by
  set c := fourierCoeff (fun x => signVal (g (t.eval x)))
  have hpos : (0 : ℝ) < 2 ^ (t.depth - 1) := by positivity
  have hge (S : Finset ι) (hS : c S ≠ 0) : 1 ≤ 2 ^ (t.depth - 1) * |c S| := by
    obtain ⟨m, hm⟩ : ∃ m : ℤ, c S = m / 2 ^ (t.depth - 1) :=
      exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one g t S
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hS (by rw [hm, Int.cast_zero, zero_div])
    rw [hm, abs_div, abs_of_pos hpos, mul_div_cancel₀ _ hpos.ne']
    exact_mod_cast Int.one_le_abs hm0
  have h : (#{S | c S ≠ 0} : ℝ) ≤ t.leafCount * 2 ^ (t.depth - 1) :=
    calc (#{S | c S ≠ 0} : ℝ) = ∑ S with c S ≠ 0, (1 : ℝ) := by rw [sum_const, nsmul_one]
      _ ≤ ∑ S with c S ≠ 0, 2 ^ (t.depth - 1) * |c S| :=
          sum_le_sum fun S hS => hge S (mem_filter.1 hS).2
      _ ≤ ∑ S, 2 ^ (t.depth - 1) * |c S| :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = 2 ^ (t.depth - 1) * ∑ S, |c S| := (mul_sum _ _ _).symm
      _ ≤ 2 ^ (t.depth - 1) * t.leafCount :=
          mul_le_mul_of_nonneg_left (sum_abs_fourierCoeff_signVal_le_leafCount g t) hpos.le
      _ = t.leafCount * 2 ^ (t.depth - 1) := mul_comm _ _
  exact_mod_cast h

end Cslib.DecisionTree
