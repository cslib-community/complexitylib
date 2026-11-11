/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Fourier
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Granularity of the Fourier coefficients of decision trees

An integer-valued function of the output of a decision tree of depth `d` has Fourier coefficients
that are integer multiples of `2 ^ (-d)`
(`DecisionTree.exists_fourierCoeff_eq_intCast_div_two_pow_depth`): a leaf has integer
coefficients, and each node averages coefficients of its subtrees, halving the denominator. A bit
read as a sign is `signVal b = 1 - 2 [b]`, one minus twice an integer, so a Boolean function
computed by a decision tree of depth `d ≥ 1`, read as signs, has coefficients in `2 ^ (1 - d) ℤ`,
and one computed by a tree of depth `0` has integer coefficients
(`DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one`)
[O'Donnell, Section 3.2][ODonnell2014]. The depth is structural, so unreachable paths only weaken
the bound.

## Main results

* `Cslib.DecisionTree.exists_fourierCoeff_eq_intCast_div_two_pow_depth`: granularity for
  integer-valued functions of decision trees.
* `Cslib.DecisionTree.exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one`:
  granularity for Boolean functions of decision trees.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- A real number in `2 ^ (-a) ℤ` is in `2 ^ (-D) ℤ` for `a ≤ D`. -/
private theorem exists_eq_intCast_div_two_pow_of_le {c : ℝ} {a D : ℕ}
    (h : ∃ m : ℤ, c = m / 2 ^ a) (haD : a ≤ D) : ∃ m : ℤ, c = m / 2 ^ D := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le haD
  refine ⟨m * 2 ^ k, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

/-- **Granularity of decision trees**: the Fourier coefficients of an integer-valued function of
the output of a decision tree of depth `d` are integer multiples of `2 ^ (-d)`. -/
theorem exists_fourierCoeff_eq_intCast_div_two_pow_depth (g : β → ℤ) (t : DecisionTree ι β)
    (S : Finset ι) : ∃ m : ℤ, fourierCoeff (fun x => (g (t.eval x) : ℝ)) S = m / 2 ^ t.depth := by
  induction t generalizing S with
  | leaf b =>
    refine ⟨if S = ∅ then g b else 0, ?_⟩
    simp only [eval_leaf, fourierCoeff_const, depth_leaf, pow_zero, div_one]
    split_ifs <;> simp
  | node i t₀ t₁ ih₀ ih₁ =>
    rw [fourierCoeff_eval_node (fun b => (g b : ℝ))]
    obtain ⟨a, ha⟩ := exists_eq_intCast_div_two_pow_of_le (ih₀ S) (le_max_left t₀.depth t₁.depth)
    obtain ⟨b, hb⟩ := exists_eq_intCast_div_two_pow_of_le (ih₁ S) (le_max_right t₀.depth t₁.depth)
    obtain ⟨c, hc⟩ := exists_eq_intCast_div_two_pow_of_le (ih₀ (symmDiff {i} S))
      (le_max_left t₀.depth t₁.depth)
    obtain ⟨e, he⟩ := exists_eq_intCast_div_two_pow_of_le (ih₁ (symmDiff {i} S))
      (le_max_right t₀.depth t₁.depth)
    refine ⟨a + b + c - e, ?_⟩
    rw [ha, hb, hc, he, depth_node, pow_succ]
    push_cast
    field_simp
    ring

/-- **Granularity of decision trees** for Boolean functions: a Boolean function of the output of
a decision tree of depth `d`, read as signs, has Fourier coefficients in `2 ^ (1 - d) ℤ` when
`d ≥ 1`, and integer coefficients when `d = 0` [O'Donnell, Section 3.2][ODonnell2014]. -/
theorem exists_fourierCoeff_signVal_eq_intCast_div_two_pow_depth_sub_one (g : β → Bool)
    (t : DecisionTree ι β) (S : Finset ι) :
    ∃ m : ℤ, fourierCoeff (fun x => signVal (g (t.eval x))) S = m / 2 ^ (t.depth - 1) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, fourierCoeff (fun x => ((if g (t.eval x) then 1 else 0 : ℤ) : ℝ)) S =
      m / 2 ^ (t.depth - 1 + 1) :=
    exists_eq_intCast_div_two_pow_of_le
      (exists_fourierCoeff_eq_intCast_div_two_pow_depth (fun b => if g b then 1 else 0) t S)
      (by omega)
  have h : (fun x => signVal (g (t.eval x))) =
      fun x => 1 - 2 * ((if g (t.eval x) then 1 else 0 : ℤ) : ℝ) := by
    funext x
    cases g (t.eval x) <;> norm_num
  refine ⟨(if S = ∅ then 2 ^ (t.depth - 1) else 0) - m, ?_⟩
  rw [h, fourierCoeff_sub, fourierCoeff_const, fourierCoeff_const_mul, hm, pow_succ]
  split_ifs
  · push_cast
    field_simp
  · push_cast
    ring

end Cslib.DecisionTree
