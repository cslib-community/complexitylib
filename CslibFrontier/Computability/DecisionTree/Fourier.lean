/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Computability.QueryComplexity.Degree
import CslibFrontier.Foundations.BooleanAnalysis.Decomposition

/-!
# Decision trees have low Fourier degree

A function computed by a decision tree of depth `d` has no Fourier weight above degree `d`
(`DecisionTree.fourierCoeff_eq_zero_of_depth_lt`) [O'Donnell, Chapter 3][ODonnell2014]. This
follows from `DecisionTree.comp_eval_mem_lowDegree` and
`BitString.fourierCoeff_eq_zero_of_mem_lowDegree`. At each node querying `i`, the computed function
is `(f₀ + f₁) / 2 + χ_{i} (f₀ - f₁) / 2` in terms of the functions `f₀` and `f₁` of its subtrees,
so its coefficient on `S` is given by the coefficients of `f₀` and `f₁` on `S` and on `{i} ∆ S`
(`DecisionTree.fourierCoeff_eval_node`).

## Main results

* `Cslib.DecisionTree.fourierCoeff_eval_node`: the Fourier coefficients at a node in terms of those
  of the subtrees.
* `Cslib.DecisionTree.fourierCoeff_eq_zero_of_depth_lt`: decision trees of depth `d` have Fourier
  degree at most `d`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.DecisionTree

open Finset BitString

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Fourier coefficients at a node**: the coefficient on `S` of a function of the output
of a node querying `i` is the average of the coefficients of the functions of its subtrees on `S`,
plus half the difference of their coefficients on `{i} ∆ S`. -/
theorem fourierCoeff_eval_node (g : β → ℝ) (i : ι) (t₀ t₁ : DecisionTree ι β) (S : Finset ι) :
    fourierCoeff (fun x => g ((node i t₀ t₁).eval x)) S =
      (fourierCoeff (fun x => g (t₀.eval x)) S + fourierCoeff (fun x => g (t₁.eval x)) S) / 2 +
        (fourierCoeff (fun x => g (t₀.eval x)) (symmDiff {i} S) -
          fourierCoeff (fun x => g (t₁.eval x)) (symmDiff {i} S)) / 2 := by
  have h : (fun x => g ((node i t₀ t₁).eval x)) =
      fun x => cond (x i) (g (t₁.eval x)) (g (t₀.eval x)) := by
    funext x
    cases hx : x i <;> simp only [eval_node, hx, Bool.cond_false, Bool.cond_true]
  rw [h]
  exact fourierCoeff_cond i _ _ S

/-- **Decision trees have low Fourier degree**: a function of the output of a decision tree of
depth `d` has no Fourier weight on sets of more than `d` coordinates. -/
theorem fourierCoeff_eq_zero_of_depth_lt (g : β → ℝ) (t : DecisionTree ι β)
    {S : Finset ι} (hS : t.depth < #S) : fourierCoeff (fun x => g (t.eval x)) S = 0 :=
  fourierCoeff_eq_zero_of_mem_lowDegree (comp_eval_mem_lowDegree g t) hS

end Cslib.DecisionTree
