/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Cslib.Computability.QueryComplexity.Measures
import CslibFrontier.Foundations.BooleanAnalysis.FourierDegree
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Influence and sensitivity

The total influence of a Boolean function, read as signs, is its *average sensitivity*, the
expected value of `sensitivityAt f x` (`BitString.totalInfluence_eq_expect_sensitivityAt`)
[O'Donnell, Section 2.3][ODonnell2014], so it is at most the sensitivity
(`BitString.totalInfluence_le_sensitivity`). A function computed by a decision tree of depth
`d` has Fourier degree at most `d`, so its total influence is at most `d`
(`DecisionTree.totalInfluence_le_depth`, a case of `BitString.totalInfluence_signVal_le_of_degree`).

## Main results

* `Cslib.BitString.totalInfluence_eq_expect_sensitivityAt`: total influence is average sensitivity.
* `Cslib.BitString.totalInfluence_le_sensitivity`: total influence is at most sensitivity.
* `Cslib.DecisionTree.totalInfluence_le_depth`: functions of decision trees of depth `d` have
  total influence at most `d`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-- The expected sensitivity at a uniformly sampled input is the total influence. -/
theorem totalInfluence_eq_expect_sensitivityAt {n : ℕ} (f : BooleanFunction n) :
    totalInfluence (fun x => signVal (f x)) = 𝔼 x, (sensitivityAt f x : ℝ) :=
  totalInfluence_signVal f

/-- The total influence of a Boolean function, read as signs, is at most its sensitivity. -/
theorem totalInfluence_le_sensitivity {n : ℕ} (f : BooleanFunction n) :
    totalInfluence (fun x => signVal (f x)) ≤ sensitivity f := by
  rw [totalInfluence_eq_expect_sensitivityAt]
  exact expect_le univ_nonempty fun x _ => by exact_mod_cast sensitivityAt_le_sensitivity f x

end Cslib.BitString

namespace Cslib.DecisionTree

open Finset BitString
open scoped BigOperators

variable {ι β : Type*} [Fintype ι] [DecidableEq ι]

/-- **Decision trees of depth `d` have total influence at most `d`**: a Boolean function of the
output of a decision tree of depth `d`, read as signs, has Fourier weight only on sets of at most
`d` coordinates, and its squared coefficients sum to one. -/
theorem totalInfluence_le_depth (g : β → Bool) (t : DecisionTree ι β) :
    totalInfluence (fun x => signVal (g (t.eval x))) ≤ t.depth :=
  totalInfluence_signVal_le_of_fourierCoeff_eq_zero (fun x => g (t.eval x)) fun _ =>
    fourierCoeff_eq_zero_of_depth_lt (fun b => signVal (g b)) t

end Cslib.DecisionTree
