/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.LocalTest.DecisionTree
public import Complexity.Computability.PropertyTesting.Monotonicity.Basic
import Complexity.Foundations.Analysis.BernoulliInequality
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# The edge tester for monotone Boolean functions

The **edge tester** of [Goldreich, Goldwasser, Lehman, Ron and
Samorodnitsky][GoldreichGoldwasserLehmanRonSamorodnitsky2000] picks a uniformly random edge of the
cube, reads `f` at both endpoints, and rejects when `f` decreases along the edge. Here it is the
two-query local test `BitString.edgeTest ι`, in the format of `PCP.LocalTest` used for the BLR
test in `Complexity.Computability.PropertyTesting.Linearity`: on the random string `(i, x)` it reads
`f` at `update x i false` and at `update x i true` and accepts when the first value is at most the
second. The bit `x i` is ignored, so a uniform random string selects a uniform direction and a
uniform edge in it, as in the source's choice of `i` and `x_{-i}`
[Roughgarden, §8.3.1][Roughgarden2015CC].

One trial rejects with probability exactly the fraction of violated edges
(`BitString.one_sub_acceptProb_edgeTest`). So it accepts monotone functions with probability one
(`BitString.acceptProb_edgeTest_of_monotone`), and by the analysis in
`Complexity.Computability.PropertyTesting.Monotonicity.Basic` it rejects every function `ε`-far
from monotone with probability at least `ε / n` (`BitString.acceptProb_edgeTest_le`), where `n` is
the number of coordinates. `k` independent trials (`LocalTest.repeatAll`) run as a decision tree
make at most `2 k` queries (`BitString.depth_decisionTree_repeatAll_edgeTest_le`), non-adaptively.
They accept monotone functions with probability one and functions `ε`-far from monotone with
probability at most `(1 - ε / n) ^ k` (`BitString.acceptProb_repeatAll_edgeTest_le`), hence at most
`1 / 3` as soon as `2 n ≤ ε k` (`BitString.acceptProb_repeatAll_edgeTest_le_one_third`). With
`k = ⌈2 n / ε⌉` this is a one-sided tester making `2 ⌈2 n / ε⌉ = O(n / ε)` queries
(`BitString.acceptProb_repeatAll_edgeTest_ceil_le_one_third`), which is
[Roughgarden, Theorem 8.2][Roughgarden2015CC] with explicit constants.

`ε`-far means `ε ≤ relDistMonotone f`: every monotone function differs from `f` on at least
`ε 2 ^ n` points. Completeness needs `ι` nonempty: the cube of dimension `0` has no edges, and the
acceptance probability over an empty set of random strings is `0` by convention. These are query
bounds in the decision-tree model; no running time is claimed.

## Main definitions

* `Cslib.BitString.edgeTest`: one trial of the edge tester, as a two-query local test.

## Main results

* `Cslib.BitString.one_sub_acceptProb_edgeTest`: the rejection probability of one trial is the
  fraction of violated edges.
* `Cslib.BitString.acceptProb_edgeTest_of_monotone`,
  `Cslib.BitString.acceptProb_repeatAll_edgeTest_of_monotone`: one-sided completeness.
* `Cslib.BitString.acceptProb_edgeTest_le`, `Cslib.BitString.acceptProb_repeatAll_edgeTest_le`:
  soundness for `ε`-far functions.
* `Cslib.BitString.depth_decisionTree_repeatAll_edgeTest_le`: `k` trials make at most `2 k`
  queries.
* `Cslib.BitString.acceptProb_repeatAll_edgeTest_le_one_third`,
  `Cslib.BitString.acceptProb_repeatAll_edgeTest_ceil_le_one_third`: acceptance probability at most
  `1 / 3` with `O(n / ε)` queries.

## References

* [O. Goldreich, S. Goldwasser, E. Lehman, D. Ron, A. Samorodnitsky, *Testing
  monotonicity*][GoldreichGoldwasserLehmanRonSamorodnitsky2000]
* [T. Roughgarden, *Communication Complexity (for Algorithm Designers)*][Roughgarden2015CC]
-/

public section

namespace Cslib.BitString

open Finset Function PCP

variable {ι : Type*} [DecidableEq ι]

variable (ι) in
/-- One trial of the **edge tester**: on the random string `(i, x)`, read `f` at the endpoints
`update x i false` and `update x i true` of the edge in direction `i` through `x`, and accept when
`f` does not decrease along it. -/
def edgeTest : LocalTest (ι → Bool) (ι × (ι → Bool)) (Fin 2) Bool where
  query := fun (i, x) => ![update x i false, update x i true]
  Accepts _ a := a 0 ≤ a 1

instance (r : ι × (ι → Bool)) (a : Fin 2 → Bool) : Decidable ((edgeTest ι).Accepts r a) :=
  inferInstanceAs (Decidable (a 0 ≤ a 1))

/-- The edge test passes on `(i, x)` when `f` does not decrease along the edge in direction `i`
through `x`. -/
@[simp]
theorem passes_edgeTest {f : (ι → Bool) → Bool} {i : ι} {x : ι → Bool} :
    (edgeTest ι).Passes f (i, x) ↔ f (update x i false) ≤ f (update x i true) :=
  Iff.rfl

variable [Fintype ι]

/-- **One trial of the edge tester rejects with probability exactly the fraction of violated
edges.** -/
theorem one_sub_acceptProb_edgeTest [Nonempty ι] (f : (ι → Bool) → Bool) :
    1 - (edgeTest ι).acceptProb f = violatedEdgeFraction f := by
  classical
  have hcard : #{r : ι × (ι → Bool) | ¬ (edgeTest ι).Passes f r} =
      2 * ∑ i, #(violatedEdges f i) := by
    rw [card_filter, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← card_endpoints_violatedEdges, card_filter]
    refine sum_congr rfl fun x _ => ?_
    simp only [passes_edgeTest]
    cases f (update x i false) <;> cases f (update x i true) <;> simp
  have hc := congrArg (Nat.cast : ℕ → ℝ) hcard
  push_cast at hc
  rw [LocalTest.one_sub_acceptProb, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    violatedEdgeFraction_eq, ← hc]
  push_cast
  congr!

/-- **Completeness**: one trial accepts a monotone function with probability one. -/
theorem acceptProb_edgeTest_of_monotone [Nonempty ι] {f : (ι → Bool) → Bool}
    (hf : Monotone f) : (edgeTest ι).acceptProb f = 1 :=
  (LocalTest.acceptProb_eq_one_iff _).2 fun _ =>
    hf (update_le_update_iff'.2 (Bool.false_le true))

/-- **Soundness of one trial**: a function `ε`-far from monotone is rejected with probability at
least `ε / n`. -/
theorem acceptProb_edgeTest_le {f : (ι → Bool) → Bool} {ε : ℝ}
    (hε : ε ≤ relDistMonotone f) :
    (edgeTest ι).acceptProb f ≤ 1 - ε / Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Fintype.card_eq_zero, Nat.cast_zero, div_zero, sub_zero]
    exact LocalTest.acceptProb_le_one _ _
  · have h := one_sub_acceptProb_edgeTest f
    linarith [div_card_le_violatedEdgeFraction hε]

/-- `k` trials of the edge tester, run as a decision tree, make at most `2 k` queries on every
random string; the queries are fixed by the random string, so the tester is non-adaptive. -/
theorem depth_decisionTree_repeatAll_edgeTest_le (k : ℕ) (r : Fin k → ι × (ι → Bool)) :
    (((edgeTest ι).repeatAll k).decisionTree r).depth ≤ 2 * k := by
  simpa only [FinEnum.card_fin, Nat.mul_comm] using
    (edgeTest ι).depth_decisionTree_repeatAll_le k r

/-- **One-sided completeness** of `k` trials: monotone functions are always accepted. -/
theorem acceptProb_repeatAll_edgeTest_of_monotone [Nonempty ι] (k : ℕ)
    {f : (ι → Bool) → Bool} (hf : Monotone f) :
    ((edgeTest ι).repeatAll k).acceptProb f = 1 := by
  rw [LocalTest.acceptProb_repeatAll, acceptProb_edgeTest_of_monotone hf, one_pow]

/-- **Soundness** of `k` trials: a function `ε`-far from monotone is accepted with probability at
most `(1 - ε / n) ^ k`. -/
theorem acceptProb_repeatAll_edgeTest_le {f : (ι → Bool) → Bool} {ε : ℝ}
    (hε : ε ≤ relDistMonotone f) (k : ℕ) :
    ((edgeTest ι).repeatAll k).acceptProb f ≤ (1 - ε / Fintype.card ι) ^ k := by
  rw [LocalTest.acceptProb_repeatAll]
  exact pow_le_pow_left₀ ((edgeTest ι).acceptProb_nonneg f) (acceptProb_edgeTest_le hε) k

/-- **The edge tester** [Roughgarden, Theorem 8.2][Roughgarden2015CC]: once `2 n ≤ ε k`, `k` trials
accept a function `ε`-far from monotone with probability at most `1 / 3`. -/
theorem acceptProb_repeatAll_edgeTest_le_one_third {f : (ι → Bool) → Bool} {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ relDistMonotone f) {k : ℕ}
    (hk : 2 * Fintype.card ι ≤ ε * k) :
    ((edgeTest ι).repeatAll k).acceptProb f ≤ 1 / 3 := by
  have hι : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    linarith [relDistMonotone_of_monotone (Subsingleton.monotone f)]
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set p := 1 - (edgeTest ι).acceptProb f with hp
  have hp0 : 0 ≤ p := by linarith [(edgeTest ι).acceptProb_le_one f]
  have hp1 : p ≤ 1 := by linarith [(edgeTest ι).acceptProb_nonneg f]
  have hpε : ε / Fintype.card ι ≤ p := by linarith [acceptProb_edgeTest_le hε]
  rw [LocalTest.acceptProb_repeatAll, show (edgeTest ι).acceptProb f = 1 - p by rw [hp]; ring]
  refine (Real.one_sub_pow_le_one_div_one_add_mul hp0 hp1 k).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : 2 ≤ (k : ℝ) * p := by
    calc (2 : ℝ) ≤ ε * k / Fintype.card ι := by rw [le_div_iff₀ hn]; linarith
      _ = k * (ε / Fintype.card ι) := by ring
      _ ≤ k * p := by gcongr
  linarith

/-- **The edge tester with `O(n / ε)` queries**: `⌈2 n / ε⌉` trials, making at most
`2 ⌈2 n / ε⌉` queries (`depth_decisionTree_repeatAll_edgeTest_le`), accept a function `ε`-far
from monotone with probability at most `1 / 3`. -/
theorem acceptProb_repeatAll_edgeTest_ceil_le_one_third {f : (ι → Bool) → Bool} {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ relDistMonotone f) :
    ((edgeTest ι).repeatAll ⌈2 * Fintype.card ι / ε⌉₊).acceptProb f ≤ 1 / 3 := by
  refine acceptProb_repeatAll_edgeTest_le_one_third hε0 hε ?_
  have h := Nat.le_ceil (2 * Fintype.card ι / ε)
  rw [div_le_iff₀ hε0] at h
  linarith

end Cslib.BitString
