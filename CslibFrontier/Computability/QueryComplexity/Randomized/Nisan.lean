/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.ApproximateDegree
public import CslibFrontier.Computability.QueryComplexity.Randomized
public import Cslib.Computability.QueryComplexity.Measures
import CslibFrontier.Computability.QueryComplexity.Relations
import Mathlib.Tactic.Linarith

/-!
# Lower bounds on randomized decision tree complexity

Block sensitivity and approximate degree bound randomized decision tree complexity below, so
deterministic and bounded-error randomized decision tree complexity are polynomially related
[Nisan1991].

**Block sensitivity**
(`QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_randomizedComplexity`). Let `μ` compute
`f` with error `ε`, and let `x` have `b = bs(f)` pairwise disjoint sensitive blocks `B₁, …, B_b`.
A tree `t` that queries no variable of `Bⱼ` on input `x` reaches the same leaf on `x` and on `x`
with `Bⱼ` flipped, while `f` differs there, so `t` errs on one of the two inputs. The blocks are
disjoint, so `t` queries variables of at most `depth t` of them, and errs on `x` or on `x` with
`Bⱼ` flipped for every other block. Averaging over `t` drawn from `μ`,
`b ≤ depth μ + ∑ⱼ (ε + ε)`, that is `(1 - 2ε) bs(f) ≤ R_ε(f)`; for `ε = 1/3`, `bs(f) ≤ 3 R(f)`.
With `D(f) ≤ bs(f)³` [BealsBuhrmanCleveMoscaDeWolf2001] this gives `D(f) ≤ 27 R(f)³`.

**Approximate degree** (`QueryComplexity.approxDegree_le_randomizedComplexity`). The probability
that a tree drawn from `μ` outputs `1` on `x` is an average of functions of degree at most the
depth of `μ` (`DecisionTree.comp_eval_mem_lowDegree`), so has degree at most `depth μ`, and it is
within `ε` of `f` when `μ` computes `f` with error `ε`. So `adeg_ε(f) ≤ R_ε(f)`
[BuhrmanDeWolf2002].

## Main results

* `Cslib.QueryComplexity.one_sub_two_mul_mul_blockSensitivity_le_randomizedComplexity`:
  `(1 - 2ε) bs(f) ≤ R_ε(f)` for `ε ≥ 0`.
* `Cslib.QueryComplexity.blockSensitivity_le_three_mul_randomizedComplexity`: `bs(f) ≤ 3 R(f)`.
* `Cslib.QueryComplexity.approxDegree_le_randomizedComplexity`: `adeg_ε(f) ≤ R_ε(f)`.
* `Cslib.RandomizedDecisionTree.Computes.one_sub_two_mul_mul_blockSensitivity_le_depth`,
  `Cslib.RandomizedDecisionTree.Computes.approxDegree_le_depth`: the same bounds for the depth of
  one randomized decision tree computing `f` with error `ε`.
* `Cslib.DecisionTree.one_sub_two_mul_pow_three_mul_complexity_le`: `(1 - 2ε)³ D(f) ≤ R_ε(f)³`
  for `ε ≥ 0`.
* `Cslib.DecisionTree.complexity_le_mul_randomizedComplexity_pow_three`: `D(f) ≤ 27 R(f)³`.

## References

* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf, *Quantum lower bounds by
  polynomials*][BealsBuhrmanCleveMoscaDeWolf2001]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

public section

open scoped NNReal

namespace Cslib

open Convexity Finset BitString RandomizedDecisionTree

namespace QueryComplexity

variable {n : ℕ} {f : BooleanFunction n}

/-- A tree that misses a sensitive block on `x` errs on `x` or on `x` with the block flipped. -/
private theorem one_le_err_add_err {t : DecisionTree (Fin n) Bool} {x : BitString n} {B : Block n}
    (hB : IsSensitiveBlock f x B) (hBt : Disjoint B (t.queries x)) :
    (1 : ℝ) ≤ (if t.eval x = f x then 0 else 1) +
      if t.eval (flipBlock B x) = f (flipBlock B x) then 0 else 1 := by
  have heval : t.eval (flipBlock B x) = t.eval x :=
    t.eval_eq_of_forall_mem_queries fun i hi =>
      flipBlock_apply_of_notMem (Finset.disjoint_right.mp hBt hi)
  rw [heval]
  by_cases h : t.eval x = f x
  · simp [h, Ne.symm hB]
  · simp only [h, ↓reduceIte]
    split_ifs <;> norm_num

end QueryComplexity

namespace RandomizedDecisionTree

open QueryComplexity

variable {n : ℕ} {f : BooleanFunction n} {μ : RandomizedDecisionTree (Fin n) Bool} {ε : ℝ}

/-- **Nisan's bound for one randomized decision tree**: if `μ` computes `f` with error `ε`, then
`(1 - 2ε) bs(f) ≤ depth μ`. -/
theorem Computes.one_sub_two_mul_mul_blockSensitivity_le_depth (h : μ.Computes ε f) :
    (1 - 2 * ε) * blockSensitivity f ≤ μ.depth := by
  classical
  -- an input and a family of pairwise disjoint sensitive blocks attaining `bs(f)`
  obtain ⟨x, -, hx⟩ := exists_mem_eq_sup univ univ_nonempty (blockSensitivityAt f)
  obtain ⟨F, hF, hFcard⟩ := exists_mem_eq_sup (sensitiveFamilies f x)
    ⟨∅, mem_sensitiveFamilies.2 ⟨by simp, by simp⟩⟩ card
  rw [mem_sensitiveFamilies] at hF
  rw [blockSensitivity, hx, blockSensitivityAt, hFcard]
  set e : DecisionTree (Fin n) Bool → BitString n → ℝ := fun t y =>
    if t.eval y = f y then 0 else 1
  have he (t : DecisionTree (Fin n) Bool) (y : BitString n) : 0 ≤ e t y := by
    simp only [e]
    split_ifs <;> norm_num
  -- every tree that `μ` can draw meets at most `depth μ` blocks and errs for every other block
  have key (t : DecisionTree (Fin n) Bool) (ht : t ∈ μ.weights.support) :
      (#F : ℝ) ≤ μ.depth + ∑ B ∈ F, (e t x + e t (flipBlock B x)) := by
    set Q := t.queries x
    have hhit : #(F.filter fun B => ¬Disjoint B Q) ≤ μ.depth := by
      refine (card_le_card_biUnion (f := fun B => B ∩ Q) (fun B hB B' hB' hne =>
        Disjoint.mono inter_subset_left inter_subset_left
          (hF.2 (mem_filter.1 hB).1 (mem_filter.1 hB').1 hne))
        fun B hB => not_disjoint_iff_nonempty_inter.1 (mem_filter.1 hB).2).trans ?_
      exact ((card_le_card (biUnion_subset.2 fun _ _ => inter_subset_right)).trans
        (t.card_queries_le_depth x)).trans (depth_le_depth ht)
    have hmiss : (#(F.filter fun B => Disjoint B Q) : ℝ) ≤
        ∑ B ∈ F, (e t x + e t (flipBlock B x)) := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine (sum_le_sum fun B hB => one_le_err_add_err (hF.1 B (mem_filter.1 hB).1)
        (mem_filter.1 hB).2).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun B _ _ =>
        add_nonneg (he t x) (he t _)
    have hsplit := card_filter_add_card_filter_not (s := F) fun B => Disjoint B Q
    have : (#F : ℝ) = #(F.filter fun B => Disjoint B Q) + #(F.filter fun B => ¬Disjoint B Q) := by
      rw [← Nat.cast_add, hsplit]
    rw [this]
    have hhit' : (#(F.filter fun B => ¬Disjoint B Q) : ℝ) ≤ μ.depth := by exact_mod_cast hhit
    linarith
  -- average over the tree drawn from `μ`
  have htot : ∑ t ∈ μ.weights.support, μ.weights t = 1 := by simpa [Finsupp.sum] using μ.total
  have havg := Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (key t ht) (μ.weights_nonneg t)
  rw [← Finset.sum_mul, htot, one_mul] at havg
  have hrhs : ∑ t ∈ μ.weights.support,
      μ.weights t * (μ.depth + ∑ B ∈ F, (e t x + e t (flipBlock B x))) =
      μ.depth + ∑ B ∈ F, (μ.errorProb f x + μ.errorProb f (flipBlock B x)) := by
    rw [Finset.sum_congr rfl fun t _ => mul_add _ _ _, Finset.sum_add_distrib, ← Finset.sum_mul,
      htot, one_mul]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [mul_add, Finset.sum_add_distrib, errorProb_eq_sum, Finsupp.sum, e]
  have herr : ∑ B ∈ F, (μ.errorProb f x + μ.errorProb f (flipBlock B x)) ≤ 2 * ε * #F := by
    refine (sum_le_sum fun B _ => add_le_add (h x) (h (flipBlock B x))).trans_eq ?_
    rw [sum_const, nsmul_eq_mul]
    ring
  linarith

/-- A randomized decision tree computing `f` with error `ε` gives a real function of degree at most
its depth within `ε` of `f`: the probability that the tree drawn outputs `1`. -/
theorem Computes.approxDegree_le_depth {ε : ℝ≥0} (h : μ.Computes ε f) :
    approxDegree ε f ≤ μ.depth := by
  classical
  set p : BitString n → ℝ := ∑ t ∈ μ.weights.support, μ.weights t • fun y => bitVal ℝ (t.eval y)
  have hp (y : BitString n) : p y = μ.weights.sum fun t w => w * bitVal ℝ (t.eval y) := by
    simp [p, Finsupp.sum]
  refine approxDegree_le_of_mem_lowDegree (p := p) (Submodule.sum_mem _ fun t ht =>
    Submodule.smul_mem _ _ (lowDegree_mono (depth_le_depth ht)
      (DecisionTree.comp_eval_mem_lowDegree _ t))) fun y => ?_
  have htot : ∑ t ∈ μ.weights.support, μ.weights t = 1 := by simpa [Finsupp.sum] using μ.total
  calc |p y - bitVal ℝ (f y)|
      = |∑ t ∈ μ.weights.support, μ.weights t * (bitVal ℝ (t.eval y) - bitVal ℝ (f y))| := by
        congr 1
        rw [hp, Finsupp.sum]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, htot, one_mul]
    _ ≤ ∑ t ∈ μ.weights.support, |μ.weights t * (bitVal ℝ (t.eval y) - bitVal ℝ (f y))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = μ.errorProb f y := by
        simp only [errorProb, Finsupp.sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [abs_mul, abs_of_nonneg (μ.weights_nonneg t)]
        congr 1
        cases t.eval y <;> cases f y <;> simp
    _ ≤ ε := h y

end RandomizedDecisionTree

namespace QueryComplexity

variable {n : ℕ} {ε : ℝ≥0}

/-- **Nisan's bound**: `(1 - 2ε) bs(f) ≤ R_ε(f)` for `ε ≥ 0`. -/
theorem one_sub_two_mul_mul_blockSensitivity_le_randomizedComplexity
    (f : BooleanFunction n) :
    (1 - 2 * (ε : ℝ)) * blockSensitivity f ≤ randomizedComplexity ε f := by
  obtain ⟨μ, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity (ε := ε) f
  exact hd ▸ hμ.one_sub_two_mul_mul_blockSensitivity_le_depth

/-- **Nisan's bound** for bounded error: `bs(f) ≤ 3 R(f)`, for `R = R_{1/3}`. -/
theorem blockSensitivity_le_three_mul_randomizedComplexity (f : BooleanFunction n) :
    blockSensitivity f ≤ 3 * randomizedComplexity (1 / 3) f := by
  have := one_sub_two_mul_mul_blockSensitivity_le_randomizedComplexity
    (ε := 1 / 3) f
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at this
  have h : (blockSensitivity f : ℝ) ≤ 3 * randomizedComplexity (1 / 3) f := by linarith
  exact_mod_cast h

/-- **Approximate degree is at most randomized complexity**: `adeg_ε(f) ≤ R_ε(f)`. -/
theorem approxDegree_le_randomizedComplexity (ε : ℝ≥0) (f : BooleanFunction n) :
    approxDegree ε f ≤ randomizedComplexity ε f := by
  obtain ⟨μ, hμ, hd⟩ := exists_computes_depth_eq_randomizedComplexity (ε := ε) f
  exact hd ▸ hμ.approxDegree_le_depth

end QueryComplexity

namespace DecisionTree

open QueryComplexity

variable {n : ℕ} {ε : ℝ≥0}

/-- `(1 - 2ε)³ D(f) ≤ R_ε(f)³` for `ε ≥ 0`, from `D(f) ≤ bs(f)³` and Nisan's bound. -/
theorem one_sub_two_mul_pow_three_mul_complexity_le (f : BooleanFunction n) :
    (1 - 2 * (ε : ℝ)) ^ 3 * complexity f ≤ (randomizedComplexity ε f : ℝ) ^ 3 := by
  rcases le_or_gt (1 - 2 * (ε : ℝ)) 0 with h | h
  · exact (mul_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos (by decide) h)
      (Nat.cast_nonneg _)).trans (by positivity)
  have hD : (complexity f : ℝ) ≤ (blockSensitivity f : ℝ) ^ 3 := by
    exact_mod_cast complexity_le_blockSensitivity_pow_three f
  calc
    (1 - 2 * (ε : ℝ)) ^ 3 * complexity f ≤
        (1 - 2 * (ε : ℝ)) ^ 3 * (blockSensitivity f : ℝ) ^ 3 := by gcongr
    _ = ((1 - 2 * (ε : ℝ)) * blockSensitivity f) ^ 3 := by ring
    _ ≤ (randomizedComplexity ε f : ℝ) ^ 3 :=
        pow_le_pow_left₀ (by positivity)
          (one_sub_two_mul_mul_blockSensitivity_le_randomizedComplexity f) 3

/-- **Deterministic and randomized decision tree complexity are polynomially related**
[Nisan1991]: `D(f) ≤ 27 R(f)³` for the bounded-error randomized complexity `R = R_{1/3}`, from
`bs(f) ≤ 3 R(f)` and `D(f) ≤ bs(f)³`. -/
theorem complexity_le_mul_randomizedComplexity_pow_three (f : BooleanFunction n) :
    complexity f ≤ 27 * randomizedComplexity (1 / 3) f ^ 3 := by
  have := one_sub_two_mul_pow_three_mul_complexity_le (ε := 1 / 3) f
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at this
  have h : (complexity f : ℝ) ≤ 27 * (randomizedComplexity (1 / 3) f : ℝ) ^ 3 := by linarith
  exact_mod_cast h

end DecisionTree

end Cslib
