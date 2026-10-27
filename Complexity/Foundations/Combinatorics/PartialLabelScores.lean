/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.UniformSchedules
public import Mathlib.Data.List.MinMax
import Mathlib.Tactic.NormNum

/-!
# Computable collision scores for partial label schedules

In the conditional-expectation construction in the proof of Lemma 4.5, printed p. 31 of
[OpenAI2026ETH], one whole variable or factor label is fixed at a time. A partial assignment
stores a whole label or `none` at each choice index. Unassigned choices are completed by one
uniformly enumerated function: repeated reads of one index never resample its value.

The closed-form score below is equal to the actual finite completion average and its average
is preserved when an unassigned choice is fixed. These are finite rational identities; no
polynomial bit-cost or machine certificate is asserted.
-/

public section

namespace Cslib.BalancedSchedules

open Finset
open scoped BigOperators

variable {I L : Type*} [DecidableEq I] [Fintype L] [DecidableEq L]

/-- Complete a partial assignment, using the same filler value on every read of an index. -/
@[expose] def completeLabels (assigned : I → Option L) (filler : I → L) (i : I) : L :=
  (assigned i).getD (filler i)

/-- Exact collision score for two choice indices under a partial assignment. A repeated index
scores one, not the reciprocal label count. -/
@[expose] def partialCollision (assigned : I → Option L) (i j : I) : ℚ :=
  if i = j then 1 else
    match assigned i, assigned j with
    | some x, some y => if x = y then 1 else 0
    | _, _ => 1 / (Fintype.card L : ℚ)

/-- The computable pair score is the true finite average over completions. -/
theorem partialCollision_eq_expect [Fintype I] [Nonempty L]
    (assigned : I → Option L) (i j : I) :
    partialCollision assigned i j =
      𝔼 filler : I → L,
        if completeLabels assigned filler i = completeLabels assigned filler j then (1 : ℚ) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [partialCollision, ↓reduceIte, Fintype.expect_const]
  · cases hi : assigned i with
    | none =>
      cases hj : assigned j with
      | none =>
        simpa only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_none] using (expect_schedule_collision (L := L) i j).symm
      | some y =>
        simp only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_none, Option.getD_some]
        rw [expect_schedule_apply i (fun x : L => if x = y then (1 : ℚ) else 0)]
        simp [NNRat.smul_def]
    | some x =>
      cases hj : assigned j with
      | none =>
        simp only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_none, Option.getD_some]
        rw [expect_schedule_apply j (fun y : L => if x = y then (1 : ℚ) else 0)]
        simp [NNRat.smul_def]
      | some y =>
        simp only [partialCollision, hij, ↓reduceIte, hi, hj, completeLabels,
          Option.getD_some, Fintype.expect_const]

/-- Averaging the candidate values of one unassigned whole label preserves the pair score. -/
theorem expect_partialCollision_update [Nonempty L] (assigned : I → Option L)
    (k i j : I) (hk : assigned k = none) :
    (𝔼 x : L, partialCollision (Function.update assigned k (some x)) i j) =
      partialCollision assigned i j := by
  by_cases hij : i = j
  · subst j
    simp only [partialCollision, ↓reduceIte, Fintype.expect_const]
  by_cases hki : k = i
  · subst k
    cases hj : assigned j with
    | none => simp [partialCollision, hij, hk, hj, Function.update, Ne.symm hij]
    | some y => simp [partialCollision, hij, hk, hj, Function.update, Ne.symm hij,
        NNRat.smul_def]
  by_cases hkj : k = j
  · subst k
    cases hi : assigned i with
    | none => simp [partialCollision, hij, hk, hi, Function.update]
    | some x => simp [partialCollision, hij, hk, hi, Function.update, NNRat.smul_def]
  simp only [partialCollision, hij, ↓reduceIte, Function.update_of_ne (Ne.symm hki),
    Function.update_of_ne (Ne.symm hkj), Fintype.expect_const]

end Cslib.BalancedSchedules
