/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Query.Submodular.ValueQuery
public import Complexity.Algorithms.Lean.Submodular.Greedy
public import Cslib.Algorithms.Lean.Query.Bounds

/-!
# Value-Oracle Query Complexity of Submodular Greedy Maximization

This module lifts `submodularGreedyM` into `FreeM (ValueQuery α β)` as `submodularGreedyQuery`,
proves that `FreeM.eval` recovers the pure `submodularGreedy` algorithm against any value oracle,
and establishes sharp query-complexity bounds ([NemhauserWolseyFisher1978], Section 4):

1. Exact multi-round query count `(submodularGreedyQuery xs k).countQueries oracle =
   ∑ t ∈ Finset.range k, (xs.toFinset.card - t)` (`countQueries_submodularGreedyQuery_eq`), yielding
   at most `k * xs.toFinset.card ≤ k * xs.length` value queries across `k` greedy rounds against
   any oracle (`countQueries_submodularGreedyQuery_le_mul_card`,
   `countQueries_submodularGreedyQuery_le_mul_length`, `submodularGreedyQuery_upperBound`).
2. Exact single-round specialization `(submodularGreedyQuery xs 1).countQueries oracle =
   xs.toFinset.card` (`countQueries_submodularGreedyQuery_one`), which matches the adversarial
   lower bound for `k = 1` and `xs.toFinset.card ≥ 2` in
   `Complexity.Algorithms.Lean.Query.Submodular.LowerBound`.
3. End-to-end `(1 - (1 - 1/k)^k)` and `(1 - 1/e)` approximation corollaries for the query program.

## Main definitions

* `Cslib.Query.submodularGreedyQuery`: `k`-step greedy algorithm in `FreeM (ValueQuery α β)`.

## Main results

* `eval_submodularGreedyQuery`, `eval_submodularGreedyQuery_oracleOf`: agreement with
  `submodularGreedy`.
* `countQueries_submodularGreedyQuery_eq`: exact `∑ t ∈ Finset.range k, (xs.toFinset.card - t)`
  query count across `k` greedy rounds.
* `countQueries_submodularGreedyQuery_le_mul_card`,
  `countQueries_submodularGreedyQuery_le_mul_length`, `submodularGreedyQuery_upperBound`:
  `k * n` value-query upper bounds.
* `countQueries_submodularGreedyQuery_one`: exact `xs.toFinset.card` query count at budget `k = 1`.
* `one_sub_exp_neg_one_mul_le_eval_submodularGreedyQuery`: `(1 - 1/e)` guarantee for the oracle
  program.

## References

* [NemhauserWolseyFisher1978] George L. Nemhauser, Laurence A. Wolsey, and Marshall L. Fisher,
  *An Analysis of Approximations for Maximizing Submodular Set Functions—I*, 1978.
-/

public section

open Cslib.Algorithms.Lean.Submodular

namespace Cslib.Query

/-- Value-oracle query tree for `k`-step greedy cardinality-constrained submodular maximization. -/
@[expose] def submodularGreedyQuery {α β : Type} [DecidableEq α] [LinearOrder β]
    (xs : List α) (k : ℕ) : FreeM (ValueQuery α β) (Finset α) :=
  submodularGreedyM ValueQuery.ask xs k

section EvalAndCount

variable {α β : Type} [DecidableEq α] [LinearOrder β]

/-- Evaluating `submodularGreedyQuery` against `oracle` agrees with `submodularGreedy` on
`fun S => oracle (.value S)`. -/
@[simp] theorem eval_submodularGreedyQuery
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (xs : List α) (k : ℕ) :
    (submodularGreedyQuery xs k).eval oracle =
      submodularGreedy (fun S => oracle (.value S)) xs k :=
  Id.pure_injective <| by
    simp [submodularGreedyQuery,
      FreeM.isMonadHom_pure_eval oracle |>.map_submodularGreedyM _ xs k]

theorem eval_submodularGreedyQuery_oracleOf
    (f : Finset α → β) (xs : List α) (k : ℕ) :
    (submodularGreedyQuery xs k).eval (ValueQuery.oracleOf f) =
      submodularGreedy f xs k := by
  simp

private theorem countQueries_scanCandidatesM
    (oracle : {ι : Type} → ValueQuery α β ι → ι)
    (S : Finset α) (best : α) (bestVal : β) (cs : List α) :
    (scanCandidatesM ValueQuery.ask S best bestVal cs).countQueries oracle = cs.length := by
  induction cs generalizing best bestVal with
  | nil => simp [scanCandidatesM]
  | cons c cs ih =>
    simp only [scanCandidatesM, FreeM.countQueries_bind, ValueQuery.countQueries_ask,
      ValueQuery.eval_ask]
    by_cases h : bestVal < oracle (.value (insert c S)) <;> simp [h, ih, Nat.add_comm]

private theorem countQueries_submodularGreedyStepM_eq
    (oracle : {ι : Type} → ValueQuery α β ι → ι)
    (u : List α) (S : Finset α) :
    (submodularGreedyStepM ValueQuery.ask u S).countQueries oracle =
      (u.filter (· ∉ S)).length := by
  unfold submodularGreedyStepM
  cases u.filter (· ∉ S) with
  | nil => simp
  | cons c₀ cs =>
    simp [countQueries_scanCandidatesM, Nat.add_comm]

private theorem eval_submodularGreedyStepM
    (oracle : {ι : Type} → ValueQuery α β ι → ι)
    (u : List α) (S : Finset α) :
    (submodularGreedyStepM ValueQuery.ask u S).eval oracle =
      submodularGreedyStep (fun T => oracle (.value T)) u S :=
  Id.pure_injective <| by
    simp [FreeM.isMonadHom_pure_eval oracle |>.map_submodularGreedyStepM _ u S]

private theorem length_filter_notMem_eq_sub
    {u : List α} (hu : u.Nodup) {S : Finset α} (hS : S ⊆ u.toFinset) :
    (u.filter (· ∉ S)).length = u.length - S.card := by
  have hnodup : (u.filter (· ∉ S)).Nodup := hu.filter _
  have htoFinset : (u.filter (· ∉ S)).toFinset = u.toFinset \ S := by
    ext x
    simp
  rw [← List.toFinset_card_of_nodup hnodup, htoFinset, Finset.card_sdiff_of_subset hS,
    List.toFinset_card_of_nodup hu]

private theorem length_sub_card_submodularGreedyStep
    (f : Finset α → β) {u : List α} (hu : u.Nodup) {S : Finset α} (hS : S ⊆ u.toFinset) :
    u.length - (submodularGreedyStep f u S).card = u.length - S.card - 1 := by
  unfold submodularGreedyStep
  cases hfilt : u.filter (· ∉ S) with
  | nil =>
    dsimp only
    have hzero := length_filter_notMem_eq_sub hu hS
    rw [hfilt, List.length_nil] at hzero
    omega
  | cons c₀ cs =>
    dsimp only
    have hmem : (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 ∈ c₀ :: cs :=
      scanCandidates_fst_mem f S c₀ (f (insert c₀ S)) cs
    rw [← hfilt] at hmem
    have hnotMem : (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 ∉ S :=
      of_decide_eq_true (List.mem_filter.mp hmem).2
    rw [Finset.card_insert_of_notMem hnotMem]
    omega

private theorem countQueries_submodularGreedyLoopM_eq
    (oracle : {ι : Type} → ValueQuery α β ι → ι)
    {u : List α} (hu : u.Nodup) (k : ℕ) {S : Finset α} (hS : S ⊆ u.toFinset) :
    (submodularGreedyLoopM ValueQuery.ask u k S).countQueries oracle =
      ∑ t ∈ Finset.range k, (u.length - S.card - t) := by
  induction k generalizing S with
  | zero => simp [submodularGreedyLoopM]
  | succ k ih =>
    simp only [submodularGreedyLoopM, FreeM.countQueries_bind,
      countQueries_submodularGreedyStepM_eq, length_filter_notMem_eq_sub hu hS,
      eval_submodularGreedyStepM]
    let f : Finset α → β := fun T => oracle (.value T)
    have hS' : submodularGreedyStep f u S ⊆ u.toFinset :=
      submodularGreedyStep_subset_toFinset f hS
    rw [ih hS', Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.add_comm (∑ x ∈ Finset.range k, _)]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [length_sub_card_submodularGreedyStep f hu hS]
    omega

/-- Exact multi-round query count: across `k` greedy rounds, `submodularGreedyQuery xs k` evaluates
`xs.toFinset.card - t` remaining candidates in round `t` (`0` once all distinct candidates are
selected), making `∑ t ∈ Finset.range k, (xs.toFinset.card - t)` value queries in total. -/
theorem countQueries_submodularGreedyQuery_eq
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (xs : List α) (k : ℕ) :
    (submodularGreedyQuery xs k).countQueries oracle =
      ∑ t ∈ Finset.range k, (xs.toFinset.card - t) := by
  have h := countQueries_submodularGreedyLoopM_eq oracle (nodup_dedupFirst xs) k
    (Finset.empty_subset (dedupFirst xs).toFinset)
  simpa [submodularGreedyQuery, submodularGreedyM, length_dedupFirst] using h

@[simp] theorem countQueries_submodularGreedyQuery_zero
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (xs : List α) :
    (submodularGreedyQuery xs 0).countQueries oracle = 0 := by
  simp [countQueries_submodularGreedyQuery_eq]

/-- At budget `k = 1`, `submodularGreedyQuery` evaluates every distinct ground singleton once,
making **exact** query count `xs.toFinset.card`. -/
theorem countQueries_submodularGreedyQuery_one
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (xs : List α) :
    (submodularGreedyQuery xs 1).countQueries oracle = xs.toFinset.card := by
  simp [countQueries_submodularGreedyQuery_eq]

/-- Pointwise query bound in terms of distinct ground elements: `submodularGreedyQuery xs k` makes
at most `k * xs.toFinset.card` value queries against any oracle. -/
theorem countQueries_submodularGreedyQuery_le_mul_card
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (xs : List α) (k : ℕ) :
    (submodularGreedyQuery xs k).countQueries oracle ≤ k * xs.toFinset.card := by
  rw [countQueries_submodularGreedyQuery_eq]
  simpa using Finset.sum_le_card_nsmul (Finset.range k)
    (fun t => xs.toFinset.card - t) xs.toFinset.card (fun t _ => Nat.sub_le _ _)

/-- Pointwise query bound in terms of input list length: `submodularGreedyQuery xs k` makes at most
`k * xs.length` value queries against any oracle. -/
theorem countQueries_submodularGreedyQuery_le_mul_length
    (oracle : {ι : Type} → ValueQuery α β ι → ι) (xs : List α) (k : ℕ) :
    (submodularGreedyQuery xs k).countQueries oracle ≤ k * xs.length :=
  (countQueries_submodularGreedyQuery_le_mul_card oracle xs k).trans
    (Nat.mul_le_mul_left k (List.toFinset_card_le xs))

/-- Uniform `Cslib.Query.UpperBound`: for fixed budget `k`, `submodularGreedyQuery · k` uses at
most `k * n` value queries on inputs of length at most `n`. -/
theorem submodularGreedyQuery_upperBound (k : ℕ) :
    UpperBound (fun xs : List α => submodularGreedyQuery (β := β) xs k)
      List.length (k * ·) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.mul_le_mul_left k h)
    (fun oracle xs => countQueries_submodularGreedyQuery_le_mul_length oracle xs k)

end EvalAndCount

section OracleApproximation

/-- Algebraic `1 - (1 - 1/k)^k` approximation guarantee for `submodularGreedyQuery` over any
strictly ordered field (`ℚ`, `ℝ`, …). -/
theorem one_sub_pow_mul_le_eval_submodularGreedyQuery
    {α β : Type} [DecidableEq α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    {xs : List α} {k : ℕ} (hk : 0 < k)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - (1 - 1 / (k : β)) ^ k) * f OPT ≤
      f ((submodularGreedyQuery xs k).eval (ValueQuery.oracleOf f)) := by
  rw [eval_submodularGreedyQuery_oracleOf]
  exact one_sub_pow_mul_le_submodularGreedy hf hmono hf0 hk hOPT_sub hOPT_card

/-- Real `(1 - 1/e)` approximation guarantee for `submodularGreedyQuery` for every `k : ℕ`. -/
theorem one_sub_exp_neg_one_mul_le_eval_submodularGreedyQuery
    {α : Type} [DecidableEq α]
    {f : Finset α → ℝ} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    (xs : List α) (k : ℕ)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * f OPT ≤
      f ((submodularGreedyQuery xs k).eval (ValueQuery.oracleOf f)) := by
  rw [eval_submodularGreedyQuery_oracleOf]
  exact one_sub_exp_neg_one_mul_le_submodularGreedy hf hmono hf0 xs k hOPT_sub hOPT_card

end OracleApproximation

end Cslib.Query
