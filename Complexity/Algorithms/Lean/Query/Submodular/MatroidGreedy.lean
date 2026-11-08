/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Query.Matroid.IndepQuery
public import Complexity.Algorithms.Lean.Query.Submodular.ValueQuery
public import Complexity.Algorithms.Lean.Query.SumQuery
public import Complexity.Algorithms.Lean.Submodular.MatroidGreedy
public import Cslib.Algorithms.Lean.Query.Bounds
import Complexity.Foundations.Data.List.EraseDups
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Matroid.Minor.Restrict

/-!
# Value- and Independence-Oracle Query Complexity of Matroid-Constrained Submodular Greedy

This module runs the Fisher–Nemhauser–Wolsey greedy algorithm `submodularMatroidGreedyM` in
`FreeM (SumQuery (ValueQuery α β) (IndepQuery α))`, so that value-oracle queries (`f S`) and
independence-oracle queries (`indep S`) are charged separately by `SumQuery.countInl` and
`SumQuery.countInr` ([FisherNemhauserWolsey1978]; [CalinescuChekuriPalVondrak2011], Appendix B).

With `n = xs.toFinset.card` distinct ground elements and greedy output `G`:

1. Round `t` (current set of size `t`) makes exactly `n - t` independence queries, one per
   remaining element, and the algorithm runs rounds `t = 0, …, |G|` (the last one finds no
   feasible element, or tests nothing when `|G| = n`). Hence exactly
   `∑ t ∈ range (|G| + 1), (n - t)` independence queries (`countInr_submodularMatroidGreedyQuery`).
   Under a matroid oracle, `|G|` is the rank `r` of the ground set, so the count is
   `∑ t ∈ range (r + 1), (n - t)` for any basis of size `r`.
2. Round `t` makes one value query per feasible candidate, so the number of value queries is
   `∑ t ∈ range |G|, |feasibleCandidates indep u S_t|` along the greedy chain
   (`countInl_submodularMatroidGreedyQuery`), at most the number of independence queries.
3. Both counts are at most `n (n + 1) / 2`, and the total is at most `n (n + 1)`
   (`submodularMatroidGreedyQuery_upperBound`).

## Main definitions

* `Cslib.Query.submodularMatroidGreedyQuery`: the greedy algorithm as a query program.

## Main results

* `eval_submodularMatroidGreedyQuery`: evaluation agrees with `submodularMatroidGreedy`.
* `countInr_submodularMatroidGreedyQuery`, `countInr_submodularMatroidGreedyQuery_of_isBasis'`:
  exact independence-query counts.
* `countInl_submodularMatroidGreedyQuery`, `countInl_le_countInr_submodularMatroidGreedyQuery`:
  exact value-query count and comparison.
* `two_mul_countInr_submodularMatroidGreedyQuery_le`,
  `two_mul_countInl_submodularMatroidGreedyQuery_le`,
  `countQueries_submodularMatroidGreedyQuery_le`, `submodularMatroidGreedyQuery_upperBound`:
  quadratic upper bounds.
* `half_le_eval_submodularMatroidGreedyQuery`,
  `div_card_succ_le_eval_submodularMatroidGreedyQuery`: the `1/2` (matroid) and `1/(k+1)`
  (intersection of `k` matroids) guarantees for the query program.

## References

* [FisherNemhauserWolsey1978] Marshall L. Fisher, George L. Nemhauser, and Laurence A. Wolsey,
  *An Analysis of Approximations for Maximizing Submodular Set Functions—II*, 1978.
* [CalinescuChekuriPalVondrak2011] Gruia Calinescu, Chandra Chekuri, Martin Pál, and Jan Vondrák,
  *Maximizing a Monotone Submodular Function Subject to a Matroid Constraint*, 2011.
-/

public section

open Cslib.Algorithms.Lean.Submodular

namespace Cslib.Query

/-- Query signature with value queries `.inl (.value S)` and independence queries
`.inr (.indep S)`. -/
abbrev ValueIndepQuery (α β : Type) : Type → Type := SumQuery (ValueQuery α β) (IndepQuery α)

/-- The Fisher–Nemhauser–Wolsey greedy algorithm as a program asking value queries and
independence queries. -/
@[expose] def submodularMatroidGreedyQuery {α β : Type} [DecidableEq α] [LinearOrder β]
    (xs : List α) : FreeM (ValueIndepQuery α β) (Finset α) :=
  submodularMatroidGreedyM (fun S => SumQuery.liftInl (.value S))
    (fun S => SumQuery.liftInr (.indep S)) xs

section EvalAndCount

variable {α β : Type} [DecidableEq α] [LinearOrder β]

/-- Evaluation against any oracle agrees with the pure greedy algorithm on the answered value and
independence functions. -/
@[simp] theorem eval_submodularMatroidGreedyQuery
    (oracle : {ι : Type} → ValueIndepQuery α β ι → ι) (xs : List α) :
    (submodularMatroidGreedyQuery xs).eval oracle =
      submodularMatroidGreedy (fun S => oracle (.inl (.value S)))
        (fun S => oracle (.inr (.indep S))) xs :=
  Id.pure_injective <| by
    simp [submodularMatroidGreedyQuery,
      FreeM.isMonadHom_pure_eval oracle |>.map_submodularMatroidGreedyM _ _ xs]

theorem eval_combine_submodularMatroidGreedyQuery (f : Finset α → β) (indep : Finset α → Bool)
    (xs : List α) :
    (submodularMatroidGreedyQuery xs).eval
        (SumQuery.combine (ValueQuery.oracleOf f) (IndepQuery.oracleOf indep)) =
      submodularMatroidGreedy f indep xs := by
  simp

variable (oracle : {ι : Type} → ValueIndepQuery α β ι → ι)

/-! ### Per-round counts

The private lemmas are stated for the value and independence functions `f` and `indep` answered by
`oracle` (hypotheses `hf` and `hi`), which keeps the statements readable. -/

omit [LinearOrder β] in
private theorem countInl_filterIndepM (S : Finset α) (cs : List α) :
    SumQuery.countInl oracle
      (filterIndepM (fun T => SumQuery.liftInr (.indep T)) S cs) = 0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [filterIndepM, SumQuery.countInl_bind, SumQuery.countInl_liftInr,
      SumQuery.countInl_map, ih, bind_pure_comp]

omit [LinearOrder β] in
private theorem countInr_filterIndepM (S : Finset α) (cs : List α) :
    SumQuery.countInr oracle
      (filterIndepM (fun T => SumQuery.liftInr (.indep T)) S cs) = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [filterIndepM, SumQuery.countInr_bind, SumQuery.countInr_liftInr,
      SumQuery.countInr_map, ih, bind_pure_comp, List.length_cons]
    omega

omit [LinearOrder β] in
private theorem eval_filterIndepM {indep : Finset α → Bool}
    (hi : ∀ T, oracle (.inr (.indep T)) = indep T) (S : Finset α) (cs : List α) :
    (filterIndepM (fun T => SumQuery.liftInr (.indep T)) S cs).eval oracle =
      cs.filter fun c => indep (insert c S) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [filterIndepM, FreeM.eval_bind, FreeM.eval_lift, FreeM.eval_pure, ih, hi,
      List.filter_cons]

private theorem countInl_scanCandidatesM (S : Finset α) (best : α) (bestVal : β)
    (cs : List α) :
    SumQuery.countInl oracle
      (scanCandidatesM (fun T => SumQuery.liftInl (.value T)) S best bestVal cs) = cs.length := by
  induction cs generalizing best bestVal with
  | nil => rfl
  | cons c cs ih =>
    simp only [scanCandidatesM, SumQuery.countInl_bind, SumQuery.countInl_liftInl]
    split_ifs <;> simp [ih, Nat.add_comm]

private theorem countInr_scanCandidatesM (S : Finset α) (best : α) (bestVal : β)
    (cs : List α) :
    SumQuery.countInr oracle
      (scanCandidatesM (fun T => SumQuery.liftInl (.value T)) S best bestVal cs) = 0 := by
  induction cs generalizing best bestVal with
  | nil => rfl
  | cons c cs ih =>
    simp only [scanCandidatesM, SumQuery.countInr_bind, SumQuery.countInr_liftInl]
    split_ifs <;> simp [ih]

private theorem eval_stepM {f : Finset α → β} {indep : Finset α → Bool}
    (hf : ∀ T, oracle (.inl (.value T)) = f T) (hi : ∀ T, oracle (.inr (.indep T)) = indep T)
    (u : List α) (S : Finset α) :
    (submodularMatroidGreedyStepM (fun T => SumQuery.liftInl (.value T))
      (fun T => SumQuery.liftInr (.indep T)) u S).eval oracle =
      submodularMatroidGreedyStep f indep u S :=
  Id.pure_injective <| by
    simp [FreeM.isMonadHom_pure_eval oracle |>.map_submodularMatroidGreedyStepM _ _ u S, hf, hi]

private theorem countInl_stepM {indep : Finset α → Bool}
    (hi : ∀ T, oracle (.inr (.indep T)) = indep T) (u : List α) (S : Finset α) :
    SumQuery.countInl oracle
      (submodularMatroidGreedyStepM (fun T => SumQuery.liftInl (.value T))
        (fun T => SumQuery.liftInr (.indep T)) u S) =
      (feasibleCandidates indep u S).length := by
  simp only [submodularMatroidGreedyStepM, SumQuery.countInl_bind, countInl_filterIndepM,
    eval_filterIndepM oracle hi, Nat.zero_add]
  change SumQuery.countInl oracle (match feasibleCandidates indep u S with
    | [] => pure none
    | c₀ :: cs => _) = _
  cases feasibleCandidates indep u S with
  | nil => rfl
  | cons c₀ cs => simp [countInl_scanCandidatesM, Nat.add_comm]

private theorem countInr_stepM {indep : Finset α → Bool}
    (hi : ∀ T, oracle (.inr (.indep T)) = indep T) (u : List α) (S : Finset α) :
    SumQuery.countInr oracle
      (submodularMatroidGreedyStepM (fun T => SumQuery.liftInl (.value T))
        (fun T => SumQuery.liftInr (.indep T)) u S) = (u.filter (· ∉ S)).length := by
  simp only [submodularMatroidGreedyStepM, SumQuery.countInr_bind, countInr_filterIndepM,
    eval_filterIndepM oracle hi]
  change _ + SumQuery.countInr oracle (match feasibleCandidates indep u S with
    | [] => pure none
    | c₀ :: cs => _) = _
  cases feasibleCandidates indep u S with
  | nil => rfl
  | cons c₀ cs => simp [countInr_scanCandidatesM]

omit [LinearOrder β] in
private theorem length_filter_notMem_add_card {u : List α} (hu : u.Nodup) {S : Finset α}
    (hS : S ⊆ u.toFinset) : (u.filter (· ∉ S)).length + S.card = u.length := by
  have hnodup : (u.filter (· ∉ S)).Nodup := hu.filter _
  have htoFinset : (u.filter (· ∉ S)).toFinset = u.toFinset \ S := by
    ext x
    simp
  rw [← List.toFinset_card_of_nodup hnodup, htoFinset, Finset.card_sdiff_of_subset hS,
    ← List.toFinset_card_of_nodup hu, Nat.sub_add_cancel (Finset.card_le_card hS)]

/-! ### Exact counts -/

private theorem countInr_loopM {f : Finset α → β} {indep : Finset α → Bool}
    (hf : ∀ T, oracle (.inl (.value T)) = f T) (hi : ∀ T, oracle (.inr (.indep T)) = indep T)
    {u : List α} (hu : u.Nodup) (k : ℕ) {S : Finset α} (hS : S ⊆ u.toFinset)
    (hk : S.card + k = u.length) :
    SumQuery.countInr oracle
      (submodularMatroidGreedyLoopM (fun T => SumQuery.liftInl (.value T))
        (fun T => SumQuery.liftInr (.indep T)) u k S) =
      ∑ t ∈ Finset.Ico S.card ((submodularMatroidGreedyLoop f indep u k S).card + 1),
        (u.length - t) := by
  induction k generalizing S with
  | zero =>
    simp only [submodularMatroidGreedyLoopM, SumQuery.countInr_pure,
      submodularMatroidGreedyLoop, Nat.Ico_succ_singleton, Finset.sum_singleton]
    omega
  | succ k ih =>
    simp only [submodularMatroidGreedyLoopM, SumQuery.countInr_bind, countInr_stepM oracle hi,
      eval_stepM oracle hf hi, submodularMatroidGreedyLoop]
    have hlen := length_filter_notMem_add_card hu hS
    rcases h : submodularMatroidGreedyStep f indep u S with _ | S'
    · simp only [SumQuery.countInr_pure, Nat.add_zero, Nat.Ico_succ_singleton,
        Finset.sum_singleton]
      omega
    · obtain ⟨c, hc, rfl, -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
      have hc' := mem_feasibleCandidates.mp hc
      have hS' : insert c S ⊆ u.toFinset :=
        Finset.insert_subset (List.mem_toFinset.mpr hc'.1) hS
      have hcard : (insert c S).card = S.card + 1 := Finset.card_insert_of_notMem hc'.2.1
      dsimp only
      rw [ih hS' (by omega), hcard]
      have hlt : S.card < (submodularMatroidGreedyLoop f indep u k (insert c S)).card + 1 := by
        have := Finset.card_le_card (subset_submodularMatroidGreedyLoop f indep u k (insert c S))
        omega
      rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
      omega

/-- **Exact independence-query count.** With `n = xs.toFinset.card` distinct ground elements and
greedy output `G`, the query program makes exactly `∑ t ∈ range (|G| + 1), (n - t)` independence
queries: `n - t` in each round `t = 0, …, |G|`. -/
theorem countInr_submodularMatroidGreedyQuery (xs : List α) :
    SumQuery.countInr oracle (submodularMatroidGreedyQuery xs) =
      ∑ t ∈ Finset.range
        ((submodularMatroidGreedy (fun S => oracle (.inl (.value S)))
          (fun S => oracle (.inr (.indep S))) xs).card + 1), (xs.toFinset.card - t) := by
  have h := countInr_loopM oracle (f := fun S => oracle (.inl (.value S)))
    (indep := fun S => oracle (.inr (.indep S))) (fun _ => rfl) (fun _ => rfl)
    (List.nodup_eraseDups xs) xs.eraseDups.length (Finset.empty_subset _) (by simp)
  rw [Finset.card_empty, ← Finset.range_eq_Ico] at h
  rw [← List.length_eraseDups]
  exact h

private theorem countInl_loopM_chain {f : Finset α → β} {indep : Finset α → Bool}
    (hf : ∀ T, oracle (.inl (.value T)) = f T) (hi : ∀ T, oracle (.inr (.indep T)) = indep T)
    (u : List α) (k t : ℕ) :
    SumQuery.countInl oracle
      (submodularMatroidGreedyLoopM (fun T => SumQuery.liftInl (.value T))
        (fun T => SumQuery.liftInr (.indep T)) u k (submodularMatroidGreedyChain f indep u t)) =
      ∑ s ∈ Finset.range k,
        (feasibleCandidates indep u (submodularMatroidGreedyChain f indep u (t + s))).length := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [submodularMatroidGreedyLoopM, SumQuery.countInl_bind, countInl_stepM oracle hi,
      eval_stepM oracle hf hi]
    rw [Finset.sum_range_succ', Nat.add_zero]
    rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
      with _ | S'
    · have hnil := submodularMatroidGreedyStep_eq_none_iff.mp h
      have hstable : ∀ s, submodularMatroidGreedyChain f indep u (t + (s + 1)) =
          submodularMatroidGreedyChain f indep u t := fun s =>
        submodularMatroidGreedyChain_add_of_step_eq_none h (s + 1)
      simp [hstable, hnil]
    · have hS' : S' = submodularMatroidGreedyChain f indep u (t + 1) := by
        rw [submodularMatroidGreedyChain_succ, h, Option.getD_some]
      dsimp only
      rw [hS', ih (t + 1), Nat.add_comm]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.add_right_comm, Nat.add_assoc]

/-- **Exact value-query count.** Round `t` of the greedy algorithm makes one value query per
feasible candidate, so the query program makes exactly
`∑ t ∈ range n, |feasibleCandidates indep u S_t|` value queries along the greedy chain `S_t`, where
`u = xs.eraseDups`, `n = xs.toFinset.card`, and `indep`, `f` are the functions answered by the
oracle (rounds after the algorithm stops contribute `0`). -/
theorem countInl_submodularMatroidGreedyQuery (xs : List α) :
    SumQuery.countInl oracle (submodularMatroidGreedyQuery xs) =
      ∑ t ∈ Finset.range xs.toFinset.card,
        (feasibleCandidates (fun S => oracle (.inr (.indep S))) xs.eraseDups
          (submodularMatroidGreedyChain (fun S => oracle (.inl (.value S)))
            (fun S => oracle (.inr (.indep S))) xs.eraseDups t)).length := by
  have h := countInl_loopM_chain oracle (f := fun S => oracle (.inl (.value S)))
    (indep := fun S => oracle (.inr (.indep S))) (fun _ => rfl) (fun _ => rfl)
    xs.eraseDups xs.eraseDups.length 0
  simp only [Nat.zero_add] at h
  rw [← List.length_eraseDups]
  exact h

private theorem countInl_le_countInr_loopM {indep : Finset α → Bool}
    {f : Finset α → β} (hf : ∀ T, oracle (.inl (.value T)) = f T)
    (hi : ∀ T, oracle (.inr (.indep T)) = indep T) (u : List α) (k : ℕ) (S : Finset α) :
    SumQuery.countInl oracle
        (submodularMatroidGreedyLoopM (fun T => SumQuery.liftInl (.value T))
          (fun T => SumQuery.liftInr (.indep T)) u k S) ≤
      SumQuery.countInr oracle
        (submodularMatroidGreedyLoopM (fun T => SumQuery.liftInl (.value T))
          (fun T => SumQuery.liftInr (.indep T)) u k S) := by
  induction k generalizing S with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [submodularMatroidGreedyLoopM, SumQuery.countInl_bind, SumQuery.countInr_bind,
      countInl_stepM oracle hi, countInr_stepM oracle hi, eval_stepM oracle hf hi]
    have hle : (feasibleCandidates indep u S).length ≤ (u.filter (· ∉ S)).length :=
      List.filter_sublist.length_le
    rcases submodularMatroidGreedyStep f indep u S with _ | S'
    · simpa using hle
    · exact Nat.add_le_add hle (ih S')

/-- The query program makes at most as many value queries as independence queries. -/
theorem countInl_le_countInr_submodularMatroidGreedyQuery (xs : List α) :
    SumQuery.countInl oracle (submodularMatroidGreedyQuery xs) ≤
      SumQuery.countInr oracle (submodularMatroidGreedyQuery xs) :=
  countInl_le_countInr_loopM oracle (f := fun S => oracle (.inl (.value S)))
    (indep := fun S => oracle (.inr (.indep S))) (fun _ => rfl) (fun _ => rfl) _ _ _

/-! ### Upper bounds -/

/-- At most `n (n + 1) / 2` independence queries, `n = xs.toFinset.card`, stated without
division. -/
theorem two_mul_countInr_submodularMatroidGreedyQuery_le (xs : List α) :
    2 * SumQuery.countInr oracle (submodularMatroidGreedyQuery xs) ≤
      xs.toFinset.card * (xs.toFinset.card + 1) := by
  rw [countInr_submodularMatroidGreedyQuery]
  set G := submodularMatroidGreedy (fun S => oracle (.inl (.value S)))
    (fun S => oracle (.inr (.indep S))) xs
  set n := xs.toFinset.card
  have hG : G.card ≤ n := Finset.card_le_card (submodularMatroidGreedy_subset_toFinset _ _ xs)
  have hsum : ∑ t ∈ Finset.range (n + 1), (n - t) = ∑ t ∈ Finset.range (n + 1), t := by
    simpa using Finset.sum_range_reflect (fun t => t) (n + 1)
  have hgauss := Finset.sum_range_id_mul_two (n + 1)
  have hmono : ∑ t ∈ Finset.range (G.card + 1), (n - t) ≤
      ∑ t ∈ Finset.range (n + 1), (n - t) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hG))
  rw [hsum] at hmono
  simp only [Nat.add_sub_cancel] at hgauss
  rw [Nat.mul_comm n]
  omega

/-- At most `n (n + 1) / 2` value queries, `n = xs.toFinset.card`, stated without division. -/
theorem two_mul_countInl_submodularMatroidGreedyQuery_le (xs : List α) :
    2 * SumQuery.countInl oracle (submodularMatroidGreedyQuery xs) ≤
      xs.toFinset.card * (xs.toFinset.card + 1) :=
  (Nat.mul_le_mul_left 2 (countInl_le_countInr_submodularMatroidGreedyQuery oracle xs)).trans
    (two_mul_countInr_submodularMatroidGreedyQuery_le oracle xs)

/-- Total query bound: at most `n (n + 1)` value and independence queries. -/
theorem countQueries_submodularMatroidGreedyQuery_le (xs : List α) :
    (submodularMatroidGreedyQuery xs).countQueries oracle ≤
      xs.toFinset.card * (xs.toFinset.card + 1) := by
  rw [← SumQuery.countInl_add_countInr]
  have h1 := two_mul_countInl_submodularMatroidGreedyQuery_le oracle xs
  have h2 := two_mul_countInr_submodularMatroidGreedyQuery_le oracle xs
  omega

/-- Uniform `Cslib.Query.UpperBound`: at most `m (m + 1)` total queries on ground lists of length
at most `m`. -/
theorem submodularMatroidGreedyQuery_upperBound :
    UpperBound (fun xs : List α => submodularMatroidGreedyQuery (β := β) xs)
      List.length (fun m => m * (m + 1)) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.mul_le_mul h (Nat.succ_le_succ h))
    (fun oracle xs => (countQueries_submodularMatroidGreedyQuery_le oracle xs).trans
      (Nat.mul_le_mul (List.toFinset_card_le xs) (Nat.succ_le_succ (List.toFinset_card_le xs))))

end EvalAndCount

/-! ## Matroid oracles -/

section Matroid

variable {α β : Type} [DecidableEq α] [LinearOrder β]

/-- Under an independence oracle implementing `M`, the number of independence queries is
`∑ t ∈ range (r + 1), (n - t)`, where `r = B.card` for any basis `B` of the ground list. -/
theorem countInr_submodularMatroidGreedyQuery_of_isBasis' {M : Matroid α}
    (oracle : {ι : Type} → ValueIndepQuery α β ι → ι)
    (hM : ∀ S : Finset α, oracle (.inr (.indep S)) = true ↔ M.Indep (S : Set α)) (xs : List α)
    {B : Finset α} (hB : M.IsBasis' (B : Set α) {x | x ∈ xs}) :
    SumQuery.countInr oracle (submodularMatroidGreedyQuery xs) =
      ∑ t ∈ Finset.range (B.card + 1), (xs.toFinset.card - t) := by
  rw [countInr_submodularMatroidGreedyQuery]
  have hG := submodularMatroidGreedy_isBasis' hM (fun S => oracle (.inl (.value S))) xs
  have hcard := Matroid.IsBasis'.encard_eq_encard hG hB
  simp only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_inj] at hcard
  rw [hcard]

/-- **`1/2`-approximation for the query program** under a value oracle for a monotone submodular
`f` with `0 ≤ f ∅` and an independence oracle implementing `M`. -/
theorem half_le_eval_submodularMatroidGreedyQuery {β : Type} [Field β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    (hf0 : 0 ≤ f ∅) {M : Matroid α} {indepOracle : {ι : Type} → IndepQuery α ι → ι}
    (hM : IndepQuery.ImplementsMatroid indepOracle M) {xs : List α} {O : Finset α}
    (hO : M.Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    f O / 2 ≤ f ((submodularMatroidGreedyQuery xs).eval
      (SumQuery.combine (ValueQuery.oracleOf f) indepOracle)) := by
  rw [eval_submodularMatroidGreedyQuery]
  exact half_le_submodularMatroidGreedy_of_matroid hf hmono hf0 (indep := fun S =>
    indepOracle (.indep S)) hM hO hOxs

/-- **`1/(k+1)`-approximation for the query program** over the intersection of `k ≥ 1`
matroids. -/
theorem div_card_succ_le_eval_submodularMatroidGreedyQuery {β : Type} [Field β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    (hf0 : 0 ≤ f ∅) {ι : Type} [Fintype ι] [Nonempty ι] {M : ι → Matroid α}
    {indepOracle : {κ : Type} → IndepQuery α κ → κ}
    (hM : ∀ S : Finset α, indepOracle (.indep S) = true ↔ ∀ i, (M i).Indep (S : Set α))
    {xs : List α} {O : Finset α} (hO : ∀ i, (M i).Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    f O / (Fintype.card ι + 1) ≤ f ((submodularMatroidGreedyQuery xs).eval
      (SumQuery.combine (ValueQuery.oracleOf f) indepOracle)) := by
  rw [eval_submodularMatroidGreedyQuery]
  exact div_card_succ_le_submodularMatroidGreedy_of_iInter_matroid hf hmono hf0
    (indep := fun S => indepOracle (.indep S)) hM hO hOxs

end Matroid

end Cslib.Query
