/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parallel Moser–Tardos algorithm

This module formalizes the parallel resampling algorithm for the variable-model Lovász Local
Lemma ([MoserTardos2010, Algorithm 1.2, Section 4, Theorem 1.3]).

In each parallel round, an admissible selection rule `psel` inspects the current assignment
`current vbl T w` and selects a **maximal independent set** of occurring bad events:
1. every selected event occurs at `current vbl T w` (`IsValidParallelRule.mem`);
2. selected events are pairwise non-adjacent (`¬Adj vbl i j`), i.e., distinct and defined on
   disjoint variable sets (`IsValidParallelRule.pairwise`);
3. every occurring event shares at least one variable with (or equals) some selected event
   (`IsValidParallelRule.max`).

In particular, `psel T w = []` holds if and only if no bad event occurs at `current vbl T w`.
Resampling all events in the chosen batch in sequence appends them onto the cumulative log `w`
(`parallelRun`), preserving `IsLog`. Any event resampled in round `k` yields a witness structure
of depth `k` and size at least `k + 1` ([MoserTardos2010, Lemma 4.1]). Summing the resulting
tail bounds `Pr[parallelRounds ≥ k + 1] ≤ min 1 ((1 - ε)^(k+1) * ∑ i, x i / (1 - x i))` yields
the logarithmic expected round bound `((max 0 (Real.log M) + 1) / ε)` of Theorem 1.3.

## Main definitions

* `Cslib.Probability.MoserTardos.IsValidParallelRule`: admissibility predicate for a parallel
  selection rule choosing a maximal independent set of occurring events.
* `Cslib.Probability.MoserTardos.parallelRun`: the cumulative log after `n` parallel rounds.
* `Cslib.Probability.MoserTardos.parallelRounds`: the number of non-empty parallel rounds
  (`ℝ≥0∞`, equal to `⊤` if no terminating round is reached).
* `Cslib.Probability.MoserTardos.greedyIndependentSubset`,
  `Cslib.Probability.MoserTardos.greedyParallelList`,
  `Cslib.Probability.MoserTardos.greedyParallel`: greedy maximal independent set selection rules.

## Main results

* `Cslib.Probability.MoserTardos.isLog_parallelRun`: parallel execution produces a valid log.
* `Cslib.Probability.MoserTardos.parallel_witness_depth`: [MoserTardos2010, Lemma 4.1] (witness
  structure of depth `k` and cardinality at least `k + 1` for every event resampled in round `k`).
* `Cslib.Probability.MoserTardos.table_succ_le_parallelRounds_le` and
  `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le`: [MoserTardos2010, Theorem 1.3] tail
  and expected round bounds under `Pr[A i] ≤ (1 - ε) * x i * ∏ j ∈ Γ i, (1 - x j)`.
* `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_symmetric`,
  `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_symmetric_of_pos`: symmetric
  specializations under `e * q * (d + 1) ≤ 1 - ε`.
* `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_pmfPi` and
  `Cslib.Probability.MoserTardos.lintegral_parallelRounds_le_pmfPi_symmetric`: `PMF.pi` bridges.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

open Finset MeasureTheory ENNReal

namespace Cslib.Probability.MoserTardos

section ParallelExecution

variable {V ι : Type*} {α : V → Type*}

/-- A parallel selection rule for the Moser–Tardos algorithm chooses, from the table `T` and the
current log `w`, a maximal independent subset of the events occurring at `current vbl T w`.
Returning `[]` indicates that no bad event occurs. -/
structure IsValidParallelRule [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι) : Prop where
  /-- Every chosen event occurs in the current assignment. -/
  mem : ∀ T w i, i ∈ psel T w → current vbl T w ∈ A i
  /-- Distinct steps in a batch have disjoint variable sets (in particular, no duplicates). -/
  pairwise : ∀ T w, (psel T w).Pairwise fun i j => ¬Adj vbl i j
  /-- Every occurring event shares at least one variable with some chosen event. -/
  max : ∀ T w i, current vbl T w ∈ A i → ∃ j ∈ psel T w, Adj vbl i j

/-- A valid parallel rule returns `[]` if and only if no bad event occurs in the current
assignment. -/
theorem IsValidParallelRule.eq_nil_iff [DecidableEq V] {vbl : ι → Finset V}
    {A : ι → Set (∀ v, α v)} {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (h : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) (w : List ι) :
    psel T w = [] ↔ ∀ i, current vbl T w ∉ A i := by
  constructor
  · intro hnil i hi
    obtain ⟨j, hj, -⟩ := h.max T w i hi
    rw [hnil] at hj
    simp at hj
  · intro hnone
    by_contra hne
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
    exact hnone i (h.mem T w i hi)

/-- The cumulative resampling log (latest step first) after `n` rounds of the parallel algorithm
using selection rule `psel` on table `T`. -/
@[expose] def parallelRun (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) : ℕ → List ι
  | 0 => []
  | n + 1 => psel T (parallelRun psel T n) ++ parallelRun psel T n

@[simp]
theorem parallelRun_zero (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) :
    parallelRun psel T 0 = [] := by
  rfl

theorem parallelRun_succ (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) (n : ℕ) :
    parallelRun psel T (n + 1) = psel T (parallelRun psel T n) ++ parallelRun psel T n := by
  rfl

/-- Once a round returns `[]`, all subsequent logs remain unchanged. -/
theorem parallelRun_eq_of_eq_nil {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    {T : ∀ p : V × ℕ, α p.1} {n : ℕ} (hn : psel T (parallelRun psel T n) = []) :
    ∀ {m : ℕ}, n ≤ m → parallelRun psel T m = parallelRun psel T n := by
  intro m hm
  induction m with
  | zero =>
    obtain rfl : n = 0 := Nat.le_zero.1 hm
    rfl
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · rfl
    · have hmn : n ≤ m := Nat.lt_succ_iff.1 hlt
      rw [parallelRun_succ, ih hmn, hn, List.nil_append]

/-- Once a round returns `[]`, all subsequent rounds return `[]`. -/
theorem psel_parallelRun_eq_nil_of_le {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    {T : ∀ p : V × ℕ, α p.1} {n m : ℕ} (hn : psel T (parallelRun psel T n) = [])
    (hnm : n ≤ m) :
    psel T (parallelRun psel T m) = [] := by
  rw [parallelRun_eq_of_eq_nil hn hnm, hn]

private theorem uses_append_eq_of_forall_notMem [DecidableEq V] (vbl : ι → Finset V)
    (b w : List ι) {v : V} (hv : ∀ j ∈ b, v ∉ vbl j) :
    uses vbl (b ++ w) v = uses vbl w v := by
  induction b with
  | nil => simp
  | cons j b ih =>
    rw [List.cons_append, uses_cons]
    have hj : v ∉ vbl j := hv j List.mem_cons_self
    have hrest : uses vbl (b ++ w) v = uses vbl w v :=
      ih fun x hx => hv x (List.mem_cons_of_mem _ hx)
    simp [hj, hrest]

private theorem isLog_append_of_pairwise [DecidableEq V] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (T : ∀ p : V × ℕ, α p.1) {w b : List ι} (hw : IsLog vbl A T w)
    (hmem : ∀ i ∈ b, current vbl T w ∈ A i)
    (hpw : b.Pairwise fun i j => ¬Adj vbl i j) :
    IsLog vbl A T (b ++ w) := by
  induction b with
  | nil => simpa using hw
  | cons i b ih =>
    rw [List.pairwise_cons] at hpw
    have ih' := ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj)) hpw.2
    rw [List.cons_append, isLog_cons]
    refine ⟨?_, ih'⟩
    have hiw : current vbl T w ∈ A i := hmem i List.mem_cons_self
    refine (hA i (fun v hv => ?_)).mp hiw
    rw [current_apply, current_apply, uses_append_eq_of_forall_notMem vbl b w fun j hj hvj => ?_]
    exact (hpw.1 j hj) (adj_of_mem vbl hv hvj)

/-- Every finite prefix `parallelRun psel T n` produced by a valid parallel selection rule is a
valid log. -/
theorem isLog_parallelRun [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel)
    (T : ∀ p : V × ℕ, α p.1) (n : ℕ) :
    IsLog vbl A T (parallelRun psel T n) := by
  induction n with
  | zero => exact isLog_nil vbl A T
  | succ n ih =>
    exact isLog_append_of_pairwise vbl A hA T ih
      (fun i hi => hrule.mem T _ i hi) (hrule.pairwise T _)

/-- The number of non-empty parallel resampling rounds performed by `psel` on `T` (`⊤` if no
round ever returns `[]`). -/
noncomputable def parallelRounds (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (_ : psel T (parallelRun psel T n) ≠ []), ((n : ℝ≥0∞) + 1)

theorem succ_le_parallelRounds_iff (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) (k : ℕ) :
    ((k : ℝ≥0∞) + 1 ≤ parallelRounds psel T) ↔ psel T (parallelRun psel T k) ≠ [] := by
  constructor
  · intro hle hnil
    have hbound : parallelRounds psel T ≤ k := by
      refine iSup₂_le fun n hn => ?_
      have hlt : n < k := by
        by_contra hge
        exact hn (psel_parallelRun_eq_nil_of_le hnil (Nat.le_of_not_lt hge))
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hk : (k : ℝ≥0∞) + 1 ≤ (k : ℝ≥0∞) := hle.trans hbound
    have hlt : (k : ℝ≥0∞) < (k : ℝ≥0∞) + 1 := by
      exact_mod_cast Nat.lt_succ_self k
    exact (not_lt_of_ge hk) hlt
  · intro hne
    exact le_iSup₂ (f := fun n (_ : psel T (parallelRun psel T n) ≠ []) => ((n : ℝ≥0∞) + 1)) k hne

theorem exists_eq_nil_of_parallelRounds_ne_top (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    {T : ∀ p : V × ℕ, α p.1} (hfin : parallelRounds psel T ≠ ⊤) :
    ∃ n : ℕ, psel T (parallelRun psel T n) = [] := by
  by_contra hne
  push Not at hne
  apply hfin
  rw [eq_top_iff]
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hc.ne_top
  exact hn.trans_le (le_self_add.trans ((succ_le_parallelRounds_iff psel T n).2 (hne n)))

theorem parallelRounds_eq_tsum (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) :
    parallelRounds psel T =
      ∑' k : ℕ, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0 := by
  classical
  by_cases hterm : ∃ n, psel T (parallelRun psel T n) = []
  · let n₀ := Nat.find hterm
    have hn₀ : psel T (parallelRun psel T n₀) = [] := Nat.find_spec hterm
    have hlt_ne : ∀ k < n₀, psel T (parallelRun psel T k) ≠ [] := fun k hk => Nat.find_min hterm hk
    have hge_nil : ∀ k ≥ n₀, psel T (parallelRun psel T k) = [] := fun k hk =>
      psel_parallelRun_eq_nil_of_le hn₀ hk
    have htsum : (∑' k : ℕ, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0) = n₀ := by
      have hfin : (∑' k : ℕ, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0) =
          ∑ k ∈ Finset.range n₀, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0 := by
        refine tsum_eq_sum fun k hk => ?_
        rw [Finset.mem_range, not_lt] at hk
        simp [hge_nil k hk]
      rw [hfin]
      have hsum1 :
          (∑ k ∈ Finset.range n₀, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0) =
            ∑ _k ∈ Finset.range n₀, (1 : ℝ≥0∞) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        simp [hlt_ne k hk]
      rw [hsum1]
      simp
    rw [htsum]
    rcases Nat.eq_zero_or_pos n₀ with hn0 | hpos
    · have hzero : ∀ n, psel T (parallelRun psel T n) = [] := fun n =>
        hge_nil n (by omega)
      simp [parallelRounds, hn0, hzero]
    · have hm : n₀ - 1 < n₀ := Nat.sub_lt hpos zero_lt_one
      have hle : (n₀ : ℝ≥0∞) ≤ parallelRounds psel T := by
        have h1 := (succ_le_parallelRounds_iff psel T (n₀ - 1)).2 (hlt_ne (n₀ - 1) hm)
        have heq : ((n₀ - 1 : ℕ) : ℝ≥0∞) + 1 = (n₀ : ℝ≥0∞) := by
          exact_mod_cast Nat.sub_add_cancel hpos
        rwa [heq] at h1
      have hge : parallelRounds psel T ≤ (n₀ : ℝ≥0∞) := by
        refine iSup₂_le fun n hn => ?_
        have hlt : n < n₀ := by
          by_contra hnot
          exact hn (hge_nil n (Nat.le_of_not_lt hnot))
        exact_mod_cast Nat.succ_le_of_lt hlt
      exact le_antisymm hge hle
  · push Not at hterm
    have htop1 : parallelRounds psel T = ⊤ := by
      by_contra hfin
      obtain ⟨n, hn⟩ := exists_eq_nil_of_parallelRounds_ne_top psel hfin
      exact hterm n hn
    have htop2 :
        (∑' k : ℕ, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0) = ⊤ := by
      rw [eq_top_iff]
      refine le_of_forall_lt fun c hc => ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hc.ne_top
      have hsum : (n : ℝ≥0∞) =
          ∑ k ∈ Finset.range n, if psel T (parallelRun psel T k) ≠ [] then (1 : ℝ≥0∞) else 0 := by
        simp [hterm]
      exact hn.trans_le (hsum.symm ▸ sum_le_tsum (Finset.range n))
    rw [htop1, htop2]

end ParallelExecution

section GreedyMIS

variable {V ι : Type*} {α : V → Type*} [DecidableEq V] [DecidableEq ι]

/-- Greedy maximal independent subset of candidates `cand` satisfying Boolean predicate `P`,
scanning right-to-left and accepting each candidate that satisfies `P` and is distinct from and
variable-disjoint from all already-selected elements. -/
@[expose] def greedyIndependentSubset (vbl : ι → Finset V) (P : ι → Bool) : List ι → List ι
  | [] => []
  | i :: is =>
      let rest := greedyIndependentSubset vbl P is
      if P i && rest.all (fun j => decide (i ≠ j) && decide (Disjoint (vbl i) (vbl j))) then
        i :: rest
      else
        rest

private theorem greedyIndependentSubset_mem (vbl : ι → Finset V) (P : ι → Bool)
    (cand : List ι) {i : ι} (hi : i ∈ greedyIndependentSubset vbl P cand) :
    i ∈ cand ∧ P i = true := by
  induction cand with
  | nil => simp [greedyIndependentSubset] at hi
  | cons x xs ih =>
    simp only [greedyIndependentSubset] at hi
    split_ifs at hi with hcond
    · rw [Bool.and_eq_true] at hcond
      rcases List.mem_cons.1 hi with rfl | hxs
      · exact ⟨List.mem_cons_self, hcond.1⟩
      · exact ⟨List.mem_cons_of_mem _ (ih hxs).1, (ih hxs).2⟩
    · exact ⟨List.mem_cons_of_mem _ (ih hi).1, (ih hi).2⟩

private theorem greedyIndependentSubset_pairwise (vbl : ι → Finset V) (P : ι → Bool)
    (cand : List ι) :
    (greedyIndependentSubset vbl P cand).Pairwise fun i j => ¬Adj vbl i j := by
  induction cand with
  | nil => simp [greedyIndependentSubset]
  | cons x xs ih =>
    simp only [greedyIndependentSubset]
    split_ifs with hcond
    · rw [List.pairwise_cons]
      refine ⟨fun j hj => ?_, ih⟩
      rw [Bool.and_eq_true, List.all_eq_true] at hcond
      have hpair := hcond.2 j hj
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hpair
      rw [adj_iff]
      push Not
      exact hpair
    · exact ih

private theorem greedyIndependentSubset_max (vbl : ι → Finset V) (P : ι → Bool)
    (cand : List ι) {i : ι} (hic : i ∈ cand) (hiP : P i = true) :
    ∃ j ∈ greedyIndependentSubset vbl P cand, Adj vbl i j := by
  induction cand with
  | nil => simp at hic
  | cons x xs ih =>
    simp only [greedyIndependentSubset]
    rcases List.mem_cons.1 hic with rfl | hixs
    · split_ifs with hcond
      · exact ⟨i, List.mem_cons_self, adj_refl vbl i⟩
      · have hnot : ¬((P i &&
            (greedyIndependentSubset vbl P xs).all
              fun j => decide (i ≠ j) && decide (Disjoint (vbl i) (vbl j))) = true) := by
          simpa using hcond
        rw [Bool.and_eq_true, not_and, hiP] at hnot
        have hall : ¬(greedyIndependentSubset vbl P xs).all
            (fun j => decide (i ≠ j) && decide (Disjoint (vbl i) (vbl j))) = true :=
          hnot rfl
        rw [List.all_eq_true] at hall
        push Not at hall
        obtain ⟨j, hj, hnotadj⟩ := hall
        refine ⟨j, hj, ?_⟩
        by_contra hna
        have hna' := not_or.1 ((adj_iff vbl).not.1 hna)
        exact hnotadj ((Bool.and_eq_true _ _).mpr
          ⟨decide_eq_true_iff.2 hna'.1, decide_eq_true_iff.2 (not_not.1 hna'.2)⟩)
    · obtain ⟨j, hj, hadj⟩ := ih hixs
      split_ifs
      · exact ⟨j, List.mem_cons_of_mem _ hj, hadj⟩
      · exact ⟨j, hj, hadj⟩

/-- Computable greedy maximal independent set parallel selection rule over an explicit candidate
list `cand` and Boolean event detector `occur`. -/
@[expose] def greedyParallelList (vbl : ι → Finset V) (cand : List ι)
    (occur : (∀ v, α v) → ι → Bool) (T : ∀ p : V × ℕ, α p.1) (w : List ι) : List ι :=
  greedyIndependentSubset vbl (fun i => occur (current vbl T w) i) cand

theorem isValidParallelRule_greedyParallelList (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (cand : List ι) (hcand : ∀ i, i ∈ cand) (occur : (∀ v, α v) → ι → Bool)
    (hoccur : ∀ a i, occur a i = true ↔ a ∈ A i) :
    IsValidParallelRule vbl A (greedyParallelList vbl cand occur) where
  mem _ _ i hi := (hoccur _ i).1 (greedyIndependentSubset_mem vbl _ cand hi).2
  pairwise _ _ := greedyIndependentSubset_pairwise vbl _ cand
  max _ _ i hi := greedyIndependentSubset_max vbl _ cand (hcand i) ((hoccur _ i).2 hi)

/-- Noncomputable canonical greedy maximal independent set parallel selection rule for finite
event index types `ι`. -/
noncomputable def greedyParallel [Fintype ι] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (T : ∀ p : V × ℕ, α p.1) (w : List ι) : List ι :=
  open Classical in
  greedyParallelList vbl (Finset.univ : Finset ι).toList (fun a i => decide (a ∈ A i)) T w

theorem isValidParallelRule_greedyParallel [Fintype ι] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) :
    IsValidParallelRule vbl A (greedyParallel vbl A) := by
  classical
  exact isValidParallelRule_greedyParallelList vbl A (Finset.univ : Finset ι).toList
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i))
    (fun a i => decide (a ∈ A i)) (fun _ _ => decide_eq_true_iff)

end GreedyMIS

section WitnessDepth

variable {V ι : Type*} {α : V → Type*}

private def pushList (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (b : List ι) (S : Finset (ι × ℕ)) : Finset (ι × ℕ) :=
  b.foldl (fun S' j => pushRel R j S') S

private theorem subset_pushRel (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (j : ι) (S : Finset (ι × ℕ)) :
    S ⊆ pushRel R j S := by
  by_cases hj : levelRel R j S = 0
  · rw [pushRel_of_eq_zero hj]
  · rw [pushRel_of_ne_zero hj]
    exact subset_insert _ _

private theorem subset_pushList (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (b : List ι) (S : Finset (ι × ℕ)) :
    S ⊆ pushList R b S := by
  induction b generalizing S with
  | nil => exact Subset.rfl
  | cons j b ih =>
    exact (subset_pushRel R j S).trans (ih _)

private theorem pushList_append (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    (a b : List ι) (S : Finset (ι × ℕ)) :
    pushList R (a ++ b) S = pushList R b (pushList R a S) :=
  List.foldl_append

private theorem levelRel_pushRel_of_not_rel (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {x y : ι} (hxy : ¬R x y) (S : Finset (ι × ℕ)) :
    levelRel R y (pushRel R x S) = levelRel R y S := by
  by_cases hx : levelRel R x S = 0
  · rw [pushRel_of_eq_zero hx]
  · rw [pushRel_of_ne_zero hx, levelRel_insert_of_not_rel hxy]

private theorem mem_pushList_spec (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {b : List ι} (hpw : b.Pairwise fun x y => ¬R x y) (S : Finset (ι × ℕ)) :
    (∀ p ∈ pushList R b S,
        p ∈ S ∨ ∃ j ∈ b, levelRel R j S ≠ 0 ∧ p = (j, levelRel R j S)) ∧
      (∀ j ∈ b, levelRel R j S ≠ 0 → (j, levelRel R j S) ∈ pushList R b S) := by
  induction b generalizing S with
  | nil => simp [pushList]
  | cons x b ih =>
    rw [List.pairwise_cons] at hpw
    have hnot : ∀ y ∈ b, ¬R x y := hpw.1
    have ih' := ih hpw.2 (pushRel R x S)
    have hlev : ∀ y ∈ b, levelRel R y (pushRel R x S) = levelRel R y S := fun y hy =>
      levelRel_pushRel_of_not_rel R (hnot y hy) S
    constructor
    · intro p hp
      change p ∈ pushList R b (pushRel R x S) at hp
      rcases ih'.1 p hp with hp1 | ⟨j, hjb, hne, rfl⟩
      · by_cases hx : levelRel R x S = 0
        · rw [pushRel_of_eq_zero hx] at hp1
          exact Or.inl hp1
        · rw [pushRel_of_ne_zero hx] at hp1
          rcases mem_insert.1 hp1 with rfl | hpS
          · exact Or.inr ⟨x, List.mem_cons_self, hx, rfl⟩
          · exact Or.inl hpS
      · rw [hlev j hjb] at hne ⊢
        exact Or.inr ⟨j, List.mem_cons_of_mem _ hjb, hne, rfl⟩
    · intro j hj hne
      change (j, levelRel R j S) ∈ pushList R b (pushRel R x S)
      rcases List.mem_cons.1 hj with rfl | hjb
      · exact subset_pushList R b (pushRel R j S) (by
          rw [pushRel_of_ne_zero hne]
          exact mem_insert_self _ _)
      · have hlevj := hlev j hjb
        rw [← hlevj] at hne ⊢
        exact ih'.2 j hjb hne

private theorem witnessRel_prefix_eq_singleton (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {i : ι} {suff : List ι} (hsuff : ∀ j ∈ suff, ¬R i j) :
    witnessRel R i suff = {(i, 0)} := by
  induction suff with
  | nil => exact witnessRel_nil R i
  | cons j suff ih =>
    rw [witnessRel_cons_of_not_rel R (hsuff j List.mem_cons_self)]
    exact ih fun x hx => hsuff x (List.mem_cons_of_mem _ hx)

private theorem witnessRel_append_eq_pushList (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]
    {i : ι} {suff : List ι} (hsuff : ∀ j ∈ suff, ¬R i j) (w : List ι) :
    witnessRel R i (suff ++ w) = pushList R w {(i, 0)} := by
  induction w using List.reverseRecOn with
  | nil =>
    rw [List.append_nil, pushList, List.foldl_nil, witnessRel_prefix_eq_singleton R hsuff]
  | append_singleton w j ih =>
    rw [← List.append_assoc, witnessRel_append_singleton, ih, pushList_append]
    simp [pushList]

private theorem parallel_step_adj [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) (m : ℕ)
    {i : ι} (hi : i ∈ psel T (parallelRun psel T (m + 1))) :
    ∃ j ∈ psel T (parallelRun psel T m), Adj vbl i j := by
  have hi_occ : current vbl T (parallelRun psel T (m + 1)) ∈ A i :=
    hrule.mem T (parallelRun psel T (m + 1)) i hi
  by_cases hm_occ : current vbl T (parallelRun psel T m) ∈ A i
  · exact hrule.max T (parallelRun psel T m) i hm_occ
  · have hdiff : ¬∀ v ∈ vbl i,
        current vbl T (parallelRun psel T (m + 1)) v =
          current vbl T (parallelRun psel T m) v := by
      intro heq
      exact hm_occ ((hA i heq).mp hi_occ)
    push Not at hdiff
    obtain ⟨v, hv, hne⟩ := hdiff
    have huses :
        uses vbl (psel T (parallelRun psel T m) ++ parallelRun psel T m) v ≠
          uses vbl (parallelRun psel T m) v := by
      intro hu
      apply hne
      rw [parallelRun_succ, current_apply, current_apply, hu]
    by_contra hdisj
    push Not at hdisj
    apply huses
    refine uses_append_eq_of_forall_notMem vbl _ _ fun j hj hvj => ?_
    exact (hdisj j hj) (adj_of_mem vbl hv hvj)

private def batchSlice (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι)
    (T : ∀ p : V × ℕ, α p.1) (r : ℕ) : ℕ → List ι
  | 0 => []
  | d + 1 => psel T (parallelRun psel T (r + d)) ++ batchSlice psel T r d

private theorem batchSlice_zero_eq_parallelRun
    (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι) (T : ∀ p : V × ℕ, α p.1) (k : ℕ) :
    batchSlice psel T 0 k = parallelRun psel T k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [batchSlice, zero_add, ih, parallelRun_succ]

private theorem batchSlice_succ_right
    (psel : (∀ p : V × ℕ, α p.1) → List ι → List ι) (T : ∀ p : V × ℕ, α p.1) (r d : ℕ) :
    batchSlice psel T r (d + 1) =
      batchSlice psel T (r + 1) d ++ psel T (parallelRun psel T r) := by
  induction d generalizing r with
  | zero => simp [batchSlice]
  | succ d ih =>
    have hidx : r + (d + 1) = (r + 1) + d := by omega
    rw [batchSlice, hidx, ih r, ← List.append_assoc]
    rfl

private theorem pushList_batchSlice_depth [DecidableEq V] [DecidableEq ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) :
    ∀ (d r t : ℕ) (S : Finset (ι × ℕ)),
      (∀ p ∈ S, p.2 ≤ t) →
      (∃ p ∈ S, p.2 = t ∧ p.1 ∈ psel T (parallelRun psel T (r + d))) →
      (∀ p ∈ pushList (Adj vbl) (batchSlice psel T r d) S, p.2 ≤ t + d) ∧
        (∃ p ∈ pushList (Adj vbl) (batchSlice psel T r d) S,
          p.2 = t + d ∧ p.1 ∈ psel T (parallelRun psel T r)) := by
  intro d
  induction d with
  | zero =>
    intro r t S hle hex
    exact ⟨hle, hex⟩
  | succ d ih =>
    intro r t S hle hex
    rw [batchSlice_succ_right, pushList_append]
    have hidx : r + (d + 1) = (r + 1) + d := by omega
    rw [hidx] at hex
    obtain ⟨hle', ⟨p, hpS', hpt, hp_in⟩⟩ := ih (r + 1) t S hle hex
    obtain ⟨j, hj, hadj⟩ := parallel_step_adj vbl A hA hrule T r hp_in
    have hspec := mem_pushList_spec (Adj vbl) (hrule.pairwise T (parallelRun psel T r))
      (pushList (Adj vbl) (batchSlice psel T (r + 1) d) S)
    have hj_bound : ∀ x ∈ psel T (parallelRun psel T r),
        levelRel (Adj vbl) x (pushList (Adj vbl) (batchSlice psel T (r + 1) d) S) ≤ t + d + 1 := by
      intro x _
      rcases Nat.eq_zero_or_pos
          (levelRel (Adj vbl) x (pushList (Adj vbl) (batchSlice psel T (r + 1) d) S)) with
        hl0 | hlpos
      · omega
      · obtain ⟨q, hq, hql, -⟩ := exists_of_levelRel_ne_zero hlpos.ne'
        have := hle' q hq
        omega
    have hlt :
        t + d < levelRel (Adj vbl) j (pushList (Adj vbl) (batchSlice psel T (r + 1) d) S) := by
      rw [← hpt]
      exact lt_levelRel hpS' hadj
    have hjeq : levelRel (Adj vbl) j (pushList (Adj vbl) (batchSlice psel T (r + 1) d) S) =
        t + d + 1 :=
      le_antisymm (hj_bound j hj) hlt
    constructor
    · intro q hq
      rcases hspec.1 q hq with hq' | ⟨x, hx, -, rfl⟩
      · exact (hle' q hq').trans (by omega)
      · exact (hj_bound x hx).trans (by omega)
    · refine ⟨(j, t + (d + 1)), ?_, rfl, hj⟩
      have hne : levelRel (Adj vbl) j (pushList (Adj vbl) (batchSlice psel T (r + 1) d) S) ≠ 0 := by
        omega
      have hmem := hspec.2 j hj hne
      rwa [hjeq] at hmem

/-- **Parallel witness-tree depth lemma** [MoserTardos2010, Lemma 4.1]: if round `k` selects a
non-empty batch containing `i` (with suffix `suff` after `i` in that batch), then the witness
structure `witness vbl i (suff ++ parallelRun psel T k)` lies in `shapes vbl i k`, is proper,
passes its check on `T`, and contains a vertex at depth `k` (hence has cardinality `≥ k + 1`). -/
theorem parallel_witness_depth [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) (k : ℕ)
    {i : ι} {pref suff : List ι}
    (hsplit : psel T (parallelRun psel T k) = pref ++ i :: suff) :
    let S := witness vbl i (suff ++ parallelRun psel T k)
    S ∈ shapes vbl i k ∧ Proper vbl S ∧ Check vbl A S T ∧ (∃ p ∈ S, p.2 = k) ∧ k + 1 ≤ #S := by
  intro S
  have hpw : (psel T (parallelRun psel T k)).Pairwise fun x y => ¬Adj vbl x y :=
    hrule.pairwise T (parallelRun psel T k)
  rw [hsplit, List.pairwise_append] at hpw
  have hi_suff : ∀ j ∈ suff, ¬Adj vbl i j := (List.pairwise_cons.1 hpw.2.1).1
  have hS_eq : S = pushList (Adj vbl) (batchSlice psel T 0 k) {(i, 0)} := by
    change witness vbl i (suff ++ parallelRun psel T k) = _
    rw [witness_eq_witnessRel, witnessRel_append_eq_pushList (Adj vbl) hi_suff,
      batchSlice_zero_eq_parallelRun]
  have hdepth := pushList_batchSlice_depth vbl A hA hrule T k 0 0 {(i, 0)}
    (fun p hp => by simp [mem_singleton.1 hp])
    ⟨(i, 0), mem_singleton_self _, rfl, by rw [zero_add, hsplit]; simp⟩
  rw [zero_add, ← hS_eq] at hdepth
  have hroot : RootedRel (Adj vbl) i S := by
    change RootedRel (Adj vbl) i (witness vbl i (suff ++ parallelRun psel T k))
    rw [witness_eq_witnessRel]
    exact rooted_witnessRel (Adj vbl) i _
  have hshape : S ∈ shapes vbl i k := by
    rw [shapes_eq_shapesRel]
    exact mem_shapesRel (Adj vbl) k hroot hdepth.1
  have hprop : Proper vbl S := proper_witness vbl i _
  have hlog_sub : IsLog vbl A T ((i :: suff) ++ parallelRun psel T k) := by
    refine isLog_append_of_pairwise vbl A hA T
      (isLog_parallelRun vbl A hA hrule T k) (fun x hx => ?_) hpw.2.1
    refine hrule.mem T (parallelRun psel T k) x ?_
    rw [hsplit]
    exact List.mem_append_right _ hx
  have hchk : Check vbl A S T := check_witness vbl A hA i _ T (by simpa using hlog_sub)
  have hdepth_k : ∃ p ∈ S, p.2 = k := by
    obtain ⟨p, hp, hpk, -⟩ := hdepth.2
    exact ⟨p, hp, hpk⟩
  have hcard : k + 1 ≤ #S := by
    have hlevels : ∀ d ≤ k, ∃ p ∈ S, p.2 = d := by
      intro d hd
      have hdesc : ∀ t : ℕ, (∃ q ∈ S, q.2 = t) → ∀ d ≤ t, ∃ q ∈ S, q.2 = d := by
        intro t
        induction t with
        | zero =>
          intro hq d hd0
          obtain rfl : d = 0 := Nat.le_zero.1 hd0
          exact hq
        | succ t iht =>
          intro ⟨q, hqS, hqt⟩ d hdt
          rcases Nat.eq_or_lt_of_le hdt with rfl | hlt
          · exact ⟨q, hqS, hqt⟩
          · obtain ⟨r, hrS, hrt, -⟩ := hroot.parent q hqS (by omega)
            exact iht ⟨r, hrS, by omega⟩ d (Nat.lt_succ_iff.1 hlt)
      exact hdesc k hdepth_k d hd
    have hsub : Finset.range (k + 1) ⊆ S.image Prod.snd := by
      intro d hd
      rw [mem_range, Nat.lt_succ_iff] at hd
      obtain ⟨p, hpS, rfl⟩ := hlevels d hd
      exact mem_image_of_mem Prod.snd hpS
    calc k + 1 = #(Finset.range (k + 1)) := (card_range (k + 1)).symm
      _ ≤ #(S.image Prod.snd) := card_le_card hsub
      _ ≤ #S := card_image_le
  exact ⟨hshape, hprop, hchk, hdepth_k, hcard⟩

end WitnessDepth

section Expectation

variable {V ι : Type*} {α : V → Type*} [∀ v, MeasurableSpace (α v)]

private def parallelEvent [DecidableEq V] [DecidableEq ι] [Fintype ι] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (k : ℕ) : Set (∀ p : V × ℕ, α p.1) :=
  {T | ∃ i : ι, ∃ S ∈ shapes vbl i k, Proper vbl S ∧ k + 1 ≤ #S ∧ Check vbl A S T}

private theorem measurableSet_parallelEvent [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    MeasurableSet (parallelEvent vbl A k) := by
  have heq : parallelEvent vbl A k =
      ⋃ i : ι, ⋃ S ∈ shapes vbl i k, ⋃ (_ : Proper vbl S), ⋃ (_ : k + 1 ≤ #S),
        {T | Check vbl A S T} := by
    ext T
    simp only [parallelEvent, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  rw [heq]
  refine MeasurableSet.iUnion fun i => MeasurableSet.biUnion (shapes vbl i k).countable_toSet
    fun S _ => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => ?_
  exact measurableSet_check vbl A hAm S

omit [∀ v, MeasurableSpace (α v)] in
private theorem mem_parallelEvent_of_psel_ne_nil [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) {T : ∀ p : V × ℕ, α p.1} {k : ℕ}
    (hne : psel T (parallelRun psel T k) ≠ []) :
    T ∈ parallelEvent vbl A k := by
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨pref, suff, hsplit⟩ := List.append_of_mem hi
  obtain ⟨hshape, hprop, hchk, -, hcard⟩ := parallel_witness_depth vbl A hA hrule T k hsplit
  exact ⟨i, witness vbl i (suff ++ parallelRun psel T k), hshape, hprop, hcard, hchk⟩

private theorem table_parallelEvent_le [Fintype V] [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    (k : ℕ) :
    table μ (parallelEvent vbl A k) ≤
      ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i)) := by
  classical
  have h1e0 : 0 ≤ 1 - ε := sub_nonneg.2 hε.2
  have h1e1 : 1 - ε ≤ 1 := by linarith [hε.1]
  have hy0 : ∀ i, 0 ≤ x i * ∏ j ∈ Γ i, (1 - x j) := fun i =>
    mul_nonneg (hx i).1 (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hx j).2.le)
  have hsub : parallelEvent vbl A k ⊆
      ⋃ i : ι, ⋃ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
        {T | Check vbl A S T} := by
    intro T ⟨i, S, hS, hprop, hcard, hchk⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_biUnion (mem_filter.2 ⟨hS, hprop, hcard⟩) hchk⟩
  calc table μ (parallelEvent vbl A k)
      ≤ table μ (⋃ i : ι,
          ⋃ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
            {T | Check vbl A S T}) := measure_mono hsub
    _ ≤ ∑ i : ι, table μ
          (⋃ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
            {T | Check vbl A S T}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : ι, ∑ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
          table μ {T | Check vbl A S T} :=
        Finset.sum_le_sum fun i _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ i : ι, ∑ S ∈ shapes vbl i k,
          ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ∑ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
              table μ {T | Check vbl A S T}
            ≤ ∑ S ∈ (shapes vbl i k).filter (fun S => Proper vbl S ∧ k + 1 ≤ #S),
                ENNReal.ofReal
                  ((1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) := by
              refine Finset.sum_le_sum fun S hS => ?_
              obtain ⟨-, hprop, hcard⟩ := mem_filter.1 hS
              rw [measure_check_eq_prod μ vbl A hAm hA hprop]
              have hprod : ∏ p ∈ S, Measure.pi μ (A p.1) =
                  ENNReal.ofReal (∏ p ∈ S, (Measure.pi μ).real (A p.1)) := by
                rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => measureReal_nonneg]
                refine Finset.prod_congr rfl fun p _ => ?_
                rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
              rw [hprod]
              refine ENNReal.ofReal_le_ofReal ?_
              calc ∏ p ∈ S, (Measure.pi μ).real (A p.1)
                  ≤ ∏ p ∈ S, ((1 - ε) * (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) :=
                    Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) fun p _ => hP p.1
                _ = (1 - ε) ^ #S * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j)) := by
                    rw [Finset.prod_mul_distrib, Finset.prod_const]
                _ ≤ (1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j)) :=
                    mul_le_mul_of_nonneg_right
                      (pow_le_pow_of_le_one h1e0 h1e1 hcard)
                      (Finset.prod_nonneg fun p _ => hy0 p.1)
          _ ≤ ∑ S ∈ shapes vbl i k,
                ENNReal.ofReal
                  ((1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) :=
              Finset.sum_le_sum_of_subset (filter_subset _ _)
    _ = ENNReal.ofReal
          (∑ i : ι, ∑ S ∈ shapes vbl i k,
            (1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) := by
        have hinner : ∀ i : ι,
            ∑ S ∈ shapes vbl i k,
              ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) =
              ENNReal.ofReal (∑ S ∈ shapes vbl i k,
                (1 - ε) ^ (k + 1) * ∏ p ∈ S, (x p.1 * ∏ j ∈ Γ p.1, (1 - x j))) := fun i => by
          rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ =>
            mul_nonneg (pow_nonneg h1e0 _) (Finset.prod_nonneg fun _ _ => hy0 _)]
        simp_rw [hinner]
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ =>
            mul_nonneg (pow_nonneg h1e0 _) (Finset.prod_nonneg fun _ _ => hy0 _)]
    _ ≤ ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp_rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (pow_nonneg h1e0 _)
        exact sum_prod_shapes_le vbl Γ hΓ hx hy0 (fun _ => le_rfl) i k

/-- **Parallel Moser–Tardos tail bound** ([MoserTardos2010, Section 4]): under
`Pr[A i] ≤ (1 - ε) * x i * ∏ j ∈ Γ i, (1 - x j)` with `ε ∈ (0, 1]`, for every admissible
parallel selection rule `psel`, the probability that the algorithm performs at least `k + 1`
parallel rounds is at most `(1 - ε) ^ (k + 1) * ∑ i, x i / (1 - x i)`. -/
theorem table_succ_le_parallelRounds_le [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (k : ℕ) :
    table μ {T | (k : ℝ≥0∞) + 1 ≤ parallelRounds psel T} ≤
      ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i)) := by
  classical
  refine (measure_mono fun T hT => ?_).trans
    (table_parallelEvent_le μ vbl A hAm hA Γ hΓ hx hε hP k)
  exact mem_parallelEvent_of_psel_ne_nil vbl A hA hrule
    ((succ_le_parallelRounds_iff psel T k).1 hT)

private theorem tsum_min_one_split_bound {ε M : ℝ} (hr0 : 0 ≤ 1 - ε)
    (hr1 : 1 - ε < 1) (N : ℕ) (hrN : (1 - ε) ^ (N + 1) * M ≤ 1) :
    (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M))) ≤
      (N : ℝ≥0∞) + ENNReal.ofReal (1 / ε) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  by_cases hn : n ≤ N
  · calc ∑ _k ∈ Finset.range n, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (_k + 1) * M))
        ≤ ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ => min_le_left _ _
      _ = (n : ℝ≥0∞) := by simp
      _ ≤ (N : ℝ≥0∞) := Nat.cast_le.mpr hn
      _ ≤ (N : ℝ≥0∞) + ENNReal.ofReal (1 / ε) := le_self_add
  · have hNn : N ≤ n := Nat.le_of_not_le hn
    rw [← Nat.add_sub_cancel' hNn, Finset.sum_range_add]
    refine add_le_add ?_ ?_
    · calc ∑ _k ∈ Finset.range N, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (_k + 1) * M))
          ≤ ∑ _k ∈ Finset.range N, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ => min_le_left _ _
        _ = (N : ℝ≥0∞) := by simp
    · have htail : ∀ m : ℕ,
          min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (N + m + 1) * M)) ≤
            ENNReal.ofReal ((1 - ε) ^ m) := fun m => by
        refine (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal ?_)
        calc (1 - ε) ^ (N + m + 1) * M
            = ((1 - ε) ^ (N + 1) * M) * (1 - ε) ^ m := by
              rw [show N + m + 1 = (N + 1) + m by omega, pow_add]; ring
          _ ≤ 1 * (1 - ε) ^ m := mul_le_mul_of_nonneg_right hrN (pow_nonneg hr0 _)
          _ = (1 - ε) ^ m := one_mul _
      calc ∑ m ∈ Finset.range (n - N),
              min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (N + m + 1) * M))
          ≤ ∑ m ∈ Finset.range (n - N), ENNReal.ofReal ((1 - ε) ^ m) :=
            Finset.sum_le_sum fun m _ => htail m
        _ = ENNReal.ofReal (∑ m ∈ Finset.range (n - N), (1 - ε) ^ m) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun m _ => pow_nonneg hr0 m]
        _ ≤ ENNReal.ofReal (∑' m : ℕ, (1 - ε) ^ m) :=
            ENNReal.ofReal_le_ofReal ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
              (Finset.range (n - N)) fun m _ => pow_nonneg hr0 m)
        _ = ENNReal.ofReal (1 / ε) := by
            rw [tsum_geometric_of_lt_one hr0 hr1, show 1 - (1 - ε) = ε by ring, one_div]

private theorem tsum_min_one_ofReal_pow_mul_le {ε M : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hM : 0 ≤ M) :
    (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M))) ≤
      ENNReal.ofReal ((max 0 (Real.log M) + 1) / ε) := by
  have h1e0 : 0 ≤ 1 - ε := sub_nonneg.2 hε.2
  rcases eq_or_lt_of_le hε.2 with rfl | hε_lt
  · simp
  · have hr_pos : 0 < 1 - ε := sub_pos.2 hε_lt
    have hr_lt : 1 - ε < 1 := sub_lt_self _ hε.1
    rcases le_or_gt M 1 with hM1 | hM1
    · have hlog_le : Real.log M ≤ 0 := by
        rcases eq_or_lt_of_le hM with rfl | hMpos
        · simp
        · exact Real.log_nonpos hMpos.le hM1
      have hmax : max 0 (Real.log M) = 0 := max_eq_left hlog_le
      rw [hmax, zero_add]
      have hterm : ∀ k : ℕ,
          min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M)) ≤
            ENNReal.ofReal ((1 - ε) ^ (k + 1)) := fun k => by
        refine min_le_of_right_le (ENNReal.ofReal_le_ofReal ?_)
        exact mul_le_of_le_one_right (pow_nonneg h1e0 _) hM1
      calc (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M)))
          ≤ ∑' k : ℕ, ENNReal.ofReal ((1 - ε) ^ (k + 1)) := tsum_le_tsum hterm
        _ = ENNReal.ofReal (∑' k : ℕ, (1 - ε) ^ (k + 1)) := by
            symm
            exact ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg h1e0 _)
              ((summable_geometric_of_lt_one h1e0 hr_lt).comp_injective Nat.succ_injective)
        _ ≤ ENNReal.ofReal (1 / ε) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hgeom : (∑' k : ℕ, (1 - ε) ^ (k + 1)) = (1 - ε) / ε := by
              have hmul : (∑' k : ℕ, (1 - ε) ^ (k + 1)) = (1 - ε) * ∑' k : ℕ, (1 - ε) ^ k := by
                simp_rw [pow_succ']
                exact tsum_mul_left
              rw [hmul, tsum_geometric_of_lt_one h1e0 hr_lt]
              have hsub : 1 - (1 - ε) = ε := by ring
              rw [hsub, ← div_eq_mul_inv]
            rw [hgeom]
            exact div_le_div_of_nonneg_right (by linarith [hε.1]) hε.1.le
    · have hMpos : 0 < M := lt_trans zero_lt_one hM1
      have hlog_pos : 0 < Real.log M := Real.log_pos hM1
      have hmax : max 0 (Real.log M) = Real.log M := max_eq_right hlog_pos.le
      rw [hmax]
      let a := -Real.log (1 - ε)
      have ha_ge : ε ≤ a := by
        have := Real.log_le_sub_one_of_pos hr_pos
        linarith
      have ha_pos : 0 < a := hε.1.trans_le ha_ge
      obtain ⟨N, hN_le_a, hN_lt⟩ :
          ∃ N : ℕ, (N : ℝ) ≤ Real.log M / a ∧ Real.log M / a < (N : ℝ) + 1 :=
        ⟨Nat.floor (Real.log M / a), Nat.floor_le (div_nonneg hlog_pos.le ha_pos.le),
          Nat.lt_floor_add_one _⟩
      have hN_le : (N : ℝ) ≤ Real.log M / ε :=
        hN_le_a.trans (div_le_div_of_nonneg_left hlog_pos.le hε.1 ha_ge)
      have hrN_le : (1 - ε) ^ (N + 1) * M ≤ 1 := by
        have hlt_mul : Real.log M < ((N : ℝ) + 1) * a := (div_lt_iff₀ ha_pos).1 hN_lt
        have hlog_prod : Real.log ((1 - ε) ^ (N + 1) * M) < 0 := by
          rw [Real.log_mul (pow_pos hr_pos _).ne' hMpos.ne', Real.log_pow]
          have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          linarith
        exact (Real.log_neg_iff (mul_pos (pow_pos hr_pos _) hMpos)).1 hlog_prod |>.le
      calc (∑' k : ℕ, min (1 : ℝ≥0∞) (ENNReal.ofReal ((1 - ε) ^ (k + 1) * M)))
          ≤ (N : ℝ≥0∞) + ENNReal.ofReal (1 / ε) :=
            tsum_min_one_split_bound h1e0 hr_lt N hrN_le
        _ = ENNReal.ofReal (N : ℝ) + ENNReal.ofReal (1 / ε) := by simp
        _ ≤ ENNReal.ofReal (Real.log M / ε) + ENNReal.ofReal (1 / ε) :=
            add_le_add (ENNReal.ofReal_le_ofReal hN_le) le_rfl
        _ = ENNReal.ofReal ((Real.log M + 1) / ε) := by
            rw [← ENNReal.ofReal_add (div_nonneg hlog_pos.le hε.1.le)
              (div_nonneg zero_le_one hε.1.le), ← add_div]

private noncomputable def parallelEventSum [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1) : ℝ≥0∞ :=
  ∑' k : ℕ, (parallelEvent vbl A k).indicator (fun _ => (1 : ℝ≥0∞)) T

private theorem measurable_parallelEventSum [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) :
    Measurable (parallelEventSum vbl A) :=
  Measurable.tsum fun k =>
    measurable_const.indicator (measurableSet_parallelEvent vbl A hAm k)

omit [∀ v, MeasurableSpace (α v)] in
private theorem parallelRounds_le_parallelEventSum [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) (T : ∀ p : V × ℕ, α p.1) :
    parallelRounds psel T ≤ parallelEventSum vbl A T := by
  rw [parallelRounds_eq_tsum, parallelEventSum]
  refine tsum_le_tsum fun k => ?_
  split_ifs with hne
  · rw [Set.indicator_of_mem (mem_parallelEvent_of_psel_ne_nil vbl A hA hrule hne)]
  · exact zero_le

private theorem lintegral_parallelEventSum_eq [DecidableEq V] [DecidableEq ι]
    [Fintype ι] (μ : ∀ v, Measure (α v))
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i)) :
    ∫⁻ T, parallelEventSum vbl A T ∂table μ = ∑' k : ℕ, table μ (parallelEvent vbl A k) := by
  unfold parallelEventSum
  rw [lintegral_tsum fun k =>
    (measurable_const.indicator (measurableSet_parallelEvent vbl A hAm k)).aemeasurable]
  refine tsum_congr fun k => ?_
  rw [lintegral_indicator (measurableSet_parallelEvent vbl A hAm k), setLIntegral_one]

private theorem lintegral_parallelEventSum_le [Fintype V] [DecidableEq V] [DecidableEq ι]
    [Fintype ι] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j))) :
    ∫⁻ T, parallelEventSum vbl A T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) := by
  rw [lintegral_parallelEventSum_eq μ vbl A hAm]
  have htail : ∑' k : ℕ, table μ (parallelEvent vbl A k) ≤
      ∑' k : ℕ, min (1 : ℝ≥0∞)
        (ENNReal.ofReal ((1 - ε) ^ (k + 1) * ∑ i : ι, x i / (1 - x i))) := by
    refine tsum_le_tsum fun k => le_min ?_ ?_
    · exact (measure_mono (Set.subset_univ _)).trans (by simp)
    · exact table_parallelEvent_le μ vbl A hAm hA Γ hΓ hx hε hP k
  have hM0 : 0 ≤ ∑ i : ι, x i / (1 - x i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (hx i).1 (sub_pos.2 (hx i).2).le
  exact htail.trans (tsum_min_one_ofReal_pow_mul_le hε hM0)

/-- **Parallel Moser–Tardos theorem** [MoserTardos2010, Theorem 1.3]: under
`Pr[A i] ≤ (1 - ε) * x i * ∏ j ∈ Γ i, (1 - x j)` with `ε ∈ (0, 1]`, any admissible parallel
selection rule terminates in at most `(max 0 (Real.log (∑ i, x i / (1 - x i))) + 1) / ε`
expected parallel rounds.

The rule is not assumed measurable, so `∫⁻` is the lower Lebesgue integral. As in the sequential
theorem, `exists_measurable_ge_parallelRounds` dominates `parallelRounds psel` for every valid
parallel rule by a single measurable function of the table with the same expected bound. -/
theorem lintegral_parallelRounds_le [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) := by
  classical
  exact (lintegral_mono (parallelRounds_le_parallelEventSum vbl A hA hrule)).trans
    (lintegral_parallelEventSum_le μ vbl A hAm hA Γ hΓ hx hε hP)

/-- **Theorem 1.3 for the outer expectation** [MoserTardos2010]: under the slack local-lemma
hypothesis there is a measurable function `g` of the table, with
`∫⁻ g ≤ (max 0 (Real.log (∑ i, x i / (1 - x i))) + 1) / ε`, that bounds `parallelRounds psel`
for every valid parallel selection rule `psel`. So the bound holds for the upper (outer)
expectation of the number of rounds as well, whether or not the rule is measurable. -/
theorem exists_measurable_ge_parallelRounds [Fintype V] [DecidableEq V] [Fintype ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j))) :
    ∃ g : (∀ p : V × ℕ, α p.1) → ℝ≥0∞, Measurable g ∧
      ∫⁻ T, g T ∂table μ ≤
        ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) ∧
      ∀ psel : (∀ p : V × ℕ, α p.1) → List ι → List ι,
        IsValidParallelRule vbl A psel → ∀ T, parallelRounds psel T ≤ g T := by
  classical
  exact ⟨parallelEventSum vbl A, measurable_parallelEventSum vbl A hAm,
    lintegral_parallelEventSum_le μ vbl A hAm hA Γ hΓ hx hε hP,
    fun _ hrule T => parallelRounds_le_parallelEventSum vbl A hA hrule T⟩

/-- When `ε = 1` (so every bad event has probability zero), every valid parallel rule performs
`0` expected rounds. -/
theorem lintegral_parallelRounds_eq_zero_of_one [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ 0)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  have hev0 : ∀ k, table μ (parallelEvent vbl A k) = 0 := fun k => by
    have h1 : ∀ i, (Measure.pi μ).real (A i) ≤
        (1 - (1 : ℝ)) * (x i * ∏ j ∈ Γ i, (1 - x j)) := by
      simpa using hP
    simpa using table_parallelEvent_le μ vbl A hAm hA Γ hΓ hx ⟨zero_lt_one, le_rfl⟩ h1 k
  refine le_antisymm ?_ zero_le
  calc ∫⁻ T, parallelRounds psel T ∂table μ
      ≤ ∫⁻ T, parallelEventSum vbl A T ∂table μ :=
        lintegral_mono (parallelRounds_le_parallelEventSum vbl A hA hrule)
    _ = ∑' k : ℕ, table μ (parallelEvent vbl A k) := lintegral_parallelEventSum_eq μ vbl A hAm
    _ = 0 := by simp [hev0]

/-- The expected number of parallel rounds is finite under the slack LLL condition. -/
theorem lintegral_parallelRounds_ne_top [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≠ ⊤ := by
  let _ := Fintype.ofFinite ι
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_parallelRounds_le μ vbl A hAm hA Γ hΓ hx hε hP hrule)

/-- Under the slack LLL condition, `parallelRounds psel T < ⊤` almost surely for every valid
parallel rule `psel`. -/
theorem ae_parallelRounds_ne_top [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, parallelRounds psel T ≠ ⊤ := by
  classical
  let _ := Fintype.ofFinite ι
  have hae : ∀ᵐ T ∂table μ, parallelEventSum vbl A T < ⊤ :=
    ae_lt_top (measurable_parallelEventSum vbl A hAm)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (lintegral_parallelEventSum_le μ vbl A hAm hA Γ hΓ hx hε hP))
  refine hae.mono fun T hT => ?_
  exact (lt_of_le_of_lt (parallelRounds_le_parallelEventSum vbl A hA hrule T) hT).ne

/-- Almost surely under the slack LLL condition, every admissible parallel rule reaches an empty
batch in finitely many rounds. -/
theorem ae_exists_parallelRun_eq_nil [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, psel T (parallelRun psel T n) = [] :=
  (ae_parallelRounds_ne_top μ vbl A hAm hA Γ hΓ hx hε hP hrule).mono
    fun _ h => exists_eq_nil_of_parallelRounds_ne_top psel h

/-- Almost surely under the slack LLL condition, every admissible parallel rule reaches an
assignment avoiding all bad events in finitely many parallel rounds. -/
theorem ae_exists_forall_notMem_parallelRun [Fintype V] [DecidableEq V] [Finite ι]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i :=
  (ae_exists_parallelRun_eq_nil μ vbl A hAm hA Γ hΓ hx hε hP hrule).mono
    fun T ⟨n, hn⟩ => ⟨n, (hrule.eq_nil_iff T _).1 hn⟩

/-- Canonical greedy specialization: `greedyParallel` terminates almost surely at an assignment
avoiding all bad events. -/
theorem ae_exists_forall_notMem_parallelRun_greedy [Fintype V] [DecidableEq V]
    [DecidableEq ι] [Fintype ι] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j))) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, ∀ i, current vbl T (parallelRun (greedyParallel vbl A) T n) ∉ A i :=
  ae_exists_forall_notMem_parallelRun μ vbl A hAm hA Γ hΓ hx hε hP
    (isValidParallelRule_greedyParallel vbl A)

end Expectation

section SymmetricAndPMF

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι] [Fintype ι]
  {α : V → Type*} [∀ v, MeasurableSpace (α v)]

private theorem ofReal_max_log_mono {a b ε : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hε : 0 < ε) :
    ENNReal.ofReal ((max 0 (Real.log a) + 1) / ε) ≤
      ENNReal.ofReal ((max 0 (Real.log b) + 1) / ε) := by
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hε.le)
  refine add_le_add ?_ le_rfl
  rcases eq_or_lt_of_le ha with rfl | hapos
  · simp
  · exact max_le_max_left 0 (Real.log_le_log hapos hab)

/-- Symmetric parallel Moser–Tardos theorem (`1 ≤ d`): under `e * q * (d + 1) ≤ 1 - ε` with
`ε ∈ (0, 1]`, any admissible parallel selection rule terminates in at most
`(max 0 (Real.log (card ι / d)) + 1) / ε` expected parallel rounds. -/
theorem lintegral_parallelRounds_le_symmetric_of_pos [Fintype V]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q) (hε : ε ∈ Set.Ioc 0 1)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log ((Fintype.card ι : ℝ) / d)) + 1) / ε) := by
  obtain ⟨Γ, x, hΓ, hx, hP, hsum, -⟩ := exists_slack_weights_of_symmetric vbl hd
    (fun _ => measureReal_nonneg) hq hε hlll
  have hM0 : 0 ≤ ∑ i : ι, x i / (1 - x i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (hx i).1 (sub_pos.2 (hx i).2).le
  exact (lintegral_parallelRounds_le μ vbl A hAm hA Γ hΓ hx hε hP hrule).trans
    (ofReal_max_log_mono hM0 (hsum hdpos) hε.1)

/-- Symmetric parallel Moser–Tardos theorem (all `d : ℕ`): under `e * q * (d + 1) ≤ 1 - ε`
with `ε ∈ (0, 1]`, any admissible parallel selection rule terminates in at most
`(max 0 (Real.log (card ι)) + 1) / ε` expected parallel rounds. -/
theorem lintegral_parallelRounds_le_symmetric [Fintype V]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q) (hε : ε ∈ Set.Ioc 0 1)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table μ ≤
      ENNReal.ofReal ((max 0 (Real.log (Fintype.card ι : ℝ)) + 1) / ε) := by
  obtain ⟨Γ, x, hΓ, hx, hP, -, hsum⟩ := exists_slack_weights_of_symmetric vbl hd
    (fun _ => measureReal_nonneg) hq hε hlll
  have hM0 : 0 ≤ ∑ i : ι, x i / (1 - x i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (hx i).1 (sub_pos.2 (hx i).2).le
  exact (lintegral_parallelRounds_le μ vbl A hAm hA Γ hΓ hx hε hP hrule).trans
    (ofReal_max_log_mono hM0 hsum hε.1)

/-- Almost sure termination and avoidance under the symmetric slack LLL hypothesis
`e * q * (d + 1) ≤ 1 - ε`. -/
theorem ae_exists_forall_notMem_parallelRun_symmetric [Fintype V]
    (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q) (hε : ε ∈ Set.Ioc 0 1)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ p : V × ℕ, α p.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table μ, ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i := by
  obtain ⟨Γ, x, hΓ, hx, hP, -, -⟩ := exists_slack_weights_of_symmetric vbl hd
    (fun _ => measureReal_nonneg) hq hε hlll
  exact ae_exists_forall_notMem_parallelRun μ vbl A hAm hA Γ hΓ hx hε hP hrule

omit [DecidableEq ι] in
/-- `PMF.pi` bridge for parallel Moser–Tardos expected rounds under the general asymmetric slack
LLL hypothesis. -/
theorem lintegral_parallelRounds_le_pmfPi [Fintype V] [∀ v, Finite (α v)]
    [∀ v, MeasurableSingletonClass (α v)] (p : ∀ v, PMF (α v)) (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hAx : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤
      (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ q : V × ℕ, α q.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal ((max 0 (Real.log (∑ i : ι, x i / (1 - x i))) + 1) / ε) :=
  lintegral_parallelRounds_le (fun v => (p v).toMeasure) vbl A hAm hA Γ hΓ hx hε
    (fun i => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm i)] using hAx i)
    hrule

omit [DecidableEq ι] [Fintype ι] in
/-- `PMF.pi` bridge for almost-sure parallel Moser–Tardos termination and avoidance under the
general asymmetric slack LLL hypothesis. -/
theorem ae_exists_forall_notMem_parallelRun_pmfPi [Fintype V] [Finite ι]
    [∀ v, Finite (α v)] [∀ v, MeasurableSingletonClass (α v)]
    (p : ∀ v, PMF (α v)) (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hAx : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤
      (1 - ε) * (x i * ∏ j ∈ Γ i, (1 - x j)))
    {psel : (∀ q : V × ℕ, α q.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table (fun v => (p v).toMeasure),
      ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i :=
  ae_exists_forall_notMem_parallelRun (fun v => (p v).toMeasure) vbl A hAm hA Γ hΓ hx hε
    (fun i => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm i)] using hAx i)
    hrule

/-- `PMF.pi` bridge for symmetric parallel Moser–Tardos expected rounds (`1 ≤ d`). -/
theorem lintegral_parallelRounds_le_pmfPi_symmetric_of_pos [Fintype V] [∀ v, Finite (α v)]
    [∀ v, MeasurableSingletonClass (α v)] (p : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ q' : V × ℕ, α q'.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal ((max 0 (Real.log ((Fintype.card ι : ℝ) / d)) + 1) / ε) :=
  lintegral_parallelRounds_le_symmetric_of_pos (fun v => (p v).toMeasure) vbl A hAm hA hdpos hd
    (fun i => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm i)] using hq i)
    hε hlll hrule

/-- `PMF.pi` bridge for symmetric parallel Moser–Tardos expected rounds (all `d : ℕ`). -/
theorem lintegral_parallelRounds_le_pmfPi_symmetric [Fintype V] [∀ v, Finite (α v)]
    [∀ v, MeasurableSingletonClass (α v)] (p : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ q' : V × ℕ, α q'.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∫⁻ T, parallelRounds psel T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal ((max 0 (Real.log (Fintype.card ι : ℝ)) + 1) / ε) :=
  lintegral_parallelRounds_le_symmetric (fun v => (p v).toMeasure) vbl A hAm hA hd
    (fun i => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm i)] using hq i)
    hε hlll hrule

/-- `PMF.pi` bridge for almost-sure symmetric parallel Moser–Tardos termination and avoidance. -/
theorem ae_exists_forall_notMem_parallelRun_pmfPi_symmetric [Fintype V] [∀ v, Finite (α v)]
    [∀ v, MeasurableSingletonClass (α v)] (p : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q ε : ℝ} (hq : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hε : ε ∈ Set.Ioc 0 1) (hlll : Real.exp 1 * q * (d + 1) ≤ 1 - ε)
    {psel : (∀ q' : V × ℕ, α q'.1) → List ι → List ι}
    (hrule : IsValidParallelRule vbl A psel) :
    ∀ᵐ T ∂table (fun v => (p v).toMeasure),
      ∃ n : ℕ, ∀ i, current vbl T (parallelRun psel T n) ∉ A i :=
  ae_exists_forall_notMem_parallelRun_symmetric (fun v => (p v).toMeasure) vbl A hAm hA hd
    (fun i => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm i)] using hq i)
    hε hlll hrule

end SymmetricAndPMF

end Cslib.Probability.MoserTardos
