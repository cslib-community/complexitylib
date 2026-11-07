/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.OptimalStopping.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The secretary problem

`n` candidates, totally ordered by quality, arrive in uniformly random order. On each arrival the
employer sees only the candidate's *relative rank* among those seen so far (`relRank`: how many
earlier candidates were better) and must hire or reject irrevocably, winning if the hired
candidate is the best overall. A permutation `σ : Equiv.Perm (Fin n)` gives the quality `σ i` of
the `i`-th arrival, and a rank-based rule (`Rule`) sees the list of relative ranks so far.
`successProb rule n` is the probability that the rule hires the best candidate when `σ` is
uniform.

The relative ranks of a uniform permutation are independent, the `i`-th uniform on `{0, …, i}`
(`uniform_map_relRanks`), so the problem is an instance of optimal stopping of independent
observations. The *cutoff rule* `cutoffRule r` rejects the first `r - 1` candidates and then hires
the first candidate better than all before it. It wins with probability
`(r - 1)/n · ∑_{i=r}^{n} 1/(i - 1)` for `r ≥ 2` and `1/n` for `r = 1` (`successProb_cutoffRule`,
`successProb_cutoffRule_one`). Backward induction shows that the cutoff `optimalCutoff n`, the
least `r ≥ 1` with `∑_{i=r}^{n-1} 1/i ≤ 1`, is optimal among *all* rank-based rules
(`successProb_le_successProb_optimalCutoff`). Quantitatively, no rule wins with probability more
than `1/e + 1/n`, the cutoff `⌊n/e⌋ + 1` wins with probability at least `1/e - 1/n`, and the
optimal success probability tends to `1/e`.

## Main definitions

* `Cslib.Probability.OptimalStopping.Secretary.relRank`: the relative rank of an arrival.
* `Cslib.Probability.OptimalStopping.Secretary.Rule`, `.successProb`: rank-based rules and their
  probability of hiring the best candidate.
* `Cslib.Probability.OptimalStopping.Secretary.cutoffRule`, `.optimalCutoff`: cutoff rules and
  the optimal cutoff.

## Main results

* `Cslib.Probability.OptimalStopping.Secretary.uniform_map_relRanks`: the relative ranks of a
  uniform permutation are independent and uniform.
* `Cslib.Probability.OptimalStopping.Secretary.successProb_cutoffRule`: the success probability of
  a cutoff rule.
* `Cslib.Probability.OptimalStopping.Secretary.successProb_le_successProb_optimalCutoff`: the
  optimal cutoff rule is optimal among all rank-based rules.
* `Cslib.Probability.OptimalStopping.Secretary.successProb_le_exp_neg_one_add`,
  `.exp_neg_one_sub_le_successProb_floor`, `.tendsto_successProb_optimalCutoff`: the `1/e`
  bounds and limit.

## References

* [D. V. Lindley, *Dynamic programming and decision theory*][Lindley1961]
* [E. B. Dynkin, *The optimum choice of the instant for stopping a Markov process*][Dynkin1963]
* [T. S. Ferguson, *Who solved the secretary problem?*][Ferguson1989]
-/

public section

namespace Cslib.Probability.OptimalStopping.Secretary

open scoped ENNReal

/-! ### Relative ranks of a uniform permutation -/

/-- The relative rank of the `i`-th arrival when arrival `j` has quality `σ j`: the number of
earlier arrivals of higher quality. It is `0` exactly when the arrival is the best so far. -/
@[expose] def relRank {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => j < i ∧ σ i < σ j).card

/-- The relative ranks of all arrivals, in arrival order. -/
@[expose] def relRanks {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (relRank σ)

/-- The uniform law on `{0, …, i}`, the law of the relative rank of arrival `i` (counting
from `0`). -/
@[expose] noncomputable def rankLaw (i : ℕ) : PMF ℕ :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin (i + 1))).map Fin.val

/-- The laws of the relative ranks of arrivals `k, …, k + m - 1`. -/
noncomputable def rankLaws (k m : ℕ) : List (PMF ℕ) := (List.range' k m).map rankLaw

theorem rankLaws_zero (k : ℕ) : rankLaws k 0 = [] := by simp [rankLaws]

theorem rankLaws_succ (k m : ℕ) : rankLaws k (m + 1) = rankLaw k :: rankLaws (k + 1) m := by
  simp [rankLaws, List.range'_succ]

/-- Extend a permutation of the first `n` arrivals by a last arrival of quality `v`. -/
private def insertLast {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Fin (n + 1) → Fin (n + 1) :=
  Fin.lastCases v fun j => v.succAbove (τ j)

private theorem insertLast_injective {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Function.Injective (insertLast v τ) := by
  intro a b h
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast j =>
      simp only [insertLast, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h.symm (Fin.succAbove_ne v (τ j))
  | cast i =>
    induction b using Fin.lastCases with
    | last =>
      simp only [insertLast, Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact absurd h (Fin.succAbove_ne v (τ i))
    | cast j =>
      simp only [insertLast, Fin.lastCases_castSucc, Fin.succAbove_right_inj,
        EmbeddingLike.apply_eq_iff_eq] at h
      rw [h]

private noncomputable def insertPerm {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (insertLast_injective v τ))

private theorem insertPerm_apply {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n))
    (i : Fin (n + 1)) : insertPerm v τ i = insertLast v τ i := rfl

/-- Every permutation of `n + 1` arrivals is uniquely a last quality and a permutation of the
first `n`. -/
private theorem insertPerm_bijective (n : ℕ) :
    Function.Bijective (fun p : Fin (n + 1) × Equiv.Perm (Fin n) => insertPerm p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun ⟨v, τ⟩ ⟨w, ρ⟩ h => ?_, ?_⟩
  · have hv : v = w := by
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n)) h
      simpa [insertPerm_apply, insertLast] using this
    subst hv
    have hτ : τ = ρ := by
      ext j
      have := congrArg (fun σ : Equiv.Perm (Fin (n + 1)) => σ j.castSucc) h
      simp only [insertPerm_apply, insertLast, Fin.lastCases_castSucc,
        Fin.succAbove_right_inj] at this
      rw [this]
    rw [hτ]
  · simp [Fintype.card_perm, Nat.factorial_succ]

private theorem relRank_insertPerm_castSucc {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n))
    (j : Fin n) : relRank (insertPerm v τ) j.castSucc = relRank τ j := by
  simp only [relRank, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [insertPerm_apply, insertLast, Fin.succAbove_lt_succAbove_iff,
    (Fin.castSucc_lt_last j).not_gt]

private theorem relRank_insertPerm_last {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    relRank (insertPerm v τ) (Fin.last n) = n - v := by
  simp only [relRank, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp only [insertPerm_apply, insertLast, Fin.lastCases_castSucc, Fin.lastCases_last,
    Fin.castSucc_lt_last, true_and, lt_self_iff_false, false_and, ite_false, add_zero]
  rw [Equiv.sum_comp τ (fun j => if v < v.succAbove j then 1 else 0)]
  simp only [Fin.lt_succAbove_iff_le_castSucc]
  rw [← Finset.card_filter]
  have hfilter : (Finset.univ.filter fun i : Fin n => v ≤ i.castSucc) =
      (Finset.Ico (v : ℕ) n).attachFin (fun _ hm => (Finset.mem_Ico.mp hm).2) := by
    ext i
    simp [Fin.le_def]
  rw [hfilter, Finset.card_attachFin, Nat.card_Ico]

private theorem relRanks_insertPerm {n : ℕ} (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    relRanks (insertPerm v τ) = relRanks τ ++ [n - v] := by
  simp only [relRanks]
  rw [List.ofFn_succ', List.concat_eq_append]
  simp only [relRank_insertPerm_castSucc, relRank_insertPerm_last]

private theorem uniform_map_rev_sub (n : ℕ) :
    (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).map (fun v => n - v.val) =
      rankLaw n := by
  have h : (fun v : Fin (n + 1) => n - v.val) = Fin.val ∘ Fin.revPerm := by
    funext v
    simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    omega
  rw [h, ← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv, rankLaw]

/-- The relative ranks of a uniformly random arrival order are independent, the rank of arrival
`i` uniform on `{0, …, i}`. -/
theorem uniform_map_relRanks (n : ℕ) :
    (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin n))).map relRanks =
      jointLaw (rankLaws 0 n) := by
  rw [rankLaws, ← List.range_eq_range']
  induction n with
  | zero =>
    have : (relRanks : Equiv.Perm (Fin 0) → List ℕ) = fun _ => [] := by
      funext σ; simp [relRanks]
    rw [this]
    simp only [List.range_zero, List.map_nil, jointLaw_nil]
    exact PMF.map_const _ _
  | succ n ih =>
    have hbij := insertPerm_bijective n
    let e := Equiv.ofBijective _ hbij
    have hcomp : ∀ (v : Fin (n + 1)) (τ : Equiv.Perm (Fin n)),
        relRanks (e (v, τ)) = relRanks τ ++ [n - v.val] := fun v τ => relRanks_insertPerm v τ
    rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.map_comp,
      ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, hcomp]
    have hlast : jointLaw (List.map rankLaw [n]) =
        (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).map (fun a => [n - a.val]) := by
      rw [List.map_cons, List.map_nil, jointLaw_cons, jointLaw_nil, ← uniform_map_rev_sub,
        PMF.bind_map]
      simp only [PMF.pure_map, Function.comp_def]
      rfl
    rw [List.range_succ, List.map_append, jointLaw_append, ← ih, PMF.bind_map, hlast]
    simp only [Function.comp_def, PMF.map_comp]
    simp only [← PMF.bind_pure_comp, Function.comp_def]
    exact PMF.bind_comm _ _ (fun (a : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) =>
      PMF.pure (relRanks τ ++ [n - a.val]))

/-! ### Rank-based rules -/

/-- A rank-based stopping rule: it sees the relative ranks of the arrivals so far, most recent
first, and decides whether to hire the current arrival. -/
abbrev Rule := List ℕ → Bool

/-- The rule hires the best candidate of the arrival order `σ`. -/
@[expose] def Wins {n : ℕ} (rule : Rule) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ i : Fin n, stopIndex rule [] (relRanks σ) = some i.val ∧ ∀ j, σ j ≤ σ i

/-- The probability that the rule hires the best of `n` candidates arriving in uniformly random
order. -/
@[expose] noncomputable def successProb (rule : Rule) (n : ℕ) : ℝ :=
  ((Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin n))).toOuterMeasure
    {σ | Wins rule σ}).toReal

/-- The reward for stopping, in terms of relative ranks: `1` if the current arrival is the best so
far and no later arrival is. -/
noncomputable def winReward (past future : List ℕ) : ℝ≥0∞ :=
  if past.head? = some 0 ∧ 0 ∉ future then 1 else 0

theorem relRank_eq_zero_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    relRank σ i = 0 ↔ ∀ j < i, σ j < σ i := by
  simp only [relRank, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_implies, not_and, not_lt]
  refine ⟨fun h j hj => lt_of_le_of_ne (h hj) (fun he => hj.ne (σ.injective he)),
    fun h j hj => (h j hj).le⟩

/-- An arrival is the best overall exactly when it is the best so far and no later arrival is. -/
theorem isMax_iff_relRank {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (∀ j, σ j ≤ σ i) ↔ relRank σ i = 0 ∧ ∀ j, i < j → relRank σ j ≠ 0 := by
  constructor
  · intro h
    refine ⟨(relRank_eq_zero_iff σ i).mpr fun j hj =>
        lt_of_le_of_ne (h j) (fun he => hj.ne (σ.injective he)), fun j hij hj => ?_⟩
    have := (relRank_eq_zero_iff σ j).mp hj i hij
    exact absurd (h j) (not_le.mpr this)
  · rintro ⟨hi, hlater⟩
    have : Nonempty (Fin n) := ⟨i⟩
    obtain ⟨b, hb⟩ := Finite.exists_max σ
    have hb0 : relRank σ b = 0 := (relRank_eq_zero_iff σ b).mpr fun j hj =>
      lt_of_le_of_ne (hb j) (fun he => hj.ne (σ.injective he))
    rcases lt_trichotomy i b with hib | rfl | hbi
    · exact absurd hb0 (hlater b hib)
    · exact hb
    · exact absurd (hb i) (not_le.mpr ((relRank_eq_zero_iff σ i).mp hi b hbi))

private theorem zero_mem_drop_relRanks_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    0 ∈ (relRanks σ).drop (k + 1) ↔ ∃ j : Fin n, k < j ∧ relRank σ j = 0 := by
  simp only [relRanks, List.mem_drop_iff_getElem, List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨k + 1 + j, by omega⟩, by simp; omega, h⟩
  · rintro ⟨j, hj, h⟩
    refine ⟨j - (k + 1), by omega, ?_⟩
    have : k + 1 + (j - (k + 1)) = j := by omega
    simp only [this]
    exact h

open Classical in
/-- The payoff of a rule under `winReward` is the indicator that it hires the best candidate. -/
theorem payoff_winReward {n : ℕ} (rule : Rule) (σ : Equiv.Perm (Fin n)) :
    payoff rule winReward [] (relRanks σ) = if Wins rule σ then 1 else 0 := by
  rw [payoff_eq_stopIndex]
  rcases h : stopIndex rule [] (relRanks σ) with _ | k
  · simp [Wins, h]
  · have hk : k < n := by
      simpa [relRanks] using stopIndex_lt rule [] (relRanks σ) h
    have hwin : Wins rule σ ↔ ∀ j, σ j ≤ σ ⟨k, hk⟩ := by
      constructor
      · rintro ⟨i, hi, hmax⟩
        rw [h, Option.some.injEq] at hi
        have : i = ⟨k, hk⟩ := Fin.ext hi.symm
        rw [← this]; exact hmax
      · intro hmax
        exact ⟨⟨k, hk⟩, by simp [h], hmax⟩
    have hhead : ((relRanks σ).take (k + 1)).reverse.head? = some (relRank σ ⟨k, hk⟩) := by
      rw [List.head?_reverse, List.getLast?_take]
      simp [relRanks, hk]
    simp only [Option.elim, List.append_nil, winReward, hhead, Option.some.injEq,
      zero_mem_drop_relRanks_iff, not_exists, not_and]
    rw [hwin, isMax_iff_relRank]
    congr 1

/-- The success probability is the expected payoff of an optimal stopping problem whose
observations are independent uniform ranks. -/
theorem successProb_eq (rule : Rule) (n : ℕ) :
    successProb rule n =
      (∑' xs, jointLaw (rankLaws 0 n) xs * payoff rule winReward [] xs).toReal := by
  classical
  rw [successProb, PMF.toOuterMeasure_apply]
  congr 1
  rw [← uniform_map_relRanks, Cslib.Probability.PMF.tsum_map_mul]
  refine tsum_congr fun σ => ?_
  rw [payoff_winReward, Set.indicator_apply]
  by_cases h : Wins rule σ <;> simp [h]

/-! ### Cutoff rules -/

private theorem tsum_rankLaw_mul (k : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑' x, rankLaw k x * f x = (∑ x ∈ Finset.range (k + 1), f x) / (k + 1) := by
  rw [rankLaw, Cslib.Probability.PMF.tsum_map_mul, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun x => f x) (k + 1)]
  push_cast
  rw [ENNReal.div_eq_inv_mul]

private theorem tsum_rankLaw_mul_of_eq (k : ℕ) {f : ℕ → ℝ≥0∞} {a b : ℝ≥0∞} (h0 : f 0 = a)
    (hb : ∀ x, x ≠ 0 → f x = b) :
    ∑' x, rankLaw k x * f x = (a + k * b) / (k + 1) := by
  rw [tsum_rankLaw_mul, Finset.sum_range_succ', h0,
    Finset.sum_congr rfl fun x _ => hb (x + 1) (Nat.succ_ne_zero x)]
  simp [add_comm]

private theorem ofReal_avg (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ENNReal.ofReal a + k * ENNReal.ofReal b) / (k + 1) =
      ENNReal.ofReal ((a + k * b) / (k + 1)) := by
  have hk : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_add ha (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, hk, ENNReal.ofReal_natCast]
  push_cast
  rfl

/-- Among arrivals `k, …, k + m - 1` (`k ≥ 1`), none is the best so far with probability
`k / (k + m)`. -/
private theorem tsum_rankLaws_noRecord (k m : ℕ) (hk : k ≠ 0) :
    ∑' xs, jointLaw (rankLaws k m) xs * (if 0 ∉ xs then 1 else 0) =
      ENNReal.ofReal (k / (k + m)) := by
  induction m generalizing k with
  | zero =>
    have : (k : ℝ) / (k + (0 : ℕ)) = 1 := by
      rw [Nat.cast_zero, add_zero, div_self (by exact_mod_cast hk)]
    rw [this, ENNReal.ofReal_one, rankLaws_zero, tsum_jointLaw_nil_mul]
    simp
  | succ m ih =>
    rw [rankLaws_succ, tsum_jointLaw_cons_mul]
    rw [tsum_rankLaw_mul_of_eq k (a := ENNReal.ofReal 0)
      (b := ENNReal.ofReal ((k + 1 : ℝ) / (k + 1 + m)))]
    · rw [ofReal_avg k le_rfl (by positivity)]
      congr 1
      push_cast
      field_simp
      ring
    · simp
    · intro x hx
      have hxs : ∀ xs : List ℕ, (0 ∉ x :: xs) ↔ 0 ∉ xs := by
        intro xs; simp [List.mem_cons, Ne.symm hx]
      simp only [hxs]
      have := ih (k + 1) (Nat.succ_ne_zero k)
      push_cast at this
      exact this

/-- The success probability of the cutoff rule `cutoffRule (s + 1)` with `n` candidates:
`s/n · ∑_{i=s}^{n-1} 1/i` for `s ≥ 1`, and `1/n` for `s = 0`. -/
noncomputable def cutoffValue (n s : ℕ) : ℝ :=
  if s = 0 then 1 / n else s / n * ∑ i ∈ Finset.Ico s n, (1 : ℝ) / i

theorem cutoffValue_nonneg (n s : ℕ) : 0 ≤ cutoffValue n s := by
  unfold cutoffValue
  split_ifs
  · positivity
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => by positivity)

theorem cutoffValue_of_le {n s : ℕ} (h : n ≤ s) : cutoffValue n s = 0 := by
  unfold cutoffValue
  split_ifs with hs
  · subst hs; simp [Nat.le_zero.mp h]
  · simp [Finset.Ico_eq_empty_of_le h]

/-- The backward recursion for cutoff values. -/
theorem cutoffValue_succ {n k : ℕ} (hk : k < n) :
    cutoffValue n k = ((k + 1) / n + k * cutoffValue n (k + 1)) / (k + 1) := by
  unfold cutoffValue
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · simp only [hk0.ne', Nat.succ_ne_zero, ↓reduceIte]
    rw [Finset.sum_eq_sum_Ico_succ_bot hk]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast
    field_simp

/-- The cutoff rule: reject the first `r - 1` arrivals, then hire the first arrival that is the
best so far. -/
@[expose] def cutoffRule (r : ℕ) : Rule := fun past =>
  decide (r ≤ past.length ∧ past.head? = some 0)

private theorem tsum_payoff_cutoffRule (n s : ℕ) :
    ∀ (m k : ℕ), k + m = n → ∀ past : List ℕ, past.length = k →
      ∑' xs, jointLaw (rankLaws k m) xs * payoff (cutoffRule (s + 1)) winReward past xs =
        ENNReal.ofReal (cutoffValue n (max k s)) := by
  intro m
  induction m with
  | zero =>
    intro k hk past _
    rw [cutoffValue_of_le (by omega)]
    simp [rankLaws_zero, payoff_nil]
  | succ m ih =>
    intro k hk past hpast
    rw [rankLaws_succ, tsum_jointLaw_cons_mul]
    simp only [payoff_cons]
    by_cases hks : s ≤ k
    · have hrule : ∀ x, cutoffRule (s + 1) (x :: past) = decide (x = 0) := by
        intro x; simp [cutoffRule, hpast, hks]
      simp only [hrule]
      rw [tsum_rankLaw_mul_of_eq k (a := ENNReal.ofReal ((k + 1 : ℝ) / n))
        (b := ENNReal.ofReal (cutoffValue n (k + 1)))]
      · rw [ofReal_avg k (by positivity) (cutoffValue_nonneg _ _), max_eq_left hks,
          ← cutoffValue_succ (by omega)]
      · simp only [decide_true, ite_true, winReward, List.head?_cons, true_and]
        rw [tsum_rankLaws_noRecord (k + 1) m (Nat.succ_ne_zero k)]
        congr 2
        · push_cast; ring_nf
        · rw [← hk]; push_cast; ring
      · intro x hx
        simp only [hx, decide_false, Bool.false_eq_true, ite_false]
        rw [ih (k + 1) (by omega) (x :: past) (by simp [hpast]), max_eq_left (by omega)]
    · have hrule : ∀ x, cutoffRule (s + 1) (x :: past) = false := by
        intro x; simp [cutoffRule, hpast]; omega
      simp only [hrule, Bool.false_eq_true, ite_false]
      have hconst : ∀ x, ∑' xs, jointLaw (rankLaws (k + 1) m) xs *
          payoff (cutoffRule (s + 1)) winReward (x :: past) xs =
            ENNReal.ofReal (cutoffValue n (max (k + 1) s)) :=
        fun x => ih (k + 1) (by omega) (x :: past) (by simp [hpast])
      simp only [hconst]
      rw [tsum_pmf_mul_const, max_eq_right (by omega), max_eq_right (by omega)]

/-- The cutoff rule `cutoffRule (s + 1)` wins with probability `cutoffValue n s`. -/
theorem successProb_cutoffRule_succ (s n : ℕ) :
    successProb (cutoffRule (s + 1)) n = cutoffValue n s := by
  rw [successProb_eq, tsum_payoff_cutoffRule n s n 0 (by simp) [] rfl, max_eq_right (by omega),
    ENNReal.toReal_ofReal (cutoffValue_nonneg _ _)]

/-- **The cutoff rule's success probability.** Rejecting the first `r - 1 ≥ 1` of `n` candidates
and then hiring the first best-so-far wins with probability `(r - 1)/n · ∑_{i=r}^{n} 1/(i - 1)`.
-/
theorem successProb_cutoffRule {r n : ℕ} (hr : 2 ≤ r) :
    successProb (cutoffRule r) n =
      ((r : ℝ) - 1) / n * ∑ i ∈ Finset.Icc r n, (1 : ℝ) / ((i : ℝ) - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [successProb_cutoffRule_succ, cutoffValue]
  simp only [show s ≠ 0 by omega, ↓reduceIte]
  push_cast
  rw [add_sub_cancel_right, ← Finset.Ico_add_one_right_eq_Icc, ← Finset.sum_Ico_add']
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

/-- Hiring the first candidate wins with probability `1/n`. -/
theorem successProb_cutoffRule_one (n : ℕ) : successProb (cutoffRule 1) n = 1 / n := by
  rw [successProb_cutoffRule_succ 0 n]
  simp [cutoffValue]

/-! ### Optimality -/

theorem exists_cutoff_le_one (n : ℕ) :
    ∃ r, 1 ≤ r ∧ ∑ i ∈ Finset.Ico r n, (1 : ℝ) / i ≤ 1 :=
  ⟨n + 1, by omega, by simp⟩

open Classical in
/-- The optimal cutoff: the least `r ≥ 1` with `∑_{i=r}^{n-1} 1/i ≤ 1`. -/
noncomputable def optimalCutoff (n : ℕ) : ℕ := Nat.find (exists_cutoff_le_one n)

theorem one_le_optimalCutoff (n : ℕ) : 1 ≤ optimalCutoff n := by
  classical
  exact (Nat.find_spec (exists_cutoff_le_one n)).1

theorem sum_optimalCutoff_le (n : ℕ) :
    ∑ i ∈ Finset.Ico (optimalCutoff n) n, (1 : ℝ) / i ≤ 1 := by
  classical
  exact (Nat.find_spec (exists_cutoff_le_one n)).2

theorem optimalCutoff_le {n r : ℕ} (hr : 1 ≤ r) (h : ∑ i ∈ Finset.Ico r n, (1 : ℝ) / i ≤ 1) :
    optimalCutoff n ≤ r := by
  classical
  exact Nat.find_min' (exists_cutoff_le_one n) ⟨hr, h⟩

theorem lt_sum_of_lt_optimalCutoff {n r : ℕ} (hr : 1 ≤ r) (h : r < optimalCutoff n) :
    1 < ∑ i ∈ Finset.Ico r n, (1 : ℝ) / i := by
  classical
  have := Nat.find_min (exists_cutoff_le_one n) h
  push Not at this
  exact this hr

/-- The backward-induction value of the secretary problem, from arrival `k` on, is the success
probability of continuing with the optimal cutoff rule. -/
private theorem valueFrom_rankLaws (n : ℕ) :
    ∀ (m k : ℕ), k + m = n → ∀ past : List ℕ,
      valueFrom winReward (rankLaws k m) past =
        ENNReal.ofReal (cutoffValue n (max k (optimalCutoff n - 1))) := by
  intro m
  induction m with
  | zero =>
    intro k hk past
    rw [cutoffValue_of_le (by omega)]
    simp [rankLaws_zero, valueFrom_nil]
  | succ m ih =>
    intro k hk past
    set s := optimalCutoff n - 1 with hs_def
    have hs1 : optimalCutoff n = s + 1 := by have := one_le_optimalCutoff n; omega
    rw [rankLaws_succ, valueFrom_cons]
    have hstop : ∀ x, ∑' xs, jointLaw (rankLaws (k + 1) m) xs * winReward (x :: past) xs =
        if x = 0 then ENNReal.ofReal ((k + 1 : ℝ) / n) else 0 := by
      intro x
      by_cases hx : x = 0
      · subst hx
        simp only [winReward, List.head?_cons, true_and, ite_true]
        rw [tsum_rankLaws_noRecord (k + 1) m (Nat.succ_ne_zero k)]
        congr 2
        · push_cast; ring_nf
        · rw [← hk]; push_cast; ring
      · simp [winReward, hx]
    have hcont : ∀ x, valueFrom winReward (rankLaws (k + 1) m) (x :: past) =
        ENNReal.ofReal (cutoffValue n (max (k + 1) s)) := fun x => ih (k + 1) (by omega) (x :: past)
    simp only [hstop, hcont]
    rw [tsum_rankLaw_mul_of_eq k
      (a := ENNReal.ofReal (max ((k + 1 : ℝ) / n) (cutoffValue n (max (k + 1) s))))
      (b := ENNReal.ofReal (cutoffValue n (max (k + 1) s)))]
    · rw [ofReal_avg k (le_max_of_le_right (cutoffValue_nonneg _ _)) (cutoffValue_nonneg _ _)]
      congr 1
      by_cases hks : s ≤ k
      · -- Past the optimal cutoff, hiring a best-so-far beats waiting.
        have hle : cutoffValue n (k + 1) ≤ (k + 1) / n := by
          by_cases hkn : n ≤ k + 1
          · rw [cutoffValue_of_le hkn]; positivity
          · unfold cutoffValue
            simp only [Nat.succ_ne_zero k, ↓reduceIte]
            have hsum : ∑ i ∈ Finset.Ico (k + 1) n, (1 : ℝ) / i ≤ 1 :=
              (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.Ico_subset_Ico (by omega) le_rfl)
                (fun i _ _ => by positivity)).trans (sum_optimalCutoff_le n)
            push_cast
            calc ((k : ℝ) + 1) / n * ∑ i ∈ Finset.Ico (k + 1) n, (1 : ℝ) / i
                ≤ ((k : ℝ) + 1) / n * 1 := by gcongr
              _ = ((k : ℝ) + 1) / n := mul_one _
        rw [max_eq_left (by omega : s ≤ k + 1), max_eq_left hle, max_eq_left hks]
        exact (cutoffValue_succ (show k < n by omega)).symm
      · -- Before the optimal cutoff, waiting beats hiring.
        push Not at hks
        have hge : ((k : ℝ) + 1) / n ≤ cutoffValue n s := by
          have hsn : s < n := by
            by_contra hsn
            push Not at hsn
            have := lt_sum_of_lt_optimalCutoff (n := n) (r := s) (by omega) (by omega)
            rw [Finset.Ico_eq_empty_of_le hsn, Finset.sum_empty] at this
            exact absurd this (by norm_num)
          have h1 := lt_sum_of_lt_optimalCutoff (n := n) (r := s) (by omega) (by omega)
          unfold cutoffValue
          simp only [show s ≠ 0 by omega, ↓reduceIte]
          have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          calc ((k : ℝ) + 1) / n ≤ (s : ℝ) / n := by
                gcongr; exact_mod_cast (show k + 1 ≤ s by omega)
            _ = (s : ℝ) / n * 1 := (mul_one _).symm
            _ ≤ (s : ℝ) / n * ∑ i ∈ Finset.Ico s n, (1 : ℝ) / i := by gcongr
        rw [max_eq_right (by omega : k + 1 ≤ s), max_eq_right hge, max_eq_right hks.le]
        field_simp
        ring
    · simp
    · intro x hx
      simp [hx]

/-- **Optimality of the cutoff rule** (Lindley; Dynkin): with `n` candidates, no rank-based rule
hires the best candidate with higher probability than the cutoff rule with the optimal cutoff. -/
theorem successProb_le_successProb_optimalCutoff (rule : Rule) (n : ℕ) :
    successProb rule n ≤ successProb (cutoffRule (optimalCutoff n)) n := by
  obtain ⟨s, hs⟩ : ∃ s, optimalCutoff n = s + 1 :=
    ⟨optimalCutoff n - 1, by have := one_le_optimalCutoff n; omega⟩
  have hle := tsum_payoff_le_valueFrom rule winReward (rankLaws 0 n) []
  rw [valueFrom_rankLaws n n 0 (by simp) [], hs, Nat.add_sub_cancel,
    max_eq_right (Nat.zero_le s)] at hle
  rw [hs, successProb_cutoffRule_succ, successProb_eq]
  calc _ ≤ (ENNReal.ofReal (cutoffValue n s)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = _ := ENNReal.toReal_ofReal (cutoffValue_nonneg _ _)

/-! ### The `1/e` asymptotics -/

private theorem sum_Ico_one_div_le_log {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico (a + 1) (b + 1), (1 : ℝ) / i ≤ Real.log b - Real.log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hstep : (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ≤ Real.log ((b + 1 : ℕ) : ℝ) - Real.log b := by
      rw [← Real.log_div (by positivity) hb.ne']
      have := Real.one_sub_inv_le_log_of_pos
        (show (0 : ℝ) < ((b + 1 : ℕ) : ℝ) / b by positivity)
      calc (1 : ℝ) / ((b + 1 : ℕ) : ℝ) = 1 - (((b + 1 : ℕ) : ℝ) / b)⁻¹ := by
            push_cast; field_simp; ring
        _ ≤ _ := this
    linarith

private theorem log_sub_log_le_sum_Ico_one_div {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ ∑ i ∈ Finset.Ico a b, (1 : ℝ) / i := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hstep : Real.log ((b + 1 : ℕ) : ℝ) - Real.log b ≤ (1 : ℝ) / b := by
      rw [← Real.log_div (by positivity) hb.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((b + 1 : ℕ) : ℝ) / b by positivity)
      calc _ ≤ ((b + 1 : ℕ) : ℝ) / b - 1 := this
        _ = 1 / b := by push_cast; field_simp; ring
    linarith

/-- `u log (1/u) ≤ 1/e` for `u = x / y`. -/
private theorem mul_log_div_le_exp_neg_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x / y * (Real.log y - Real.log x) ≤ Real.exp (-1) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hz : 0 < y / (Real.exp 1 * x) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hz
  rw [Real.log_div hy.ne' (by positivity), Real.log_mul he.ne' hx.ne', Real.log_exp] at hlog
  rw [Real.exp_neg]
  have hxy : 0 < x / y := by positivity
  calc x / y * (Real.log y - Real.log x) ≤ x / y * (y / (Real.exp 1 * x)) := by
        gcongr; linarith
    _ = (Real.exp 1)⁻¹ := by field_simp

theorem cutoffValue_le_exp_neg_one_add (n s : ℕ) : cutoffValue n s ≤ Real.exp (-1) + 1 / n := by
  have he := Real.exp_pos (-1)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp only [cutoffValue, ite_true]; linarith
  by_cases hsn : n ≤ s
  · rw [cutoffValue_of_le hsn]; positivity
  push Not at hsn
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  unfold cutoffValue
  simp only [hs.ne', ↓reduceIte]
  rw [Finset.sum_eq_sum_Ico_succ_bot hsn]
  have hlog := sum_Ico_one_div_le_log hs (show s ≤ b by omega)
  have hn : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hkey := mul_log_div_le_exp_neg_one hsr hbr
  have hsb : (s : ℝ) / ((b + 1 : ℕ) : ℝ) ≤ s / b := by
    gcongr; linarith
  have hlogpos : 0 ≤ Real.log b - Real.log s :=
    sub_nonneg.mpr (Real.log_le_log hsr (by exact_mod_cast (show s ≤ b by omega)))
  rw [mul_add, show (s : ℝ) / ((b + 1 : ℕ) : ℝ) * (1 / s) = 1 / ((b + 1 : ℕ) : ℝ) by
    field_simp]
  calc 1 / ((b + 1 : ℕ) : ℝ) + s / ((b + 1 : ℕ) : ℝ) *
        ∑ i ∈ Finset.Ico (s + 1) (b + 1), (1 : ℝ) / i
      ≤ 1 / ((b + 1 : ℕ) : ℝ) + s / ((b + 1 : ℕ) : ℝ) * (Real.log b - Real.log s) := by
        gcongr
    _ ≤ 1 / ((b + 1 : ℕ) : ℝ) + s / b * (Real.log b - Real.log s) := by gcongr
    _ ≤ _ := by linarith

/-- No rank-based rule hires the best of `n` candidates with probability more than `1/e + 1/n`. -/
theorem successProb_le_exp_neg_one_add (rule : Rule) (n : ℕ) :
    successProb rule n ≤ Real.exp (-1) + 1 / n := by
  refine (successProb_le_successProb_optimalCutoff rule n).trans ?_
  obtain ⟨s, hs⟩ : ∃ s, optimalCutoff n = s + 1 :=
    ⟨optimalCutoff n - 1, by have := one_le_optimalCutoff n; omega⟩
  rw [hs, successProb_cutoffRule_succ]
  exact cutoffValue_le_exp_neg_one_add _ _

/-- The value of the cutoff `⌊n/e⌋ + 1` is at least `1/e - 1/n`. -/
theorem exp_neg_one_sub_le_cutoffValue_floor {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-1) - 1 / n ≤ cutoffValue n ⌊(n : ℝ) / Real.exp 1⌋₊ := by
  set s := ⌊(n : ℝ) / Real.exp 1⌋₊ with hs_def
  have he : 1 < Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have he0 : 0 < Real.exp 1 := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsle : (s : ℝ) ≤ n / Real.exp 1 := Nat.floor_le (by positivity)
  have hslt : (n : ℝ) / Real.exp 1 < s + 1 := Nat.lt_floor_add_one _
  have hexp : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · rw [hs0]
    simp only [cutoffValue, ite_true]
    rw [hs0, Nat.cast_zero, zero_add, div_lt_one he0] at hslt
    rw [hexp]
    have : 1 / Real.exp 1 ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnr hslt.le
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  · have hsr : (0 : ℝ) < s := by exact_mod_cast hs
    have hsn : s < n := by
      have : (n : ℝ) / Real.exp 1 < n := div_lt_self hnr he
      exact_mod_cast hsle.trans_lt this
    unfold cutoffValue
    simp only [hs.ne', ↓reduceIte]
    have hlog : 1 ≤ Real.log n - Real.log s := by
      rw [← Real.log_div hnr.ne' hsr.ne', Real.le_log_iff_exp_le (by positivity),
        le_div_iff₀ hsr]
      rw [le_div_iff₀ he0] at hsle
      linarith
    have hsum := log_sub_log_le_sum_Ico_one_div hs hsn.le
    calc Real.exp (-1) - 1 / n = (n / Real.exp 1 - 1) / n := by
          rw [hexp]; field_simp
      _ ≤ s / n := by gcongr; linarith
      _ = s / n * 1 := (mul_one _).symm
      _ ≤ s / n * ∑ i ∈ Finset.Ico s n, (1 : ℝ) / i := by gcongr; linarith

/-- Rejecting the first `⌊n/e⌋` candidates and then hiring the first best-so-far wins with
probability at least `1/e - 1/n`. -/
theorem exp_neg_one_sub_le_successProb_floor {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-1) - 1 / n ≤ successProb (cutoffRule (⌊(n : ℝ) / Real.exp 1⌋₊ + 1)) n := by
  rw [successProb_cutoffRule_succ]
  exact exp_neg_one_sub_le_cutoffValue_floor hn

/-- The optimal probability of hiring the best of `n` candidates tends to `1/e`. -/
theorem tendsto_successProb_optimalCutoff :
    Filter.Tendsto (fun n : ℕ => successProb (cutoffRule (optimalCutoff n)) n) Filter.atTop
      (nhds (Real.exp (-1))) := by
  have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n : ℕ => Real.exp (-1) - 1 / n)
    (h := fun n : ℕ => Real.exp (-1) + 1 / n) ?_ ?_ ?_ ?_
  · simpa using tendsto_const_nhds.sub h0
  · simpa using tendsto_const_nhds.add h0
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (exp_neg_one_sub_le_successProb_floor hn).trans
      (successProb_le_successProb_optimalCutoff _ n)
  · exact Filter.Eventually.of_forall fun n => successProb_le_exp_neg_one_add _ n

end Cslib.Probability.OptimalStopping.Secretary
