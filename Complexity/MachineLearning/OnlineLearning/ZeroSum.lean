/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.OnlineLearning.MultiplicativeWeights
public import Complexity.Probability.Minimax.Value
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Solving zero-sum games with multiplicative weights

Let `M : I → J → ℝ` be the loss matrix of a finite zero-sum game with entries in `[0, 1]`: the row
player pays `M i j`. Run multiplicative weights on the rows with learning rate `ε / 2`, where the
loss vector of round `t` is the column `M · (col t)` of a column `col t` that best responds to the
current distribution (`bestResponse`). After `T ≥ 4 ln n / ε ^ 2` rounds, with `n = card I`
[AroraHazanKale2012, §3.2, Theorem 3.1], [FreundSchapire1999]:

* the average of the learner's distributions (`averageProb`) pays at most `v + ε` against every
  column and the empirical distribution of the columns played (`empirical`) collects at least
  `v - ε` against every row, where `v` is the value of the game
  (`mw_bestResponse_approx_optimal`);
* the average payoff `(1 / T) ∑ t, ⟨p t, M · (col t)⟩` lies in `[v, v + ε]`
  (`averagePayoff_mem_Icc`);
* the average distribution pays at most the guarantee of the empirical column distribution plus
  `ε` (`sum_averageProb_mul_le_sum_empirical_mul_add`), for every row and column, with no reference
  to `v`.

This is an algorithmic minimax theorem. The last inequality shows `min_p max_j ≤ max_q min_i + ε`
for every `ε > 0` without Sion's theorem, and it gives an explicit approximate form of
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le`
(`sum_averageProb_mul_le_add_of_forall_exists_sum_le`). The value `v` is that of the exact minimax
theorem (`Cslib.Probability.IsMinimaxValue`, `Cslib.Probability.exists_isMinimaxValue`).

The theorems take the best-response property of the columns as a hypothesis, so they apply to any
best-response oracle; `bestResponsePlay` is one, defined by choice (`bestResponsePlay_spec`), and
`bestResponsePlay_approx_optimal` is the result for it with `T = ⌈4 ln n / ε ^ 2⌉`, the number of
rounds of [AroraHazanKale2012, proof of Theorem 3.1].

[AroraHazanKale2012, §3.2, proof of Theorem 3.1] proves all three bounds: the average payoff bound
is their (3.5), the empirical column bound is derived from (3.5), and the bound for the average
row strategy is their footnote 1 (their main text uses the distribution of the best single round
instead). They note that the algorithm and the result are those of [FreundSchapire1999], whose
proof of convergence is different. [AroraHazanKale2012] apply Corollary 2.2 against an optimal
row strategy `p*`. Here Theorem 2.1 (`mw_regret_le`) is applied against each single row `i`, and
the comparison is with the payoff of `i` against the empirical column distribution. This avoids
`p*` and gives the inequality without `v` above; the `ε`-optimality bounds then follow from it and
the defining properties of the value (`IsMinimaxValue.exists_le`, `IsMinimaxValue.exists_ge`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.averageProb`: the average of the learner's
  distributions.
* `Cslib.MachineLearning.OnlineLearning.Experts.empirical`: the empirical distribution of a
  sequence.
* `Cslib.MachineLearning.OnlineLearning.Experts.bestResponse`: a best response of the column
  player.
* `Cslib.MachineLearning.OnlineLearning.Experts.bestResponsePlay`: the columns of multiplicative
  weights against best responses.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.sum_averageProb_mul_le_sum_empirical_mul_add`: the
  approximate minimax inequality.
* `Cslib.MachineLearning.OnlineLearning.Experts.averagePayoff_mem_Icc`: the average payoff
  approximates the value [AroraHazanKale2012, (3.5)].
* `Cslib.MachineLearning.OnlineLearning.Experts.mw_bestResponse_approx_optimal`: the average row
  strategy and the empirical column strategy are `ε`-optimal [AroraHazanKale2012, Theorem 3.1].
* `Cslib.MachineLearning.OnlineLearning.Experts.sum_averageProb_mul_le_add_of_forall_exists_sum_le`:
  an algorithmic form of the minimax theorem.
* `Cslib.MachineLearning.OnlineLearning.Experts.bestResponsePlay_approx_optimal`: Theorem 3.1 of
  [AroraHazanKale2012] for `bestResponsePlay` with `T = ⌈4 ln n / ε ^ 2⌉` rounds.

## References

* [S. Arora, E. Hazan, S. Kale, *The Multiplicative Weights Update Method: a Meta-Algorithm and
  Applications*][AroraHazanKale2012]
* [Y. Freund, R. E. Schapire, *Adaptive game playing using multiplicative
  weights*][FreundSchapire1999]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Real Convexity Cslib.Probability

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The average of the distributions `p t` over the first `T` rounds. -/
noncomputable def averageProb (p : ℕ → I → ℝ) (T : ℕ) (i : I) : ℝ :=
  (∑ t ∈ range T, p t i) / T

/-- The empirical distribution of the first `T` entries of the sequence `col`. -/
noncomputable def empirical [DecidableEq J] (col : ℕ → J) (T : ℕ) (j : J) : ℝ :=
  (#{t ∈ range T | col t = j} : ℝ) / T

omit [Fintype I] in
/-- The average is nonnegative if the averaged distributions are. -/
theorem averageProb_nonneg {p : ℕ → I → ℝ} {T : ℕ} (hp : ∀ t < T, ∀ i, 0 ≤ p t i) (i : I) :
    0 ≤ averageProb p T i :=
  div_nonneg (sum_nonneg fun t ht => hp t (mem_range.mp ht) i) (Nat.cast_nonneg _)

/-- The average of `T > 0` distributions is a distribution. -/
theorem sum_averageProb {p : ℕ → I → ℝ} {T : ℕ} (hT : 0 < T) (hp : ∀ t < T, ∑ i, p t i = 1) :
    ∑ i, averageProb p T i = 1 := by
  simp only [averageProb, ← sum_div]
  rw [sum_comm, sum_congr rfl fun t ht => hp t (mem_range.mp ht)]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast hT.ne')

/-- The expectation of `f` under the empirical distribution is the average of `f` along the
sequence. -/
theorem sum_empirical_mul [DecidableEq J] (col : ℕ → J) (T : ℕ) (f : J → ℝ) :
    ∑ j, empirical col T j * f j = (∑ t ∈ range T, f (col t)) / T := by
  simp only [empirical, div_mul_eq_mul_div, ← sum_div]
  congr 1
  calc ∑ j, (#{t ∈ range T | col t = j} : ℝ) * f j
      = ∑ j, ∑ t ∈ range T, if col t = j then f j else 0 := by
        refine sum_congr rfl fun j _ => ?_
        rw [← sum_boole, sum_mul]
        refine sum_congr rfl fun t _ => ?_
        split_ifs
        · exact one_mul _
        · exact zero_mul _
    _ = ∑ t ∈ range T, f (col t) := by
        rw [sum_comm]
        refine sum_congr rfl fun t _ => ?_
        rw [sum_ite_eq]
        simp only [mem_univ, ite_true]

omit [Fintype J] in
/-- The empirical distribution is nonnegative. -/
theorem empirical_nonneg [DecidableEq J] (col : ℕ → J) (T : ℕ) (j : J) :
    0 ≤ empirical col T j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The empirical distribution of `T > 0` entries is a distribution. -/
theorem sum_empirical [DecidableEq J] (col : ℕ → J) {T : ℕ} (hT : 0 < T) :
    ∑ j, empirical col T j = 1 := by
  have := sum_empirical_mul col T fun _ => 1
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul] at this
  rw [this, div_self (by exact_mod_cast hT.ne')]

/-- A best response of the column player to the row distribution `p`: a column maximizing the
expected loss `∑ i, p i * M i j` of the row player. -/
noncomputable def bestResponse [Nonempty J] (M : I → J → ℝ) (p : I → ℝ) : J :=
  (Finite.exists_max fun j => ∑ i, p i * M i j).choose

/-- `bestResponse M p` maximizes the row player's expected loss under `p`. -/
theorem le_bestResponse [Nonempty J] (M : I → J → ℝ) (p : I → ℝ) (j : J) :
    ∑ i, p i * M i j ≤ ∑ i, p i * M i (bestResponse M p) :=
  (Finite.exists_max fun j => ∑ i, p i * M i j).choose_spec j

/-- The column played in round `t` when multiplicative weights with learning rate `η` plays the
rows against best responses: the column that best responds to the current distribution. -/
noncomputable def bestResponsePlay [Nonempty J] (M : I → J → ℝ) (η : ℝ) (t : ℕ) : J :=
  bestResponse M fun i =>
    adaptiveWeight (mwFactor η) (fun _ p i => M i (bestResponse M p)) t i /
      ∑ k, adaptiveWeight (mwFactor η) (fun _ p i => M i (bestResponse M p)) t k

/-- `bestResponsePlay` best responds to the learner's distribution in every round. -/
theorem bestResponsePlay_spec [Nonempty J] (M : I → J → ℝ) (η : ℝ) (t : ℕ) (j : J) :
    ∑ i, prob (mwFactor η) (fun s i => M i (bestResponsePlay M η s)) t i * M i j ≤
      ∑ i, prob (mwFactor η) (fun s i => M i (bestResponsePlay M η s)) t i *
        M i (bestResponsePlay M η t) := by
  have h := congrFun (adaptiveLoss_eq (mwFactor η) (fun _ p i => M i (bestResponse M p)) t)
  have hrow : ∀ i, M i (bestResponsePlay M η t) =
      M i (bestResponse M (prob (mwFactor η) (fun s i => M i (bestResponsePlay M η s)) t)) := h
  simp only [hrow]
  exact le_bestResponse M _ j

section Game

variable {M : I → J → ℝ} {ε : ℝ} {T : ℕ} {col : ℕ → J}

omit [Fintype J] in
/-- The regret of multiplicative weights with learning rate `ε / 2` against any column sequence,
for a loss matrix with entries in `[0, 1]` and `ε ^ 2 T ≥ 4 ln n`. -/
private theorem game_regret (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε) (hε' : ε ≤ 1)
    (hT : 4 * log (Fintype.card I) ≤ ε ^ 2 * T) (i : I) :
    ∑ t ∈ range T, ∑ k, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t k * M k (col t) ≤
      ∑ t ∈ range T, M i (col t) + ε * T := by
  have hη : 0 < ε / 2 := by linarith
  have h := mw_regret_le (ℓ := fun s i => M i (col s)) (T := T) hη (by linarith)
    (fun s _ k => by rw [abs_le]; constructor <;> linarith [(hM k (col s)).1, (hM k (col s)).2]) i
  have habs : ∑ t ∈ range T, |M i (col t)| ≤ T := by
    calc ∑ t ∈ range T, |M i (col t)| ≤ ∑ t ∈ range T, (1 : ℝ) :=
          sum_le_sum fun t _ => by
            rw [abs_le]; constructor <;> linarith [(hM i (col t)).1, (hM i (col t)).2]
      _ = T := by simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  have hlog : log (Fintype.card I) / (ε / 2) ≤ ε * T / 2 := by
    rw [div_le_iff₀ hη]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left habs hη.le]

/-- **The approximate minimax inequality**: for a loss matrix with entries in `[0, 1]`,
`0 < ε ≤ 1` and `T > 0` rounds with `ε ^ 2 T ≥ 4 ln n`, if every column `col t` best responds to
the distribution of multiplicative weights with learning rate `ε / 2`, then against every column
`j` the average distribution pays at most `ε` more than every row `i` pays against the empirical
distribution of the columns. -/
theorem sum_averageProb_mul_le_sum_empirical_mul_add [DecidableEq J]
    (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε) (hε' : ε ≤ 1) (hT0 : 0 < T)
    (hT : 4 * log (Fintype.card I) ≤ ε ^ 2 * T)
    (hbr : ∀ t < T, ∀ j, ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i j ≤
      ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i (col t)) (i : I) (j : J) :
    ∑ k, averageProb (prob (mwFactor (ε / 2)) (fun s i => M i (col s))) T k * M k j ≤
      ∑ l, empirical col T l * M i l + ε := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  set p := prob (mwFactor (ε / 2)) (fun s i => M i (col s)) with hpdef
  have hreg := game_regret (col := col) hM hε hε' hT i
  rw [sum_empirical_mul]
  have hlhs : ∑ k, averageProb p T k * M k j = (∑ t ∈ range T, ∑ k, p t k * M k j) / T := by
    simp only [averageProb, div_mul_eq_mul_div, ← sum_div, sum_mul]
    rw [sum_comm]
  rw [hlhs, div_add' _ _ _ hT'.ne', div_le_div_iff_of_pos_right hT']
  calc ∑ t ∈ range T, ∑ k, p t k * M k j ≤ ∑ t ∈ range T, ∑ k, p t k * M k (col t) :=
        sum_le_sum fun t ht => hbr t (mem_range.mp ht) j
    _ ≤ _ := hreg

/-- **Multiplicative weights against best responses approximates the value**
[AroraHazanKale2012, (3.5)]: under the hypotheses of
`sum_averageProb_mul_le_sum_empirical_mul_add`, the average payoff
`(1 / T) ∑ t, ⟨p t, M · (col t)⟩` lies in `[v, v + ε]`, where `v` is the value of the game. -/
theorem averagePayoff_mem_Icc (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε)
    (hε' : ε ≤ 1) (hT0 : 0 < T) (hT : 4 * log (Fintype.card I) ≤ ε ^ 2 * T)
    (hbr : ∀ t < T, ∀ j, ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i j ≤
      ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i (col t))
    {v : ℝ} (hv : IsMinimaxValue M v) :
    (∑ t ∈ range T, ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i (col t)) / T ∈
      Set.Icc v (v + ε) := by
  classical
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
  have hφ : ∀ t, ∀ s < t, ∀ k, 0 < mwFactor (ε / 2) (M k (col s)) := fun t s _ k => by
    rw [mwFactor_apply]; nlinarith [(hM k (col s)).2]
  have hne : Nonempty I := by
    obtain ⟨⟨q, -⟩, -⟩ := hv
    exact q.nonempty
  constructor
  · rw [le_div_iff₀ hT']
    calc v * T = ∑ t ∈ range T, v := by
          rw [sum_const, card_range, nsmul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum fun t ht => by
          obtain ⟨j, hj⟩ := hv.exists_le (prob_nonneg (hφ t)) (sum_prob (hφ t))
          exact hj.trans (hbr t (mem_range.mp ht) j)
  · obtain ⟨i, hi⟩ := hv.exists_ge (empirical_nonneg col T) (sum_empirical col hT0)
    rw [sum_empirical_mul] at hi
    have hreg := game_regret (col := col) hM hε hε' hT i
    rw [div_le_iff₀ hT']
    rw [div_le_iff₀ hT'] at hi
    nlinarith

/-- **Multiplicative weights solves zero-sum games** [AroraHazanKale2012, Theorem 3.1],
[FreundSchapire1999]: under the hypotheses of `sum_averageProb_mul_le_sum_empirical_mul_add`,
the average distribution of the row player pays at most `v + ε` against every column, and the
empirical distribution of the columns collects at least `v - ε` against every row, where `v` is
the value of the game. -/
theorem mw_bestResponse_approx_optimal [DecidableEq J] (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1)
    (hε : 0 < ε)
    (hε' : ε ≤ 1) (hT0 : 0 < T) (hT : 4 * log (Fintype.card I) ≤ ε ^ 2 * T)
    (hbr : ∀ t < T, ∀ j, ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i j ≤
      ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i (col t))
    {v : ℝ} (hv : IsMinimaxValue M v) :
    (∀ j, ∑ k, averageProb (prob (mwFactor (ε / 2)) (fun s i => M i (col s))) T k * M k j ≤
      v + ε) ∧ ∀ i, v - ε ≤ ∑ l, empirical col T l * M i l := by
  have hφ : ∀ t, ∀ s < t, ∀ k, 0 < mwFactor (ε / 2) (M k (col s)) := fun t s _ k => by
    rw [mwFactor_apply]; nlinarith [(hM k (col s)).2]
  have hne : Nonempty I := by
    obtain ⟨⟨q, -⟩, -⟩ := hv
    exact q.nonempty
  constructor
  · intro j
    obtain ⟨i, hi⟩ := hv.exists_ge (empirical_nonneg col T) (sum_empirical col hT0)
    linarith [sum_averageProb_mul_le_sum_empirical_mul_add hM hε hε' hT0 hT hbr i j]
  · intro i
    obtain ⟨j, hj⟩ := hv.exists_le (averageProb_nonneg fun t _ => prob_nonneg (hφ t))
      (sum_averageProb hT0 fun t _ => sum_prob (hφ t))
    linarith [sum_averageProb_mul_le_sum_empirical_mul_add hM hε hε' hT0 hT hbr i j]

/-- **An algorithmic minimax theorem**: under the hypothesis of
`Convexity.StdSimplex.exists_forall_sum_le_of_forall_exists_sum_le` (against every mixed column
strategy some row pays at most `c`) and the hypotheses of
`sum_averageProb_mul_le_sum_empirical_mul_add`, the explicit average distribution of
multiplicative weights pays at most `c + ε` against every column. -/
theorem sum_averageProb_mul_le_add_of_forall_exists_sum_le
    (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε) (hε' : ε ≤ 1) (hT0 : 0 < T)
    (hT : 4 * log (Fintype.card I) ≤ ε ^ 2 * T)
    (hbr : ∀ t < T, ∀ j, ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i j ≤
      ∑ i, prob (mwFactor (ε / 2)) (fun s i => M i (col s)) t i * M i (col t))
    {c : ℝ} (h : ∀ q : StdSimplex ℝ J, ∃ i, ∑ j, q.weights j * M i j ≤ c) (j : J) :
    ∑ k, averageProb (prob (mwFactor (ε / 2)) (fun s i => M i (col s))) T k * M k j ≤ c + ε := by
  classical
  let q : StdSimplex ℝ J :=
    { weights := Finsupp.equivFunOnFinite.symm (empirical col T)
      nonneg := empirical_nonneg col T
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        exact sum_empirical col hT0 }
  obtain ⟨i, hi⟩ := h q
  have hi' : ∑ l, empirical col T l * M i l ≤ c := hi
  linarith [sum_averageProb_mul_le_sum_empirical_mul_add hM hε hε' hT0 hT hbr i j]

end Game

/-- **Multiplicative weights solves zero-sum games** [AroraHazanKale2012, Theorem 3.1], for the
best-response oracle `bestResponsePlay`: for a game with `n ≥ 2` rows, entries in `[0, 1]` and
value `v`, and `0 < ε ≤ 1`, after `T = ⌈4 ln n / ε ^ 2⌉` rounds of multiplicative weights with
learning rate `ε / 2` against best responses, the average row distribution pays at most `v + ε`
against every column, and the empirical column distribution collects at least `v - ε` against
every row. -/
theorem bestResponsePlay_approx_optimal [DecidableEq J] [Nonempty J] {M : I → J → ℝ} {ε v : ℝ}
    (hn : 2 ≤ Fintype.card I) (hM : ∀ i j, M i j ∈ Set.Icc (0 : ℝ) 1) (hε : 0 < ε)
    (hε' : ε ≤ 1) (hv : IsMinimaxValue M v) :
    let T := ⌈4 * log (Fintype.card I) / ε ^ 2⌉₊
    (∀ j, ∑ k, averageProb (prob (mwFactor (ε / 2))
        (fun s i => M i (bestResponsePlay M (ε / 2) s))) T k * M k j ≤ v + ε) ∧
      ∀ i, v - ε ≤ ∑ l, empirical (bestResponsePlay M (ε / 2)) T l * M i l := by
  intro T
  have hlog : 0 < log (Fintype.card I) := log_pos (by exact_mod_cast hn)
  have hceil := Nat.le_ceil (4 * log (Fintype.card I) / ε ^ 2)
  have hT0 : 0 < T := Nat.ceil_pos.mpr (by positivity)
  have hT : 4 * log (Fintype.card I) ≤ ε ^ 2 * T := by
    rw [div_le_iff₀ (by positivity)] at hceil
    linarith
  exact mw_bestResponse_approx_optimal hM hε hε' hT0 hT
    (fun t _ j => bestResponsePlay_spec M (ε / 2) t j) hv

end Cslib.MachineLearning.OnlineLearning.Experts
