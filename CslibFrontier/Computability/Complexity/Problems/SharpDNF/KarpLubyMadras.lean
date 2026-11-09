/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FPRAS
public import CslibFrontier.Logics.Propositional.DNF.ModelCount
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# The Karp–Luby–Madras estimator for #DNF

Let `φ = t₀ ∨ … ∨ t_{m-1}` be a formula in disjunctive normal form with `n` variables, and let
`S_i` be the set of assignments satisfying term `t_i`, so that `#φ = |S_0 ∪ … ∪ S_{m-1}|`. A
consistent term of width `w` (the number of distinct variables it mentions) has
`|S_i| = 2 ^ (n - w)`, and an inconsistent term has `S_i = ∅`. Karp, Luby and Madras
[Karp, Luby and Madras][KarpLubyMadras1989], [Mitzenmacher and Upfal, Section
11.2][MitzenmacherUpfal2017] sample a pair `(i, a)` with `a ∈ S_i` uniformly, by choosing `i` with
probability `|S_i| / Σ |S_j|` and then `a ∈ S_i` uniformly, and accept when `t_i` is the first term
that `a` satisfies. Each model is accepted for exactly one `i`, so the acceptance probability is
`#φ / Σ |S_j| ≥ 1 / m`, and `O(m ε⁻² log (1 / δ))` trials estimate `#φ` within relative error `ε`
with probability at least `1 - δ`.

The weights `|S_i| / Σ |S_j|` need not be dyadic (for `|S_0| = 1` and `|S_1| = 2` the first is
`1 / 3`), so a fair-coin program cannot sample them exactly with a bounded number of coins. The
trial here (`Cslib.Complexity.KarpLubyMadras.trial`) has the same conditional law. Let `L` be
the minimum width of a consistent term (`Cslib.Complexity.KarpLubyMadras.minWidth`). Choose
`i` uniformly below `D = dyadicSize m`, a power of two above `m`. Reject if `i ≥ m`. Otherwise flip
`padding φ i = w_i - L` fair coins and reject unless all are `false`. Then draw a uniform
assignment, force the literals of `t_i` (`Cslib.Logic.PL.Term.force`), and accept when `t_i` is
the first term satisfied. The pair `(i, a)` is then produced with probability
`2 ^ (L - w_i) / D · 1 / 2 ^ (n - w_i) = 1 / (D · 2 ^ (n - L))`, the same for every pair. Forcing an
inconsistent term never satisfies it, so contradictory terms are rejected with no special case.
The exact law (`Cslib.Complexity.KarpLubyMadras.eval_trial_true_toReal`) is

  `Pr[trial accepts] = #φ / (D · 2 ^ (n - L))`.

A satisfiable formula has a consistent term of width `L` (or `L = n`), so `#φ ≥ 2 ^ (n - L)`
(`Cslib.Complexity.KarpLubyMadras.two_pow_sub_minWidth_le_modelCount`), and the acceptance
probability is at least `1 / D ≥ 1 / (2 m + 2)`.

The estimator (`Cslib.Complexity.KarpLubyMadras.estimate`) with relative error `1 / p` and
failure probability `2 ^ (-t)` runs `T = D · K` trials, `K = 3 (t + 1) p ^ 2`, counts the
acceptances `S`, and returns the rational number `S · 2 ^ (n - L) / K`, whose mean is `#φ`. The
mean of `S` is `μ = K · #φ / 2 ^ (n - L) ≥ K`. The multiplicative Chernoff bound with deviation
`1 / p` gives failure probability at most `2 exp (-μ / (3 p ^ 2)) ≤ 2 exp (-(t + 1)) ≤ 2 ^ (-t)`
(`Cslib.Complexity.KarpLubyMadras.approxWithin_estimate`). A formula without models is counted
exactly: every trial rejects and the estimate is `0` with probability one
(`Cslib.Complexity.KarpLubyMadras.estimate_fst_eq_zero`).

## Main definitions

* `Cslib.Complexity.KarpLubyMadras.minWidth`: the minimum width of a consistent term, capped at
  the number of variables.
* `Cslib.Complexity.KarpLubyMadras.trial`: one Karp–Luby–Madras trial.
* `Cslib.Complexity.KarpLubyMadras.estimate`: the estimator.

## Main results

* `Cslib.Complexity.KarpLubyMadras.two_pow_sub_minWidth_le_modelCount`: the smallest subcube of a
  satisfiable formula is not too small.
* `Cslib.Complexity.KarpLubyMadras.sum_firstCount`: the first satisfied terms partition the models.
* `Cslib.Complexity.KarpLubyMadras.eval_trial_true_toReal`: the exact law of one trial.
* `Cslib.Complexity.KarpLubyMadras.approxWithin_estimate`: the estimate is within relative error
  `1 / p` with probability at least `1 - 2 ^ (-t)`.
* `Cslib.Complexity.KarpLubyMadras.estimate_fst_eq_zero`: a formula without models is counted
  exactly with probability one.

## References

* [R. M. Karp, M. Luby, N. Madras, *Monte-Carlo approximation algorithms for enumeration
  problems*][KarpLubyMadras1989]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*, Section 11.2][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Complexity.KarpLubyMadras

open Cslib.Logic.PL Cslib.Probability

variable {V : Type} [DecidableEq V]

/-! ### The minimum width of a consistent term -/

/-- The minimum width of a consistent term of `φ`, capped at the number of variables: the
number of `k < CNF.numVars φ` below the width of every consistent term. -/
def minWidth (φ : DNF V) : ℕ :=
  (List.range (CNF.numVars φ)).countP fun k => φ.all fun t => !t.consistent || decide (k < t.width)

private theorem countP_range_le_of_lt (p : ℕ → Bool) {w : ℕ} (hp : ∀ k, p k = true → k < w) :
    ∀ n, (List.range n).countP p ≤ w
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    by_cases hn : p n = true
    · have hlt := hp n hn
      have hle : (List.range n).countP p ≤ n := List.countP_le_length.trans_eq List.length_range
      simp only [hn, ite_true]
      omega
    · simpa [hn] using countP_range_le_of_lt p hp n

/-- The minimum width is at most the number of variables. -/
theorem minWidth_le_numVars (φ : DNF V) : minWidth φ ≤ CNF.numVars φ :=
  List.countP_le_length.trans_eq List.length_range

/-- The minimum width is at most the width of every consistent term. -/
theorem minWidth_le_width {φ : DNF V} {t : Term V} (ht : t ∈ φ) (hc : t.consistent = true) :
    minWidth φ ≤ t.width := by
  refine countP_range_le_of_lt _ (fun k hk => ?_) _
  have := (List.all_eq_true.1 hk) t ht
  simpa [hc] using this

/-- Below the number of variables, the minimum width is attained by a consistent term. -/
theorem exists_width_le_minWidth {φ : DNF V} (h : minWidth φ < CNF.numVars φ) :
    ∃ t ∈ φ, t.consistent = true ∧ t.width ≤ minWidth φ := by
  by_contra hne
  push Not at hne
  have hall : ∀ k ∈ List.range (minWidth φ + 1),
      (φ.all fun t => !t.consistent || decide (k < t.width)) = true := by
    intro k hk
    rw [List.mem_range] at hk
    refine List.all_eq_true.2 fun t ht => ?_
    cases hc : t.consistent
    · rfl
    · have := hne t ht hc
      simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
      omega
  have hle := (List.range_sublist.2 (Nat.succ_le_of_lt h)).countP_le
    (p := fun k => φ.all fun t => !t.consistent || decide (k < t.width))
  rw [List.countP_eq_length.2 hall, List.length_range] at hle
  exact absurd hle (by unfold minWidth; omega)

/-- **The smallest subcube is not too small**: a satisfiable formula has at least
`2 ^ (CNF.numVars φ - minWidth φ)` satisfying assignments. -/
theorem two_pow_sub_minWidth_le_modelCount {φ : DNF V} (hpos : 0 < DNF.modelCount φ) :
    2 ^ (CNF.numVars φ - minWidth φ) ≤ DNF.modelCount φ := by
  by_cases h : minWidth φ < CNF.numVars φ
  · obtain ⟨t, ht, hc, hw⟩ := exists_width_le_minWidth h
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
      (two_pow_sub_width_le_modelCount ht hc)
  · rw [Nat.sub_eq_zero_of_le (not_lt.1 h), pow_zero]
    exact hpos

/-! ### One trial -/

/-- The number of extra fair coins that term `i` spends so that it is chosen with probability
proportional to `2 ^ (CNF.numVars φ - width)`. -/
def padding (φ : DNF V) (i : ℕ) : ℕ := (φ.getD i []).width - minWidth φ

/-- The assignment read from the word `w` on the distinct variables of `φ`, with the literals
of term `i` forced. -/
def forcedAssignment (φ : DNF V) (i : ℕ) (w : List Bool) : V → Bool :=
  (φ.getD i []).force (wordAssignment (CNF.distinctVars φ) w)

/-- Term `i` is the first term of `φ` satisfied by the forced assignment read from `w`. -/
def firstHit (φ : DNF V) (i : ℕ) (w : List Bool) : Bool :=
  (φ.getD i []).eval (forcedAssignment φ i w) &&
    !DNF.eval (forcedAssignment φ i w) (φ.take i)

/-- A trial for term `i` accepts the word `w` when its first `padding φ i` bits are `false` and
term `i` is the first term satisfied by the forced assignment read from the remaining bits. -/
def accepts (φ : DNF V) (i : ℕ) (w : List Bool) : Bool :=
  !(w.take (padding φ i)).any id && firstHit φ i (w.drop (padding φ i))

/-- **One Karp–Luby–Madras trial.** Choose an index below the dyadic size of the number of
terms; if it names a term, flip its padding coins and draw an assignment of the variables, forced
on the term, and accept when the padding coins are all `false` and the term is the first one
satisfied. -/
noncomputable def trial (φ : DNF V) : ProbComp Bool := do
  let i ← ProbComp.sampleDyadicIndex φ.length
  if i < φ.length then
    accepts φ i <$> BitString.sampleList (padding φ i + CNF.numVars φ)
  else pure false

/-! ### The exact law of one trial -/

/-- The number of assignments of the variables of `φ`, as words, whose first satisfied term is
term `i`. -/
def firstCount (φ : DNF V) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun y : Fin (CNF.numVars φ) → Bool =>
    (φ.getD i []).eval (wordAssignment (CNF.distinctVars φ) (List.ofFn y)) = true ∧
      DNF.eval (wordAssignment (CNF.distinctVars φ) (List.ofFn y)) (φ.take i) = false).card

/-- **The first satisfied terms partition the models.** -/
theorem sum_firstCount (φ : DNF V) :
    ∑ i ∈ Finset.range φ.length, firstCount φ i = DNF.modelCount φ := by
  rw [DNF.modelCount_eq_card_filter,
    DNF.card_filter_eval_eq_sum (fun y : Fin (CNF.numVars φ) → Bool =>
      wordAssignment (CNF.distinctVars φ) (List.ofFn y))]
  rfl

/-- Requiring `a` leading `false` bits leaves the count of the remaining bits unchanged. -/
private theorem card_filter_take_drop (a n : ℕ) (f : List Bool → Bool) :
    (Finset.univ.filter fun r : Fin (a + n) → Bool =>
      (!((List.ofFn r).take a).any id && f ((List.ofFn r).drop a)) = true).card =
      (Finset.univ.filter fun x : Fin n → Bool => f (List.ofFn x) = true).card := by
  have htake (r : Fin (a + n) → Bool) :
      (List.ofFn r).take a = List.ofFn fun i : Fin a => r (Fin.castAdd n i) := by
    rw [List.ofFn_add, List.take_left' (by simp)]
    rfl
  have hdrop (r : Fin (a + n) → Bool) :
      (List.ofFn r).drop a = List.ofFn fun i : Fin n => r (Fin.natAdd a i) := by
    rw [List.ofFn_add, List.drop_left' (by simp)]
  refine Finset.card_nbij' (fun r i => r (Fin.natAdd a i)) (fun x => Fin.append (fun _ => false) x)
    ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Bool.and_eq_true,
      htake, hdrop] at hr ⊢
    exact hr.2
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Bool.and_eq_true,
      htake, hdrop, Fin.append_left, Fin.append_right] at hx ⊢
    exact ⟨by simp, hx⟩
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Bool.and_eq_true,
      htake, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, List.mem_ofFn, id_eq] at hr
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · dsimp only
      rw [Fin.append_left]
      by_contra hj
      exact hr.1 _ ⟨j, rfl⟩ (by simpa using hj)
    · dsimp only
      rw [Fin.append_right]
  · intro x _
    funext i
    dsimp only
    rw [Fin.append_right]

/-- Forcing term `i` multiplies the count of words whose first satisfied term is `i` by
`2 ^ width`. -/
theorem card_filter_firstHit (φ : DNF V) {i : ℕ} (hi : i < φ.length) :
    (Finset.univ.filter fun x : Fin (CNF.numVars φ) → Bool =>
        firstHit φ i (List.ofFn x) = true).card =
      2 ^ (φ.getD i []).width * firstCount φ i := by
  have hmem : φ.getD i [] ∈ φ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have h := card_filter_force (CNF.nodup_distinctVars φ) (DNF.mem_distinctVars_of_mem hmem)
    (fun σ => DNF.eval σ (φ.take i) = false)
  rw [CNF.length_distinctVars] at h
  simpa [firstCount, firstHit, forcedAssignment] using h

/-- **The exact law of one trial**: it accepts with probability
`#φ / (dyadicSize m * 2 ^ (n - L))`, where `m` is the number of terms, `n` the number of
variables and `L` the minimum width of a consistent term. -/
theorem eval_trial_true_toReal (φ : DNF V) :
    (ProbComp.eval (trial φ) true).toReal = (DNF.modelCount φ : ℝ) /
      (dyadicSize φ.length * 2 ^ (CNF.numVars φ - minWidth φ)) := by
  have hterm (i : ℕ) (hi : i < φ.length) :
      (ProbComp.eval (accepts φ i <$> BitString.sampleList (padding φ i + CNF.numVars φ))
        true).toReal = (firstCount φ i : ℝ) / 2 ^ (CNF.numVars φ - minWidth φ) := by
    rw [ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList_map_apply,
      ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    have hcard : (Finset.univ.filter fun r : Fin (padding φ i + CNF.numVars φ) → Bool =>
        accepts φ i (List.ofFn r) = true).card = 2 ^ (φ.getD i []).width * firstCount φ i :=
      (card_filter_take_drop _ _ (firstHit φ i)).trans (card_filter_firstHit φ hi)
    rw [hcard]
    by_cases hF : firstCount φ i = 0
    · simp [hF]
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hF)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hmem : φ.getD i [] ∈ φ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    have hL := minWidth_le_width hmem (Term.consistent_of_eval hy.1)
    have hw := Term.width_le_length (CNF.nodup_distinctVars φ) (DNF.mem_distinctVars_of_mem hmem)
    rw [CNF.length_distinctVars] at hw
    have hpow : (2 : ℝ) ^ (padding φ i + CNF.numVars φ) =
        2 ^ (φ.getD i []).width * 2 ^ (CNF.numVars φ - minWidth φ) := by
      rw [← pow_add]
      congr 1
      unfold padding
      omega
    rw [hpow]
    push_cast
    field_simp
  simp only [trial, ProbComp.eval_bind, ProbComp.eval_sampleDyadicIndex, PMF.bind_map]
  rw [PMF.bind_apply_toReal]
  simp only [Function.comp_apply, PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun i => (ProbComp.eval (if i < φ.length then
      accepts φ i <$> BitString.sampleList (padding φ i + CNF.numVars φ) else pure false)
        true).toReal)]
  have hsplit : ∑ i ∈ Finset.range (dyadicSize φ.length), (ProbComp.eval (if i < φ.length then
      accepts φ i <$> BitString.sampleList (padding φ i + CNF.numVars φ) else pure false)
        true).toReal =
      ∑ i ∈ Finset.range φ.length, (firstCount φ i : ℝ) / 2 ^ (CNF.numVars φ - minWidth φ) := by
    rw [← Finset.sum_range_add_sum_Ico _ (lt_dyadicSize φ.length).le]
    rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun i hi => by
      rw [Finset.mem_Ico] at hi
      simp [not_lt.2 hi.1]), add_zero]
    exact Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi
      simp only [hi, ↓reduceIte]
      exact hterm i hi
  rw [hsplit, ← Finset.sum_div, ← sum_firstCount φ]
  push_cast
  ring

/-! ### The estimator -/

/-- The number of trials: `dyadicSize m * 3 (t + 1) p ^ 2`. -/
def trialBudget (φ : DNF V) (p t : ℕ) : ℕ := dyadicSize φ.length * (3 * (t + 1) * p ^ 2)

/-- **The Karp–Luby–Madras estimator** with relative error `1 / p` and failure probability
`2 ^ (-t)`: count the accepting trials `S` among `trialBudget φ p t`, and return the rational
estimate `S * 2 ^ (n - L) / (3 (t + 1) p ^ 2)`. -/
noncomputable def estimate (φ : DNF V) (p t : ℕ) : ProbComp (ℕ × ℕ) :=
  (fun successes => (successes * 2 ^ (CNF.numVars φ - minWidth φ), 3 * (t + 1) * p ^ 2)) <$>
    OracleComp.countTrue (trialBudget φ p t) (trial φ)

/-- The multiplicative Chernoff bound for a repeated success count. -/
private theorem countTrue_relative_deviation (count : ℕ) (program : ProbComp Bool) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    ((ProbComp.eval (OracleComp.countTrue count program)).toOuterMeasure {successes |
      δ * (count * (ProbComp.eval program true).toReal) ≤
        |(successes : ℝ) - count * (ProbComp.eval program true).toReal|}).toReal ≤
      2 * Real.exp (-(δ ^ 2 * (count * (ProbComp.eval program true).toReal) / 3)) := by
  rw [ProbComp.eval_countTrue, PMF.toOuterMeasure_map_apply]
  have h := Probability.PMF.pi_sum_abs_sub_mean_ge_mul (fun _ : Fin count => ProbComp.eval program)
    (fun _ bit => (bit.toNat : ℝ)) (by intro i bit _; cases bit <;> norm_num) hδ hδ₁
  simpa [Set.preimage_ofPred_eq, Nat.cast_sum, Fintype.sum_bool] using h

/-- A trial on a formula without models never accepts. -/
theorem eval_trial_true_of_modelCount_eq_zero {φ : DNF V} (h : DNF.modelCount φ = 0) :
    ProbComp.eval (trial φ) true = 0 := by
  have h' := eval_trial_true_toReal φ
  rw [h, Nat.cast_zero, zero_div] at h'
  exact (ENNReal.toReal_eq_zero_iff _).1 h' |>.resolve_right (PMF.apply_ne_top _ _)

/-- On a formula without models every trial rejects, so the success count is `0` with
probability one. -/
private theorem eval_countTrue_zero {φ : DNF V} (h : DNF.modelCount φ = 0) (count : ℕ)
    {s : Set ℕ} (hs : 0 ∈ s) :
    (ProbComp.eval (OracleComp.countTrue count (trial φ))).toOuterMeasure s = 1 := by
  rw [PMF.toOuterMeasure_apply_eq_one_iff]
  intro successes hsucc
  rw [ProbComp.eval_countTrue, PMF.mem_support_map_iff] at hsucc
  obtain ⟨bits, hbits, rfl⟩ := hsucc
  rw [Probability.PMF.mem_support_pi_iff] at hbits
  have hzero : ∀ i, bits i = false := by
    intro i
    have hi := hbits i
    rw [PMF.mem_support_iff] at hi
    cases hb : bits i
    · rfl
    · rw [hb] at hi
      exact absurd (eval_trial_true_of_modelCount_eq_zero h) hi
  simpa [hzero] using hs

/-- **Zero counts are exact**: on a formula without models the estimate is `0` with probability
one, for every `p` and `t`. -/
theorem estimate_fst_eq_zero {φ : DNF V} (h : DNF.modelCount φ = 0) (p t : ℕ) :
    (ProbComp.eval (estimate φ p t)).toOuterMeasure {out | out.1 = 0} = 1 := by
  rw [estimate, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  exact eval_countTrue_zero h _ (by simp)

/-- **Accuracy of the Karp–Luby–Madras estimator**: for `p > 0`, its estimate is within relative
error `1 / p` of the number of models with probability at least `1 - (1 / 2) ^ t`. A formula
without models is counted exactly. -/
theorem approxWithin_estimate (φ : DNF V) {p : ℕ} (hp : 0 < p) (t : ℕ) :
    1 - (1 / 2 : ℝ) ^ t ≤ ((ProbComp.eval (estimate φ p t)).toOuterMeasure
      {out | ApproxWithin (DNF.modelCount φ) p out.1 out.2}).toReal := by
  set c := DNF.modelCount φ with hc_def
  set N := 2 ^ (CNF.numVars φ - minWidth φ) with hN_def
  set K := 3 * (t + 1) * p ^ 2 with hK_def
  have hK : 0 < K := by positivity
  rw [estimate, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · -- No models: every trial rejects, so the estimate is exactly `0`.
    have hone : ((ProbComp.eval (OracleComp.countTrue (trialBudget φ p t) (trial φ))).toOuterMeasure
        ((fun successes => (successes * N, K)) ⁻¹'
          {out | ApproxWithin c p out.1 out.2})) = 1 :=
      eval_countTrue_zero hc0 _ (by simp [ApproxWithin, hc0, hK])
    rw [hone, ENNReal.toReal_one]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) t]
  -- Some models: the multiplicative Chernoff bound with `δ = 1 / p`.
  have hNc : N ≤ c := two_pow_sub_minWidth_le_modelCount hcpos
  have hNpos : (0 : ℝ) < N := by rw [hN_def]; positivity
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hDR : (0 : ℝ) < dyadicSize φ.length := by exact_mod_cast dyadicSize_pos _
  have hNcR : (N : ℝ) ≤ c := by exact_mod_cast hNc
  set μ := (trialBudget φ p t : ℝ) * (ProbComp.eval (trial φ) true).toReal with hμ_def
  have hμ : μ = K * c / N := by
    rw [hμ_def, eval_trial_true_toReal, trialBudget, ← hc_def, hN_def, hK_def]
    push_cast
    field_simp
  have hδ₁ : (1 : ℝ) / p ≤ 1 := by
    rw [div_le_one hpR]
    exact_mod_cast hp
  have hchern := countTrue_relative_deviation (trialBudget φ p t) (trial φ)
    (δ := 1 / p) (by positivity) hδ₁
  rw [← hμ_def] at hchern
  set good := (fun successes => (successes * N, K)) ⁻¹' {out | ApproxWithin c p out.1 out.2}
  have hsub : goodᶜ ⊆ {successes : ℕ | 1 / p * μ ≤ |(successes : ℝ) - μ|} := by
    intro s hs
    simp only [Set.mem_compl_iff, good, Set.mem_preimage, Set.mem_ofPred_eq] at hs ⊢
    by_contra hlt
    push Not at hlt
    apply hs
    refine ⟨hK, ?_⟩
    have hμN : μ * N = K * c := by rw [hμ]; field_simp
    have hrw : ((s * N : ℕ) : ℝ) / (K : ℕ) - c = ((s : ℝ) - μ) * N / K := by
      push_cast
      field_simp
      linarith
    rw [hrw, abs_div, abs_mul, abs_of_pos hNpos, abs_of_pos hKR, div_le_div_iff₀ hKR hpR]
    have h1 : |(s : ℝ) - μ| * p < μ := by
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ hpR] at hlt
      exact hlt
    nlinarith [abs_nonneg ((s : ℝ) - μ)]
  have hbad : ((ProbComp.eval (OracleComp.countTrue (trialBudget φ p t) (trial φ))).toOuterMeasure
      goodᶜ).toReal ≤ (1 / 2 : ℝ) ^ t := by
    refine (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      (MeasureTheory.measure_mono hsub)).trans (hchern.trans ?_)
    have hexp : (t + 1 : ℝ) ≤ (1 / p) ^ 2 * μ / 3 := by
      rw [hμ, hK_def]
      push_cast
      rw [div_pow, one_pow, show (1 : ℝ) / p ^ 2 * (3 * (t + 1) * p ^ 2 * c / N) / 3 =
        (t + 1) * (c / N) by field_simp]
      have : (1 : ℝ) ≤ c / N := by rw [one_le_div hNpos]; exact hNcR
      nlinarith
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow : (2 : ℝ) ^ (t + 1) ≤ Real.exp (t + 1) := by
      rw [show ((t : ℝ) + 1) = ((t + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) he _
    calc 2 * Real.exp (-((1 / p) ^ 2 * μ / 3)) ≤ 2 * Real.exp (-(t + 1)) := by
          gcongr
      _ = 2 / Real.exp (t + 1) := by rw [Real.exp_neg, div_eq_mul_inv]
      _ ≤ 2 / 2 ^ (t + 1) := by gcongr
      _ = (1 / 2 : ℝ) ^ t := by
          rw [pow_succ, one_div_pow]
          field_simp
  have hsum := Probability.PMF.toOuterMeasure_toReal_add_compl
    (ProbComp.eval (OracleComp.countTrue (trialBudget φ p t) (trial φ))) good
  linarith

end Cslib.Complexity.KarpLubyMadras
