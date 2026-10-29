/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.Bernoulli
public import Mathlib.Data.Fintype.Perm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# PPSZ: random placements and the depth recursion

The analysis of PPSZ [Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005] bounds the
probability that a variable `x` is forced by the probability of a *cut* event on the set `A` of
variables processed before `x`. This file contains the probabilistic part of that argument; it
does not mention formulas.

The paper places the variables at independent uniform times in `[0, 1]`. We work with a uniformly
random order instead. If `x` is fixed and the order `π` is uniform, the set `A` of the other `m`
variables placed before `x` equals a given set `S` with probability
`1 / ((m + 1) * C(m, |S|)) = ∫₀¹ r ^ |S| * (1 - r) ^ (m - |S|) dr`
(`card_filter_placedBefore_mul_choose`, `card_filter_placedBefore_div_factorial`). Hence for
every event `E` on sets of variables, the probability of `E(A)` is the average over `r ∈ [0, 1]`
of the probability of `E` when each of the other variables is included independently with
probability `r` (`card_filter_placedBefore_div_factorial_eq_integral`). The integrand
`bernoulliProb U r E` is a finite sum, so no measure on `[0, 1]ⁿ` is needed. This reduction is
ours (original).

For a fixed `r`, the Harris inequality (`bernoulliProb_mul_le`, from Mathlib's `fkg`) bounds the
probability of an intersection of increasing events below by the product of their probabilities.
This gives the fixed-`r` form of Lemma 7 of the paper with all `qᵢ = r`
(`prod_le_bernoulliProb_forall_or`), and by induction on the depth the bound `Q k d r` of the
PPSZ recursion (`Q_le_bernoulliProb`)
[Paturi, Pudlák, Saks, Zane, Lemma 7 (p. 350) and p. 351][PaturiPudlakSaksZane2005].

## Main definitions

* `Cslib.Complexity.PPSZ.Q`: the recursion `Q k 0 r = 0`,
  `Q k (d + 1) r = (r + (1 - r) * Q k d r) ^ (k - 1)`
  [Paturi, Pudlák, Saks, Zane, p. 351][PaturiPudlakSaksZane2005].
* `Cslib.Complexity.PPSZ.qbar`: its average `∫₀¹ Q k d r dr`.
* `Cslib.Complexity.PPSZ.placedBefore`: the variables placed before `x` in an order.
* `Cslib.Complexity.PPSZ.bernoulliProb`: the probability of an event on subsets of `U` when
  every element is included independently with probability `r`, as an explicit finite sum.

## Main results

* `Cslib.Complexity.PPSZ.qbar_three_two`: `qbar 3 2 = 31 / 70`.
* `Cslib.Complexity.PPSZ.antitone_qbar_width`: `qbar k d` is antitone in the clause width `k`
  (original).
* `Cslib.Complexity.PPSZ.integral_pow_mul_one_sub_pow`: the Beta integral
  `∫₀¹ r ^ i * (1 - r) ^ j dr = i! * j! / (i + j + 1)!`.
* `Cslib.Complexity.PPSZ.card_filter_placedBefore_mul_choose`: the set placed before `x` is a given
  set `S` in a `1 / (n * C(n - 1, |S|))` fraction of the orders (original).
* `Cslib.Complexity.PPSZ.card_filter_placedBefore_div_factorial_eq_integral`: the probability of
  any event on the set placed before `x` is `∫₀¹ bernoulliProb (univ.erase x) r E dr`
  (original).
* `Cslib.Complexity.PPSZ.bernoulliProb_eq_bernoulliAverage`: `bernoulliProb` is the
  `BitString.bernoulliAverage` of the indicator of the event, over masks `U → Bool`.
* `Cslib.Complexity.PPSZ.bernoulliProb_union_of_forall_insert`: elements that an event ignores
  can be dropped (original).
* `Cslib.Complexity.PPSZ.card_add_one_mul_integral_bernoulliProb`: conditioning a random order on
  its first element, in the form of independent inclusion (original).
* `Cslib.Complexity.PPSZ.bernoulliProb_mul_le`: the Harris inequality for increasing events.
* `Cslib.Complexity.PPSZ.prod_le_bernoulliProb_forall_or`: Lemma 7 of the paper, for a fixed
  `r`, with all `qᵢ = r` [Paturi, Pudlák, Saks, Zane, Lemma 7][PaturiPudlakSaksZane2005].
* `Cslib.Complexity.PPSZ.Q_le_bernoulliProb`: the depth recursion bounds a recursively defined
  family of increasing events [Paturi, Pudlák, Saks, Zane, p. 351][PaturiPudlakSaksZane2005].
* `Cslib.Complexity.PPSZ.qbar_le_card_filter_placedBefore_div_factorial`: the bound for a uniformly
  random order, by integration.

## References

* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
-/

@[expose] public section

namespace Cslib.Complexity.PPSZ

open Finset

/-! ### The depth recursion -/

/-- **The PPSZ depth recursion** [Paturi, Pudlák, Saks, Zane, p. 351][PaturiPudlakSaksZane2005]:
`Q k 0 r = 0` and
`Q k (d + 1) r = (r + (1 - r) * Q k d r) ^ (k - 1)`. For a critical clause tree of degree at most
`k - 1` and depth `d`, it bounds the probability of a cut when each variable is placed before the
root with probability `r`. The uppercase name follows the paper's `Q_k^{(d)}`. -/
noncomputable def Q (k : ℕ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | d + 1, r => (r + (1 - r) * Q k d r) ^ (k - 1)

/-- The average `∫₀¹ Q k d r dr` of the depth recursion, the bound on the probability that a
variable is forced [Paturi, Pudlák, Saks, Zane, p. 351][PaturiPudlakSaksZane2005]. -/
noncomputable def qbar (k d : ℕ) : ℝ := ∫ r in (0 : ℝ)..1, Q k d r

variable {k d : ℕ} {r : ℝ}

/-- At depth zero the bound is `0`. -/
@[simp]
theorem Q_zero (k : ℕ) (r : ℝ) : Q k 0 r = 0 := rfl

/-- The recursion step. -/
theorem Q_succ (k d : ℕ) (r : ℝ) : Q k (d + 1) r = (r + (1 - r) * Q k d r) ^ (k - 1) := rfl

/-- At depth one the bound is `r ^ (k - 1)`. -/
@[simp]
theorem Q_one (k : ℕ) (r : ℝ) : Q k 1 r = r ^ (k - 1) := by
  simp [Q_succ]

/-- The base `r + (1 - r) * q` of the recursion lies in `[0, 1]`. -/
theorem add_one_sub_mul_mem_Icc {q : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : r + (1 - r) * q ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hq0, hq1⟩ := hq
  constructor <;> nlinarith

/-- `Q` takes values in `[0, 1]` on `[0, 1]`. -/
theorem Q_mem_Icc (hr : r ∈ Set.Icc (0 : ℝ) 1) : Q k d r ∈ Set.Icc (0 : ℝ) 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨h0, h1⟩ := add_one_sub_mul_mem_Icc hr ih
    exact ⟨pow_nonneg h0 _, pow_le_one₀ h0 h1⟩

/-- `Q` is nonnegative on `[0, 1]`. -/
theorem Q_nonneg (hr : r ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ Q k d r := (Q_mem_Icc hr).1

/-- `Q` is at most `1` on `[0, 1]`. -/
theorem Q_le_one (hr : r ∈ Set.Icc (0 : ℝ) 1) : Q k d r ≤ 1 := (Q_mem_Icc hr).2

/-- `Q` is monotone in the depth. -/
theorem Q_le_Q_succ (hr : r ∈ Set.Icc (0 : ℝ) 1) : Q k d r ≤ Q k (d + 1) r := by
  induction d with
  | zero => exact Q_nonneg hr
  | succ d ih =>
    rw [Q_succ k (d + 1)]
    exact pow_le_pow_left₀ (add_one_sub_mul_mem_Icc hr (Q_mem_Icc hr)).1
      ((add_le_add_iff_left r).2 (mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hr.2))) _

/-- For fixed `r ∈ [0, 1]`, `Q` is monotone in the depth. -/
theorem monotone_Q (hr : r ∈ Set.Icc (0 : ℝ) 1) : Monotone fun d => Q k d r :=
  monotone_nat_of_le_succ fun _ => Q_le_Q_succ hr

/-- `Q` is monotone in `r` on `[0, 1]`. -/
theorem Q_le_Q_of_le {s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) : Q k d r ≤ Q k d s := by
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have hrI : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr, hrs.trans hs⟩
    have hsI : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.trans hrs, hs⟩
    obtain ⟨hq0, hq1⟩ := Q_mem_Icc (k := k) (d := d) hsI
    refine pow_le_pow_left₀ (add_one_sub_mul_mem_Icc hrI (Q_mem_Icc hrI)).1 ?_ _
    nlinarith [mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hrI.2)]

/-- `Q k d` is a polynomial in `r`, hence continuous. -/
@[fun_prop]
theorem continuous_Q (k d : ℕ) : Continuous (Q k d) := by
  induction d with
  | zero => exact continuous_const
  | succ d ih =>
    exact (by fun_prop : Continuous fun r => (r + (1 - r) * Q k d r) ^ (k - 1))

/-- `qbar` is nonnegative. -/
theorem qbar_nonneg : 0 ≤ qbar k d :=
  intervalIntegral.integral_nonneg zero_le_one fun _ hr => Q_nonneg hr

/-- `qbar` is at most `1`. -/
theorem qbar_le_one : qbar k d ≤ 1 := by
  have h := intervalIntegral.integral_mono_on zero_le_one
    ((continuous_Q k d).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    fun r hr => Q_le_one (k := k) (d := d) hr
  unfold qbar
  simpa using h

/-- `qbar` is monotone in the depth. -/
theorem monotone_qbar : Monotone (qbar k) := fun _ _ hde =>
  intervalIntegral.integral_mono_on zero_le_one ((continuous_Q k _).intervalIntegrable 0 1)
    ((continuous_Q k _).intervalIntegrable 0 1) fun _ hr => monotone_Q hr hde

/-- `Q` is antitone in the clause width `k` on `[0, 1]`: wider clauses give smaller bounds. The
idea is the remark of [Hertli, p. 8][Hertli2011] that `S_k` increases with `k`; the proof, by
induction on the depth, is original. -/
theorem antitone_Q_width (hr : r ∈ Set.Icc (0 : ℝ) 1) (d : ℕ) : Antitone fun k => Q k d r := by
  intro j k hjk
  dsimp only
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    obtain ⟨hb0, hb1⟩ := add_one_sub_mul_mem_Icc hr (Q_mem_Icc (k := k) (d := d) hr)
    calc Q k (d + 1) r ≤ (r + (1 - r) * Q k d r) ^ (j - 1) :=
          pow_le_pow_of_le_one hb0 hb1 (Nat.sub_le_sub_right hjk 1)
      _ ≤ Q j (d + 1) r :=
          pow_le_pow_left₀ hb0 ((add_le_add_iff_left r).2
            (mul_le_mul_of_nonneg_left ih (sub_nonneg.2 hr.2))) _

/-- `qbar` is antitone in the clause width `k`; in particular `qbar k d ≤ qbar 3 d` for
`k ≥ 3`. This is the finite-depth form of the remark of [Hertli, p. 8][Hertli2011] that `S_k`
increases with `k`. -/
theorem antitone_qbar_width (d : ℕ) : Antitone fun k => qbar k d := fun _ _ hjk =>
  intervalIntegral.integral_mono_on zero_le_one ((continuous_Q _ d).intervalIntegrable 0 1)
    ((continuous_Q _ d).intervalIntegrable 0 1) fun _ hr => antitone_Q_width hr d hjk

/-- At depth one the bound is `1 / k`, the bound of PPZ. -/
theorem qbar_one (hk : 1 ≤ k) : qbar k 1 = 1 / k := by
  simp only [qbar, Q_one, integral_pow, one_pow, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
    and_false, not_false_eq_true, zero_pow, sub_zero]
  rw [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel]

/-- The integral of a polynomial over `[0, 1]`:
`∫₀¹ ∑ i < m, c i * r ^ i dr = ∑ i < m, c i / (i + 1)`. -/
theorem integral_sum_mul_pow (c : ℕ → ℝ) (m : ℕ) :
    ∫ r in (0 : ℝ)..1, ∑ i ∈ range m, c i * r ^ i = ∑ i ∈ range m, c i / (i + 1) := by
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (by fun_prop : Continuous fun r : ℝ => c i * r ^ i).intervalIntegrable 0 1]
  refine sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [div_eq_mul_inv]

/-- **The bound at depth two for `k = 3`**: `Q 3 2 r = (r + (1 - r) * r ^ 2) ^ 2`, so
`qbar 3 2 = 31 / 70`. -/
theorem qbar_three_two : qbar 3 2 = 31 / 70 := by
  let c : ℕ → ℝ := fun i => [0, 0, 1, 2, -1, -2, 1].getD i 0
  rw [qbar, intervalIntegral.integral_congr (g := fun r => ∑ i ∈ range 7, c i * r ^ i)
    fun r _ => by
      simp only [Q_succ, Q_zero, sum_range_succ, sum_range_zero, c, List.getD_cons_succ,
        List.getD_cons_zero]
      ring, integral_sum_mul_pow]
  norm_num [sum_range_succ, c]

/-! ### The Beta integral -/

/-- **The Beta integral** `∫₀¹ r ^ i * (1 - r) ^ j dr = i! * j! / (i + j + 1)!`, by induction on
`j`. This is the value `B(i + 1, j + 1)` of the Beta function at natural numbers. Mathlib has the
general form, `ProbabilityTheory.beta α β = Γ(α) Γ(β) / Γ(α + β)` with
`ProbabilityTheory.beta_eq_betaIntegralReal` relating it to `Complex.betaIntegral`, but that
integral uses complex powers, so for natural exponents the elementary induction is shorter. -/
theorem integral_pow_mul_one_sub_pow (i j : ℕ) :
    ∫ r in (0 : ℝ)..1, r ^ i * (1 - r) ^ j =
      (i.factorial * j.factorial : ℝ) / (i + j + 1).factorial := by
  induction j generalizing i with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, one_pow, ne_eq, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero, Nat.factorial_zero,
      Nat.cast_one, add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ j ih =>
    have hsplit : (fun r : ℝ => r ^ i * (1 - r) ^ (j + 1)) =
        fun r => r ^ i * (1 - r) ^ j - r ^ (i + 1) * (1 - r) ^ j := by
      funext r
      ring
    rw [hsplit, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun r : ℝ => r ^ i * (1 - r) ^ j).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun r : ℝ => r ^ (i + 1) * (1 - r) ^ j).intervalIntegrable 0 1),
      ih i, ih (i + 1),
      show i + 1 + j + 1 = i + j + 1 + 1 by ring, show i + (j + 1) + 1 = i + j + 1 + 1 by ring]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have : ((i + j).factorial : ℝ) ≠ 0 := by positivity
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### Independent inclusion -/

section Bernoulli

variable {α : Type*}

open Classical in
/-- **Independent inclusion.** The probability that a random subset of `U`, containing each
element independently with probability `r`, satisfies `E`: the sum of the weights
`r ^ |S| * (1 - r) ^ (|U| - |S|)` over the subsets `S ⊆ U` that satisfy `E`.

This is the measure of `BitString.bernoulliAverage` carried by subsets of `U` instead of masks
`U → Bool`: `bernoulliProb_eq_bernoulliAverage` identifies the two through the bijection between
subsets of `U` and their indicator masks. We keep the `Finset` carrier because the events of PPSZ
are monotone families of variable sets and Mathlib's FKG inequality `fkg`, which gives the Harris
inequality `bernoulliProb_mul_le`, is stated on the lattice `Finset α`. -/
noncomputable def bernoulliProb (U : Finset α) (r : ℝ) (E : Finset α → Prop) : ℝ :=
  ∑ S ∈ U.powerset with E S, r ^ #S * (1 - r) ^ (#U - #S)

variable {U : Finset α} {r : ℝ} {E F : Finset α → Prop}

/-- `bernoulliProb` as a sum, for any decidability instance of the event. -/
theorem bernoulliProb_eq_sum (U : Finset α) (r : ℝ) (E : Finset α → Prop) [DecidablePred E] :
    bernoulliProb U r E = ∑ S ∈ U.powerset with E S, r ^ #S * (1 - r) ^ (#U - #S) := by
  unfold bernoulliProb
  congr

/-- Events that agree on the subsets of `U` have the same probability. -/
theorem bernoulliProb_congr (h : ∀ S ⊆ U, E S ↔ F S) :
    bernoulliProb U r E = bernoulliProb U r F := by
  classical
  rw [bernoulliProb_eq_sum, bernoulliProb_eq_sum, filter_congr fun S hS => h S (mem_powerset.1 hS)]

/-- Probabilities are nonnegative for `r ∈ [0, 1]`. -/
theorem bernoulliProb_nonneg (hr : r ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ bernoulliProb U r E := by
  classical
  rw [bernoulliProb_eq_sum]
  exact sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hr.1 _) (pow_nonneg (sub_nonneg.2 hr.2) _)

/-- The weights sum to one. -/
theorem bernoulliProb_true (U : Finset α) (r : ℝ) : bernoulliProb U r (fun _ => True) = 1 := by
  classical
  rw [bernoulliProb_eq_sum, filter_true, sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]

/-- The impossible event has probability `0`. -/
@[simp]
theorem bernoulliProb_false (U : Finset α) (r : ℝ) : bernoulliProb U r (fun _ => False) = 0 := by
  classical
  rw [bernoulliProb_eq_sum, filter_false, sum_empty]

/-- Probabilities are at most `1` for `r ∈ [0, 1]`. -/
theorem bernoulliProb_le_one (hr : r ∈ Set.Icc (0 : ℝ) 1) : bernoulliProb U r E ≤ 1 := by
  classical
  rw [← bernoulliProb_true U r, bernoulliProb_eq_sum, bernoulliProb_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun _ _ _ => trivial)
    fun _ _ _ => mul_nonneg (pow_nonneg hr.1 _) (pow_nonneg (sub_nonneg.2 hr.2) _)

/-- **Masks and subsets.** `bernoulliProb U r E` is the expectation, under
`BitString.bernoulliAverage` at rate `r`, of the indicator of `E` evaluated at the subset
`{a ∈ U | s a}` of `U` selected by a mask `s : U → Bool`. -/
theorem bernoulliProb_eq_bernoulliAverage [DecidableEq α] (U : Finset α) (r : ℝ)
    (E : Finset α → Prop) [DecidablePred E] :
    bernoulliProb U r E = BitString.bernoulliAverage r fun s : U → Bool =>
      if E (({i | s i} : Finset U).map (Function.Embedding.subtype (· ∈ U))) then 1 else 0 := by
  rw [bernoulliProb_eq_sum, sum_filter]
  unfold BitString.bernoulliAverage BitString.bernoulliWeight
  symm
  refine sum_nbij' (fun s => ({i | s i} : Finset U).map (Function.Embedding.subtype (· ∈ U)))
    (fun S i => decide (i.1 ∈ S)) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_powerset]
    intro a ha
    obtain ⟨i, -, rfl⟩ := mem_map.1 ha
    exact i.2
  · intro _ _
    exact mem_univ _
  · intro s _
    funext i
    simp
  · intro S hS
    rw [mem_powerset] at hS
    ext a
    simp only [mem_map, mem_filter, mem_univ, true_and, decide_eq_true_eq,
      Function.Embedding.coe_subtype]
    exact ⟨fun ⟨i, hi, he⟩ => he ▸ hi, fun ha => ⟨⟨a, hS ha⟩, ha, rfl⟩⟩
  · intro s _
    have hc : #({i | ¬ s i} : Finset U) = #U - #({i | s i} : Finset U) := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset U)) (fun i => s i)
      rw [card_univ, Fintype.card_coe] at h
      omega
    rw [prod_ite, prod_const, prod_const, card_map, hc, mul_ite, mul_one, mul_zero]

/-- The probability of an event is a polynomial in `r`, hence continuous. -/
@[fun_prop]
theorem continuous_bernoulliProb (U : Finset α) (E : Finset α → Prop) :
    Continuous fun r => bernoulliProb U r E := by
  classical
  simp only [bernoulliProb_eq_sum]
  fun_prop

/-- **Conditioning on one element.** For `v ∉ U`, a random subset of `insert v U` omits `v` with
probability `1 - r` and contains it with probability `r`. -/
theorem bernoulliProb_insert [DecidableEq α] {v : α} (hv : v ∉ U) (E : Finset α → Prop) :
    bernoulliProb (insert v U) r E =
      (1 - r) * bernoulliProb U r E + r * bernoulliProb U r fun S => E (insert v S) := by
  classical
  simp only [bernoulliProb_eq_sum, sum_filter]
  rw [sum_powerset_insert hv, mul_sum, mul_sum]
  congr 1 <;> refine sum_congr rfl fun t ht => ?_
  · have htU := card_le_card (mem_powerset.1 ht)
    rw [card_insert_of_notMem hv, show #U + 1 - #t = #U - #t + 1 by omega]
    split_ifs <;> ring
  · have hvt : v ∉ t := fun h => hv (mem_powerset.1 ht h)
    rw [card_insert_of_notMem hv, card_insert_of_notMem hvt, Nat.add_sub_add_right]
    split_ifs <;> ring

/-- **An element and an independent event.** If `v ∈ U` and `E` does not depend on `v`, then a
random subset contains `v` or satisfies `E` with probability `r + (1 - r) * Pr[E]`. -/
theorem bernoulliProb_mem_or [DecidableEq α] {v : α} (hv : v ∈ U)
    (hind : ∀ S, E (insert v S) ↔ E S) :
    bernoulliProb U r (fun S => v ∈ S ∨ E S) = r + (1 - r) * bernoulliProb U r E := by
  have hv' : v ∉ U.erase v := notMem_erase v U
  have h1 : bernoulliProb (U.erase v) r (fun S => v ∈ S ∨ E S) = bernoulliProb (U.erase v) r E :=
    bernoulliProb_congr fun S hS => or_iff_right fun h => hv' (hS h)
  have h2 : bernoulliProb (U.erase v) r (fun S => v ∈ insert v S ∨ E (insert v S)) = 1 := by
    rw [← bernoulliProb_true (U.erase v) r]
    exact bernoulliProb_congr fun S _ => by simp
  have h3 : bernoulliProb (U.erase v) r (fun S => E (insert v S)) =
      bernoulliProb (U.erase v) r E :=
    bernoulliProb_congr fun S _ => hind S
  rw [← insert_erase hv, bernoulliProb_insert hv', bernoulliProb_insert hv', h1, h2, h3]
  ring

/-- A given element is in the random set with probability `r`. -/
theorem bernoulliProb_mem {v : α} (hv : v ∈ U) :
    bernoulliProb U r (fun S => v ∈ S) = r := by
  classical
  rw [bernoulliProb_congr (E := fun S => v ∈ S) (F := fun S => v ∈ S ∨ False)
      fun S _ => by simp,
    bernoulliProb_mem_or hv fun _ => Iff.rfl, bernoulliProb_false, mul_zero, add_zero]

/-- **Ignored elements do not matter** (original). If `D` is disjoint from `U` and `E` does not
depend on the elements of `D`, then a random subset of `U ∪ D` satisfies `E` with the same
probability as a random subset of `U`. -/
theorem bernoulliProb_union_of_forall_insert [DecidableEq α] {D : Finset α} (hUD : Disjoint U D)
    (hE : ∀ v ∈ D, ∀ S, E (insert v S) ↔ E S) :
    bernoulliProb (U ∪ D) r E = bernoulliProb U r E := by
  induction D using Finset.induction_on with
  | empty => rw [union_empty]
  | insert v D hv ih =>
    have hvU : v ∉ U ∪ D := by
      rw [mem_union, not_or]
      exact ⟨fun h => disjoint_left.1 hUD h (mem_insert_self v D), hv⟩
    rw [union_insert, bernoulliProb_insert hvU,
      bernoulliProb_congr (E := fun S => E (insert v S)) (F := E)
        fun S _ => hE v (mem_insert_self v D) S,
      ih (disjoint_of_subset_right (subset_insert v D) hUD) fun u hu => hE u (mem_insert_of_mem hu)]
    ring

/-- **Averaging independent inclusion over `r`** (original): `∫₀¹ Pr[E] dr` gives each subset
`S ⊆ U` the weight `|S|! * (|U| - |S|)! / (|U| + 1)!`, by the Beta integral. -/
theorem integral_bernoulliProb (U : Finset α) (E : Finset α → Prop) [DecidablePred E] :
    ∫ r in (0 : ℝ)..1, bernoulliProb U r E =
      ∑ S ∈ U.powerset with E S,
        ((#S).factorial * (#U - #S).factorial : ℝ) / (#U + 1).factorial := by
  simp only [bernoulliProb_eq_sum]
  rw [intervalIntegral.integral_finsetSum fun S _ =>
    (by fun_prop : Continuous fun r : ℝ => r ^ #S * (1 - r) ^ (#U - #S)).intervalIntegrable 0 1]
  refine sum_congr rfl fun S hS => ?_
  have := card_le_card (mem_powerset.1 (mem_filter.1 hS).1)
  rw [integral_pow_mul_one_sub_pow, show #S + (#U - #S) + 1 = #U + 1 by omega]

/-- Summing over the elements of the subsets of `U` is summing over the elements `y` of `U` and
the subsets of `U` containing `y`. -/
private theorem sum_powerset_sum_eq_sum_sum_powerset_erase [DecidableEq α] {β : Type*}
    [AddCommMonoid β] (U : Finset α) (g : α → Finset α → β) :
    ∑ S ∈ U.powerset, ∑ y ∈ S, g y S = ∑ y ∈ U, ∑ S ∈ (U.erase y).powerset, g y (insert y S) := by
  calc ∑ S ∈ U.powerset, ∑ y ∈ S, g y S
        = ∑ S ∈ U.powerset, ∑ y ∈ U, if y ∈ S then g y S else 0 := by
          refine sum_congr rfl fun S hS => ?_
          rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.2 (mem_powerset.1 hS)]
    _ = ∑ y ∈ U, ∑ S ∈ U.powerset, if y ∈ S then g y S else 0 := sum_comm
    _ = _ := by
          refine sum_congr rfl fun y hy => ?_
          conv_lhs => rw [← insert_erase hy]
          rw [sum_powerset_insert (notMem_erase y U),
            sum_eq_zero fun S hS => ite_eq_right fun h => notMem_erase y U (mem_powerset.1 hS h),
            zero_add]
          exact sum_congr rfl fun S _ => ite_eq_left (mem_insert_self y S)

/-- **The first element of a random order, for independent inclusion** (original). For every
event `E` on subsets of `U`,
`(|U| + 1) * ∫₀¹ Pr_U[E] dr = [E ∅] + ∑ y ∈ U, ∫₀¹ Pr_{U ∖ {y}}[E (insert y ·)] dr`.
By `card_filter_placedBefore_div_factorial_eq_integral`, the integrals are probabilities over a
uniformly random order of `U` and one more element `x`, of the event on the set placed before `x`.
The identity conditions on the first element of the order: it is `x` with probability
`1 / (|U| + 1)`, and the set placed before `x` is then empty; it is `y ∈ U` with the same
probability, and the rest of the order is then uniform. -/
theorem card_add_one_mul_integral_bernoulliProb [DecidableEq α] (U : Finset α)
    (E : Finset α → Prop) [DecidablePred E] :
    (#U + 1 : ℝ) * ∫ r in (0 : ℝ)..1, bernoulliProb U r E =
      (if E ∅ then 1 else 0) +
        ∑ y ∈ U, ∫ r in (0 : ℝ)..1, bernoulliProb (U.erase y) r fun S => E (insert y S) := by
  set N := #U with hN
  set d : Finset α → ℝ := fun S => ((#S).factorial * (N - 1 - #S).factorial : ℝ) / N.factorial
  have hNf : (N.factorial : ℝ) ≠ 0 := by positivity
  -- the weight of `S` splits over the elements of `S`
  have hc : ∀ S ⊆ U, (#U + 1 : ℝ) *
      (((#S).factorial * (#U - #S).factorial : ℝ) / (#U + 1).factorial) =
      (if S = ∅ then 1 else 0) + ∑ y ∈ S, d (S.erase y) := by
    intro S hS
    have hSN : #S ≤ N := card_le_card hS
    rw [← hN, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
    rcases S.eq_empty_or_nonempty with rfl | hne
    · rw [ite_eq_left rfl, sum_empty, card_empty, Nat.factorial_zero, Nat.sub_zero]
      field_simp
      norm_num
    · have hS0 : 0 < #S := hne.card_pos
      rw [ite_eq_right hne.ne_empty, zero_add, sum_congr rfl fun y hy =>
        show d (S.erase y) = ((#S - 1).factorial * (N - #S).factorial : ℝ) / N.factorial by
          simp only [d, card_erase_of_mem hy]
          rw [show N - 1 - (#S - 1) = N - #S by omega], sum_const, nsmul_eq_mul,
        ← Nat.mul_factorial_pred hS0.ne', Nat.cast_mul]
      field_simp
  have hd : ∀ y ∈ U, ∀ S ∈ (U.erase y).powerset,
      ((#S).factorial * (#(U.erase y) - #S).factorial : ℝ) / (#(U.erase y) + 1).factorial =
        d S := by
    intro y hy S _
    rw [card_erase_of_mem hy, ← hN, show N - 1 + 1 = N by have := card_pos.2 ⟨y, hy⟩; omega]
  rw [integral_bernoulliProb, mul_sum, sum_filter]
  simp only [integral_bernoulliProb]
  rw [sum_congr rfl fun y hy => (sum_congr rfl fun S hS => hd y hy S (mem_filter.1 hS).1).trans
    (sum_filter (fun S => E (insert y S)) d)]
  rw [← hN, sum_congr rfl fun S hS => show (if E S then (N + 1 : ℝ) *
      (((#S).factorial * (N - #S).factorial : ℝ) / (N + 1).factorial) else 0) =
      (if E S ∧ S = ∅ then 1 else 0) + ∑ y ∈ S, if E S then d (S.erase y) else 0 by
    rw [hN, hc S (mem_powerset.1 hS)]
    by_cases hES : E S
    · simp only [hES, true_and, ite_true]
    · simp only [hES, false_and, ite_false, sum_const_zero, add_zero]]
  rw [sum_add_distrib, sum_eq_single_of_mem ∅ (empty_mem_powerset U)
    fun S _ hS => ite_eq_right fun h => hS h.2, sum_powerset_sum_eq_sum_sum_powerset_erase]
  congr 1
  · simp only [and_true]
  · refine sum_congr rfl fun y _ => sum_congr rfl fun S hS => ?_
    rw [erase_insert fun h => notMem_erase y U (mem_powerset.1 hS h)]

/-- **The Harris inequality.** Increasing events are positively correlated under independent
inclusion; a consequence of the FKG inequality (Mathlib's `fkg`). -/
theorem bernoulliProb_mul_le [Finite α] (hr : r ∈ Set.Icc (0 : ℝ) 1) (hE : Monotone E)
    (hF : Monotone F) :
    bernoulliProb U r E * bernoulliProb U r F ≤ bernoulliProb U r fun S => E S ∧ F S := by
  classical
  have := Fintype.ofFinite α
  obtain ⟨hr0, hr1⟩ := hr
  set μ : Finset α → ℝ := fun S => if S ⊆ U then r ^ #S * (1 - r) ^ (#U - #S) else 0 with hμ
  set ind : (Finset α → Prop) → Finset α → ℝ := fun P S => if P S then 1 else 0 with hind
  have key : ∀ P : Finset α → Prop, bernoulliProb U r P = ∑ S, μ S * ind P S := by
    intro P
    rw [bernoulliProb_eq_sum, sum_filter,
      ← sum_subset (subset_univ U.powerset) (f := fun S => μ S * ind P S) ?_]
    · refine sum_congr rfl fun S hS => ?_
      simp only [hμ, hind, mem_powerset.1 hS, ite_true, mul_ite, mul_one, mul_zero]
    · intro S _ hS
      have hSU : ¬ S ⊆ U := fun h => hS (mem_powerset.2 h)
      simp only [hμ, hSU, ite_false, zero_mul]
  have hμ0 : 0 ≤ μ := fun S => by
    simp only [hμ, Pi.zero_apply]
    split_ifs
    · exact mul_nonneg (pow_nonneg hr0 _) (pow_nonneg (sub_nonneg.2 hr1) _)
    · exact le_rfl
  have hind0 : ∀ P, 0 ≤ ind P := fun P S => by
    simp only [hind, Pi.zero_apply]
    split_ifs <;> norm_num
  have hindm : ∀ P : Finset α → Prop, Monotone P → Monotone (ind P) := fun P hP S T hST => by
    simp only [hind]
    by_cases hS : P S
    · simp [hS, hP hST hS]
    · simp only [hS, ite_false]
      split_ifs <;> norm_num
  have hμm : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b) := by
    intro a b
    by_cases ha : a ⊆ U
    · by_cases hb : b ⊆ U
      · have hab : a ∩ b ⊆ U := inter_subset_left.trans ha
        have hab' : a ∪ b ⊆ U := union_subset ha hb
        have e1 : #a + #b = #(a ∩ b) + #(a ∪ b) := by
          have := card_union_add_card_inter a b
          omega
        have e2 : (#U - #a) + (#U - #b) = (#U - #(a ∩ b)) + (#U - #(a ∪ b)) := by
          have h1 := card_le_card hab'
          have h2 := card_union_add_card_inter a b
          have h3 := card_le_card ha
          have h4 := card_le_card hb
          have h5 := card_le_card (subset_union_left : a ⊆ a ∪ b)
          omega
        refine le_of_eq ?_
        simp only [hμ, inf_eq_inter, sup_eq_union, ha, hb, hab, hab', ite_true]
        calc r ^ #a * (1 - r) ^ (#U - #a) * (r ^ #b * (1 - r) ^ (#U - #b))
            = r ^ (#a + #b) * (1 - r) ^ ((#U - #a) + (#U - #b)) := by ring
          _ = r ^ (#(a ∩ b) + #(a ∪ b)) * (1 - r) ^ ((#U - #(a ∩ b)) + (#U - #(a ∪ b))) := by
            rw [e1, e2]
          _ = _ := by ring
      · have : μ b = 0 := by simp [hμ, hb]
        rw [this, mul_zero]
        exact mul_nonneg (hμ0 _) (hμ0 _)
    · have : μ a = 0 := by simp [hμ, ha]
      rw [this, zero_mul]
      exact mul_nonneg (hμ0 _) (hμ0 _)
  have h := fkg (μ := μ) (f := ind E) (g := ind F) (hμ₀ := hμ0) (hf₀ := hind0 E)
    (hg₀ := hind0 F) (hf := hindm E hE) (hg := hindm F hF) (hμ := hμm)
  have htot : ∑ S, μ S = 1 := by
    rw [← bernoulliProb_true U r, key]
    simp [hind]
  have hprod : ∀ S, ind E S * ind F S = ind (fun S => E S ∧ F S) S := fun S => by
    simp only [hind]
    split_ifs <;> simp_all
  rw [key E, key F, key fun S => E S ∧ F S]
  simpa only [htot, one_mul, hprod] using h

/-- **The Harris inequality for a finite family** of increasing events. -/
theorem prod_le_bernoulliProb_forall [Finite α] (hr : r ∈ Set.Icc (0 : ℝ) 1) {ι : Type*}
    (s : Finset ι) {E : ι → Finset α → Prop} (hE : ∀ i ∈ s, Monotone (E i)) :
    ∏ i ∈ s, bernoulliProb U r (E i) ≤ bernoulliProb U r fun S => ∀ i ∈ s, E i S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty, bernoulliProb_congr (E := fun S => ∀ i ∈ (∅ : Finset ι), E i S)
      (F := fun _ => True) fun S _ => by simp,
      bernoulliProb_true]
  | insert a s ha ih =>
    rw [prod_insert ha]
    have hmono : Monotone fun S => ∀ i ∈ s, E i S :=
      fun S T hST hS i hi => hE i (mem_insert_of_mem hi) hST (hS i hi)
    calc bernoulliProb U r (E a) * ∏ i ∈ s, bernoulliProb U r (E i)
        ≤ bernoulliProb U r (E a) * bernoulliProb U r fun S => ∀ i ∈ s, E i S :=
          mul_le_mul_of_nonneg_left (ih fun i hi => hE i (mem_insert_of_mem hi))
            (bernoulliProb_nonneg hr)
      _ ≤ bernoulliProb U r fun S => E a S ∧ ∀ i ∈ s, E i S :=
          bernoulliProb_mul_le hr (hE a (mem_insert_self a s)) hmono
      _ = bernoulliProb U r fun S => ∀ i ∈ insert a s, E i S :=
          bernoulliProb_congr fun S _ => by simp

/-- **The PPSZ product bound**, the fixed-`r` form of
[Paturi, Pudlák, Saks, Zane, Lemma 7][PaturiPudlakSaksZane2005] with all `qᵢ = r`. Let `vᵢ ∈ U`
and let `Eᵢ` be increasing events that do not depend on `vᵢ`. Then the event that every `vᵢ` is
in the random set or `Eᵢ` holds has probability at least `∏ᵢ (r + (1 - r) * Pr[Eᵢ])`. In the
paper, `vᵢ` are the children of the root of a critical clause tree and `Eᵢ` are the cut events of
the subtrees below them. -/
theorem prod_le_bernoulliProb_forall_or [Finite α] [DecidableEq α]
    (hr : r ∈ Set.Icc (0 : ℝ) 1) {ι : Type*} (s : Finset ι) {v : ι → α}
    {E : ι → Finset α → Prop} (hv : ∀ i ∈ s, v i ∈ U) (hE : ∀ i ∈ s, Monotone (E i))
    (hind : ∀ i ∈ s, ∀ S, E i (insert (v i) S) ↔ E i S) :
    ∏ i ∈ s, (r + (1 - r) * bernoulliProb U r (E i)) ≤
      bernoulliProb U r fun S => ∀ i ∈ s, v i ∈ S ∨ E i S := by
  rw [prod_congr rfl fun i hi => (bernoulliProb_mem_or (hv i hi) (hind i hi)).symm]
  exact prod_le_bernoulliProb_forall hr s fun i hi S T hST hS =>
    hS.imp (fun h => hST h) (hE i hi hST)

/-- **The PPSZ product bound, uniform form.** If there are at most `m` events `Eᵢ` as in
`prod_le_bernoulliProb_forall_or`, each of probability at least `q ∈ [0, 1]`, the probability is
at least `(r + (1 - r) * q) ^ m`. -/
theorem pow_le_bernoulliProb_forall_or [Finite α] [DecidableEq α]
    (hr : r ∈ Set.Icc (0 : ℝ) 1) {ι : Type*} {s : Finset ι} {v : ι → α}
    {E : ι → Finset α → Prop} (hv : ∀ i ∈ s, v i ∈ U) (hE : ∀ i ∈ s, Monotone (E i))
    (hind : ∀ i ∈ s, ∀ S, E i (insert (v i) S) ↔ E i S) {m : ℕ} (hs : #s ≤ m) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqE : ∀ i ∈ s, q ≤ bernoulliProb U r (E i)) :
    (r + (1 - r) * q) ^ m ≤ bernoulliProb U r fun S => ∀ i ∈ s, v i ∈ S ∨ E i S := by
  obtain ⟨hb0, hb1⟩ := add_one_sub_mul_mem_Icc hr hq
  calc (r + (1 - r) * q) ^ m ≤ (r + (1 - r) * q) ^ #s := pow_le_pow_of_le_one hb0 hb1 hs
    _ = ∏ _i ∈ s, (r + (1 - r) * q) := (prod_const _).symm
    _ ≤ ∏ i ∈ s, (r + (1 - r) * bernoulliProb U r (E i)) :=
        prod_le_prod₀ (fun _ _ => hb0) fun i hi =>
          (add_le_add_iff_left r).2 (mul_le_mul_of_nonneg_left (hqE i hi) (sub_nonneg.2 hr.2))
    _ ≤ _ := prod_le_bernoulliProb_forall_or hr s hv hE hind

/-- **One step of the depth recursion.** If at most `k - 1` increasing events `Eᵢ`, each not
depending on `vᵢ ∈ U`, have probability at least `Q k d r`, then the event that every `vᵢ` is in
the random set or `Eᵢ` holds has probability at least `Q k (d + 1) r`. -/
theorem Q_succ_le_bernoulliProb_forall_or [Finite α] [DecidableEq α]
    (hr : r ∈ Set.Icc (0 : ℝ) 1) {ι : Type*} {s : Finset ι} {v : ι → α}
    {E : ι → Finset α → Prop} (hv : ∀ i ∈ s, v i ∈ U) (hE : ∀ i ∈ s, Monotone (E i))
    (hind : ∀ i ∈ s, ∀ S, E i (insert (v i) S) ↔ E i S) {k d : ℕ} (hs : #s ≤ k - 1)
    (hqE : ∀ i ∈ s, Q k d r ≤ bernoulliProb U r (E i)) :
    Q k (d + 1) r ≤ bernoulliProb U r fun S => ∀ i ∈ s, v i ∈ S ∨ E i S :=
  pow_le_bernoulliProb_forall_or hr hv hE hind hs (Q_mem_Icc hr) hqE

/-- **The depth recursion bounds recursive events**
[Paturi, Pudlák, Saks, Zane, p. 351][PaturiPudlakSaksZane2005]. Let `E d b` be increasing
events indexed by a height `d` and a node `b`, among the nodes satisfying `good d b`. Suppose a
good node `b` of height `d + 1` has a set `ch b ⊆ U` of at most `k - 1` child labels, the child
`nxt b y` of label `y` is good of height `d`, its event does not depend on `y`, and `E (d + 1) b`
holds exactly when every child label is in the set or its child's event holds. Then every good
node of height `d` has `Q k d r ≤ Pr[E d b]`. For a critical clause tree, `E d b` is the event
that the paths of length `d` below `b` are cut. -/
theorem Q_le_bernoulliProb [Finite α] [DecidableEq α] (hr : r ∈ Set.Icc (0 : ℝ) 1)
    {k : ℕ} {β : Type*} (E : ℕ → β → Finset α → Prop) (good : ℕ → β → Prop) (ch : β → Finset α)
    (nxt : β → α → β) (hmono : ∀ d b, good d b → Monotone (E d b))
    (hch : ∀ d b, good (d + 1) b → ch b ⊆ U ∧ #(ch b) ≤ k - 1)
    (hgood : ∀ d b, good (d + 1) b → ∀ y ∈ ch b, good d (nxt b y))
    (hind : ∀ d b, good (d + 1) b → ∀ y ∈ ch b, ∀ S, E d (nxt b y) (insert y S) ↔ E d (nxt b y) S)
    (hrec : ∀ d b, good (d + 1) b → ∀ S ⊆ U, E (d + 1) b S ↔ ∀ y ∈ ch b, y ∈ S ∨ E d (nxt b y) S) :
    ∀ d b, good d b → Q k d r ≤ bernoulliProb U r (E d b) := by
  intro d
  induction d with
  | zero => exact fun b _ => bernoulliProb_nonneg hr
  | succ d ih =>
    intro b hb
    rw [bernoulliProb_congr (hrec d b hb)]
    exact Q_succ_le_bernoulliProb_forall_or hr (v := id) (fun y hy => (hch d b hb).1 hy)
      (fun y hy => hmono d _ (hgood d b hb y hy)) (hind d b hb) (hch d b hb).2
      fun y hy => ih _ (hgood d b hb y hy)

end Bernoulli

/-! ### Random placements -/

section Placement

variable {n : ℕ}

/-- The variables placed before `x` by the order `π`, in which `π j` is placed at step `j`. This is
`PPZ.prefixSet π (π.symm x)` (`placedBefore_eq_prefixSet`, in
`Complexity.Computability.Complexity.FineGrained.PPSZ.Unique`); it is defined separately because
this file does not depend on formulas or on PPZ. -/
def placedBefore (π : Equiv.Perm (Fin n)) (x : Fin n) : Finset (Fin n) :=
  univ.filter fun y => π.symm y < π.symm x

/-- `y` is placed before `x` when its position is smaller. -/
theorem mem_placedBefore {π : Equiv.Perm (Fin n)} {x y : Fin n} :
    y ∈ placedBefore π x ↔ π.symm y < π.symm x := by
  simp [placedBefore]

/-- `x` is not placed before itself. -/
theorem placedBefore_subset_erase (π : Equiv.Perm (Fin n)) (x : Fin n) :
    placedBefore π x ⊆ univ.erase x := fun y hy =>
  mem_erase.2 ⟨fun h => (lt_irrefl _ (h ▸ mem_placedBefore.1 hy)), mem_univ y⟩

/-- `x` is preceded by as many variables as its position. -/
theorem card_placedBefore (π : Equiv.Perm (Fin n)) (x : Fin n) :
    #(placedBefore π x) = π.symm x := by
  have : placedBefore π x = (Iio (π.symm x)).map π.toEmbedding := by
    ext y
    simp only [mem_placedBefore, mem_map, mem_Iio, Equiv.coe_toEmbedding]
    constructor
    · exact fun h => ⟨π.symm y, h, π.apply_symm_apply y⟩
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
  rw [this, card_map, Fin.card_Iio]

/-- The classes of a set `P`, a point `p` and the rest. -/
private def classify {α : Type*} [DecidableEq α] (P : Finset α) (p y : α) : Fin 3 :=
  if y ∈ P then 0 else if y = p then 1 else 2

private theorem classify_eq_zero {α : Type*} [DecidableEq α] {P : Finset α} {p y : α} :
    classify P p y = 0 ↔ y ∈ P := by
  unfold classify
  by_cases hy : y ∈ P
  · simp [hy]
  · by_cases hyp : y = p <;> simp [hy, hyp]

private theorem classify_eq_one {α : Type*} [DecidableEq α] {P : Finset α} {p y : α}
    (hp : p ∉ P) : classify P p y = 1 ↔ y = p := by
  unfold classify
  by_cases hy : y ∈ P
  · simp only [hy, ite_true]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro rfl
      exact absurd hy hp
  · by_cases hyp : y = p
    · subst hyp
      simp [hy]
    · simp [hy, hyp]

private theorem classify_eq_two {α : Type*} [DecidableEq α] {P : Finset α} {p y : α} :
    classify P p y = 2 ↔ y ∉ P ∧ y ≠ p := by
  unfold classify
  by_cases hy : y ∈ P
  · simp [hy]
  · by_cases hyp : y = p
    · subst hyp
      simp [hy]
    · simp [hy, hyp]

private theorem card_fiber_classify {α : Type*} [Fintype α] [DecidableEq α] {P : Finset α}
    {p : α} (hp : p ∉ P) (i : Fin 3) :
    Fintype.card {y // classify P p y = i} = ![#P, 1, Fintype.card α - (#P + 1)] i := by
  rw [Fintype.card_subtype]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    congr 1
    ext y
    simp [classify_eq_zero]
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [show (univ.filter fun y => classify P p y = 1) = {p} by
      ext y
      simp [classify_eq_one hp]]
    rfl
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    rw [show (univ.filter fun y => classify P p y = 2) = (insert p P)ᶜ by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_compl, mem_insert, not_or, classify_eq_two]
      exact and_comm,
      card_compl, card_insert_of_notMem hp]

/-- Permutations carrying one function to another with fibers of the same sizes. -/
private theorem card_filter_comp_eq {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    [DecidableEq ι] (f g : α → ι)
    (h : ∀ i, Fintype.card {a // f a = i} = Fintype.card {a // g a = i}) :
    #(univ.filter fun σ : Equiv.Perm α => g ∘ σ = f) =
      ∏ i, (Fintype.card {a // f a = i}).factorial := by
  let e : α ≃ α := Equiv.ofFiberEquiv fun i => Fintype.equivOfCardEq (h i)
  have he : ∀ a, g (e a) = f a := Equiv.ofFiberEquiv_map _
  have he' : ∀ a, f (e.symm a) = g a := fun a => by rw [← he, e.apply_symm_apply]
  rw [← Fintype.card_subtype, ← DomMulAct.stabilizer_card f]
  exact Fintype.card_congr
    { toFun := fun σ => ⟨σ.1.trans e.symm, by
        funext a
        simp only [Function.comp_apply, Equiv.trans_apply, he']
        exact congrFun σ.2 a⟩
      invFun := fun τ => ⟨τ.1.trans e, by
        funext a
        simp only [Function.comp_apply, Equiv.trans_apply, he]
        exact congrFun τ.2 a⟩
      left_inv := fun σ => by
        ext a
        simp
      right_inv := fun τ => by
        ext a
        simp }

/-- The orders placing exactly `S` before `x` are those carrying the classes of `S` and `x` to the
first `|S|` positions and position `|S|`. -/
private theorem placedBefore_eq_iff {π : Equiv.Perm (Fin n)} {x : Fin n} {S : Finset (Fin n)}
    (hx : x ∉ S) (hs : #S < n) :
    placedBefore π x = S ↔
      classify (Iio (⟨#S, hs⟩ : Fin n)) ⟨#S, hs⟩ ∘ π.symm = classify S x := by
  set s : Fin n := ⟨#S, hs⟩
  have hsI : s ∉ Iio s := by simp
  constructor
  · intro h
    have hxs : π.symm x = s := by
      ext
      rw [← card_placedBefore, h]
    funext y
    simp only [Function.comp_apply, classify, ← h, mem_placedBefore, mem_Iio, ← hxs,
      π.symm.injective.eq_iff]
  · intro h
    have hxs : π.symm x = s := by
      have := congrFun h x
      simp only [Function.comp_apply] at this
      rw [(classify_eq_one hx).2 rfl, classify_eq_one hsI] at this
      exact this
    ext y
    have := congrArg (· = 0) (congrFun h y)
    simp only [Function.comp_apply, classify_eq_zero, mem_Iio, eq_iff_iff] at this
    rw [mem_placedBefore, hxs, this]

private theorem card_lt_of_notMem {x : Fin n} {S : Finset (Fin n)} (hx : x ∉ S) : #S < n := by
  have hSx : S ⊆ univ.erase x := fun y hy => mem_erase.2 ⟨by rintro rfl; exact hx hy, mem_univ y⟩
  have := card_le_card hSx
  rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin] at this
  have := x.pos
  omega

/-- **The orders placing `S` before `x`** (original): `|S|! * (n - 1 - |S|)!` of the `n!` orders
place exactly the variables of `S` before `x`. -/
theorem card_filter_placedBefore_eq {x : Fin n} {S : Finset (Fin n)} (hx : x ∉ S) :
    #(univ.filter fun π : Equiv.Perm (Fin n) => placedBefore π x = S) =
      (#S).factorial * (n - 1 - #S).factorial := by
  have hs := card_lt_of_notMem hx
  set s : Fin n := ⟨#S, hs⟩
  have hsI : s ∉ Iio s := by simp
  rw [show #(univ.filter fun π : Equiv.Perm (Fin n) => placedBefore π x = S) =
      #(univ.filter fun σ : Equiv.Perm (Fin n) => classify (Iio s) s ∘ σ = classify S x) from
    card_bij' (fun π _ => π.symm) (fun σ _ => σ.symm)
      (fun π hπ => by simpa [placedBefore_eq_iff hx hs] using hπ)
      (fun σ hσ => by simpa [placedBefore_eq_iff hx hs] using hσ)
      (fun π _ => π.symm_symm) (fun σ _ => σ.symm_symm),
    card_filter_comp_eq _ _ fun i => by
      rw [card_fiber_classify hx, card_fiber_classify hsI, Fin.card_Iio],
    Fin.prod_univ_three]
  simp only [card_fiber_classify hx, Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.factorial_one, mul_one]
  congr 2
  omega

/-- **The set placed before `x` is uniform given its size** (original): it is a given set `S` in
a `1 / (n * C(n - 1, |S|))` fraction of the orders. -/
theorem card_filter_placedBefore_mul_choose {x : Fin n} {S : Finset (Fin n)} (hx : x ∉ S) :
    #(univ.filter fun π : Equiv.Perm (Fin n) => placedBefore π x = S) *
      (n * (n - 1).choose #S) = n.factorial := by
  have hs : #S ≤ n - 1 := Nat.le_sub_one_of_lt (card_lt_of_notMem hx)
  rw [card_filter_placedBefore_eq hx, ← Nat.mul_factorial_pred x.pos.ne',
    ← Nat.choose_mul_factorial_mul_factorial hs]
  ring

/-- **The placement integral for one set** (original): the probability that exactly the
variables of `S` are placed before `x` is `∫₀¹ r ^ |S| * (1 - r) ^ (n - 1 - |S|) dr`. -/
theorem card_filter_placedBefore_div_factorial {x : Fin n} {S : Finset (Fin n)} (hx : x ∉ S) :
    (#(univ.filter fun π : Equiv.Perm (Fin n) => placedBefore π x = S) : ℝ) / n.factorial =
      ∫ r in (0 : ℝ)..1, r ^ #S * (1 - r) ^ (n - 1 - #S) := by
  have hs := card_lt_of_notMem hx
  rw [integral_pow_mul_one_sub_pow, card_filter_placedBefore_eq hx,
    show #S + (n - 1 - #S) + 1 = n by omega]
  push_cast
  rfl

/-- **Random orders as random placements** (original). For every event `E` on sets of variables,
the probability over a uniformly random order that the set placed before `x` satisfies `E` is the
average over `r ∈ [0, 1]` of the probability of `E` when each other variable is included
independently with probability `r`. -/
theorem card_filter_placedBefore_div_factorial_eq_integral (x : Fin n)
    (E : Finset (Fin n) → Prop) [DecidablePred E] :
    (#(univ.filter fun π : Equiv.Perm (Fin n) => E (placedBefore π x)) : ℝ) / n.factorial =
      ∫ r in (0 : ℝ)..1, bernoulliProb (univ.erase x) r E := by
  have hU : #(univ.erase x) = n - 1 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, Fintype.card_fin]
  have hfib := card_eq_sum_card_fiberwise (f := fun π : Equiv.Perm (Fin n) => placedBefore π x)
    (s := univ.filter fun π => E (placedBefore π x))
    (t := (univ.erase x).powerset.filter E) fun π hπ =>
      mem_filter.2 ⟨mem_powerset.2 (placedBefore_subset_erase π x), (mem_filter.1 hπ).2⟩
  have hx : ∀ S ∈ (univ.erase x).powerset.filter E, x ∉ S := fun S hS h =>
    notMem_erase x univ (mem_powerset.1 (mem_filter.1 hS).1 h)
  rw [hfib, Nat.cast_sum, sum_div]
  simp only [bernoulliProb_eq_sum, hU]
  rw [intervalIntegral.integral_finsetSum fun S _ =>
    (by fun_prop : Continuous fun r : ℝ => r ^ #S * (1 - r) ^ (n - 1 - #S)).intervalIntegrable 0 1]
  refine sum_congr rfl fun S hS => ?_
  have hfil : ((univ.filter fun π : Equiv.Perm (Fin n) => E (placedBefore π x)).filter
      fun π => placedBefore π x = S) = univ.filter fun π => placedBefore π x = S := by
    ext π
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact (mem_filter.1 hS).2
  rw [hfil, card_filter_placedBefore_div_factorial (hx S hS)]

/-- **The depth bound for a random order.** If for every `r ∈ [0, 1]` the event `E` has
probability at least `Q k d r` under independent inclusion of the variables other than `x`, then
over a uniformly random order the set placed before `x` satisfies `E` with probability at least
`qbar k d`. -/
theorem qbar_le_card_filter_placedBefore_div_factorial {k d : ℕ} {x : Fin n}
    {E : Finset (Fin n) → Prop} [DecidablePred E]
    (h : ∀ r ∈ Set.Icc (0 : ℝ) 1, Q k d r ≤ bernoulliProb (univ.erase x) r E) :
    qbar k d ≤
      (#(univ.filter fun π : Equiv.Perm (Fin n) => E (placedBefore π x)) : ℝ) / n.factorial := by
  rw [card_filter_placedBefore_div_factorial_eq_integral]
  exact intervalIntegral.integral_mono_on zero_le_one ((continuous_Q k d).intervalIntegrable 0 1)
    ((continuous_bernoulliProb _ E).intervalIntegrable 0 1) h

end Placement

end Cslib.Complexity.PPSZ
