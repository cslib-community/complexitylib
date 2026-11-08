/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The distinct-parsing bound

A *distinct parsing* of a word `x` is a list of phrases `ws` with `ws.flatten = x` and
`ws.Nodup`. Because there are at most `k ^ i` words of length `i` over an alphabet of size `k`,
a word of length `n` cannot be cut into many distinct phrases: the number of phrases `c` is
`O(n / log n)`. This is the combinatorial core of the analysis of Lempel–Ziv incremental parsing
(LZ78) in [ZivLempel1978] and [CoverThomas2006], Ch. 13.

The basic finite inequality is `m * c ≤ n + 2 * k ^ m` for every `m` (`mul_length_le_of_nodup`):
each phrase of length less than `m` has a deficit `m - |w|`, and the total deficit of distinct
words is at most `∑_{i < m} (m - i) k ^ i ≤ 2 k ^ m`. Choosing `m` gives the two standard forms:

* `c * log_k c ≤ n + 2 c` with `m = ⌊log_k c⌋` (`length_mul_log_le_of_nodup`);
* `c * (log_k n - log_k log_k n - 4) ≤ n` (`length_mul_logb_sub_le_of_nodup`). For `k = 2` this
  is the bound `c ≤ n / ((1 - ε_n) log₂ n)` with `ε_n = min(1, (log₂ log₂ n + 4) / log₂ n)` of
  [CoverThomas2006], Lemma 13.5.3 (`length_le_div_of_nodup`, `tendsto_epsilon`). Here it is
  proved for every alphabet size `k ≥ 2` with logarithms to base `k`.

The arithmetic steps from the first inequality to the other two are stated separately
(`mul_log_le_of_forall_mul_le`, `mul_logb_sub_le_of_forall_mul_le`), because LZ78's parse is
only distinct up to its last phrase and satisfies the first inequality by a variant argument
(`mul_length_le_of_nodup_dropLast`).

## Main definitions

* `Cslib.Algorithms.Lean.LempelZiv.epsilon`: the vanishing slack `ε_n` of [CoverThomas2006],
  Lemma 13.5.3, to base `k`.

## Main results

* `Cslib.Algorithms.Lean.LempelZiv.sum_tsub_length_le_of_nodup`: the total deficit bound.
* `Cslib.Algorithms.Lean.LempelZiv.mul_length_le_of_nodup`,
  `Cslib.Algorithms.Lean.LempelZiv.mul_length_le_of_nodup_dropLast`: `m * c ≤ n + 2 * k ^ m`,
  also when only the phrases before the last are distinct (and all phrases are nonempty).
* `Cslib.Algorithms.Lean.LempelZiv.mul_log_le_of_forall_mul_le`,
  `Cslib.Algorithms.Lean.LempelZiv.mul_logb_sub_le_of_forall_mul_le`,
  `Cslib.Algorithms.Lean.LempelZiv.le_div_of_forall_mul_le`: the arithmetic inversions.
* `Cslib.Algorithms.Lean.LempelZiv.length_mul_log_le_of_nodup`,
  `Cslib.Algorithms.Lean.LempelZiv.length_mul_logb_sub_le_of_nodup`,
  `Cslib.Algorithms.Lean.LempelZiv.length_le_div_of_nodup`: the distinct-parsing bound.
* `Cslib.Algorithms.Lean.LempelZiv.tendsto_epsilon`: `ε_n → 0`.

## References

* [ZivLempel1978] J. Ziv and A. Lempel, *Compression of individual sequences via variable-rate
  coding*, IEEE Trans. Inf. Theory 24(5), 1978.
* [CoverThomas2006] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  2006, Ch. 13, Lemma 13.5.3.
-/

public section

namespace Cslib.Algorithms.Lean.LempelZiv

open Finset

variable {α : Type*}

/-! ## The finite inequality `m * c ≤ n + 2 * k ^ m` -/

/-- **Total deficit of distinct words.** For pairwise distinct words over an alphabet of size
`k`, the deficits `m - |w|` sum to at most `∑_{i < m} (m - i) k ^ i`. -/
theorem sum_tsub_length_le_of_nodup [Fintype α] {ws : List (List α)} (hws : ws.Nodup) (m : ℕ) :
    (ws.map fun w => m - w.length).sum ≤
      ∑ i ∈ Finset.range m, (m - i) * Fintype.card α ^ i := by
  classical
  rw [← List.sum_toFinset _ hws]
  set s := ws.toFinset
  have h1 : ∑ w ∈ s, (m - w.length) =
      ∑ w ∈ s.filter (fun w => w.length < m), (m - w.length) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    split_ifs with h <;> omega
  rw [h1, ← Finset.sum_fiberwise_of_maps_to (g := List.length) (t := Finset.range m)
    (fun w hw => Finset.mem_range.2 (Finset.mem_filter.1 hw).2)]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ w ∈ (s.filter fun w => w.length < m).filter (fun w => w.length = i), (m - w.length)
      = ∑ w ∈ (s.filter fun w => w.length < m).filter (fun w => w.length = i), (m - i) :=
        Finset.sum_congr rfl fun w hw => by rw [(Finset.mem_filter.1 hw).2]
    _ = ((s.filter fun w => w.length < m).filter (fun w => w.length = i)).card * (m - i) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Fintype.card α ^ i * (m - i) :=
        Nat.mul_le_mul_right _ Finset.card_filter_length_eq_le
    _ = (m - i) * Fintype.card α ^ i := Nat.mul_comm _ _

/-- `∑_{i < m} (m - i) k ^ i + (m + 2) ≤ 2 k ^ m` for `k ≥ 2`. -/
private theorem sum_range_sub_mul_pow_add_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    ∑ i ∈ Finset.range m, (m - i) * k ^ i + (m + 2) ≤ 2 * k ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have hshift : ∑ i ∈ Finset.range m, (m + 1 - (i + 1)) * k ^ (i + 1) =
        k * ∑ i ∈ Finset.range m, (m - i) * k ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [hshift, pow_succ]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    nlinarith [Nat.mul_le_mul_left k ih, Nat.mul_le_mul_right (m + 2) hk]

private theorem mul_length_le_add_deficit (m : ℕ) (ws : List (List α)) :
    m * ws.length ≤ ws.flatten.length + (ws.map fun w => m - w.length).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.length_cons, List.flatten_cons, List.length_append, List.map_cons,
      List.sum_cons, Nat.mul_succ]
    omega

/-- **Distinct-parsing inequality.** If `ws` consists of `c` pairwise distinct words of total
length `n` over an alphabet of size `k ≥ 2`, then `m * c ≤ n + 2 * k ^ m` for every `m`. -/
theorem mul_length_le_of_nodup [Fintype α] (hα : 2 ≤ Fintype.card α) {ws : List (List α)}
    (hws : ws.Nodup) (m : ℕ) :
    m * ws.length ≤ ws.flatten.length + 2 * Fintype.card α ^ m := by
  have h1 := sum_tsub_length_le_of_nodup hws m
  have h2 := sum_range_sub_mul_pow_add_le hα m
  have h3 := mul_length_le_add_deficit m ws
  omega

/-- The distinct-parsing inequality `m * c ≤ n + 2 * k ^ m` also holds when the phrases are
nonempty and only the phrases before the last are pairwise distinct, as in LZ78's parse, whose
last phrase may repeat an earlier one. -/
theorem mul_length_le_of_nodup_dropLast [Fintype α] (hα : 2 ≤ Fintype.card α)
    {ws : List (List α)} (hne : ∀ w ∈ ws, w ≠ []) (hws : ws.dropLast.Nodup) (m : ℕ) :
    m * ws.length ≤ ws.flatten.length + 2 * Fintype.card α ^ m := by
  rcases List.eq_nil_or_concat ws with rfl | ⟨vs, w, rfl⟩
  · simp
  rw [List.concat_eq_append] at hne hws ⊢
  rw [List.dropLast_concat] at hws
  -- Replace the last phrase by `[]`: the deficit grows, and `[] :: vs` is still distinct.
  have hnd : ([] :: vs).Nodup :=
    List.nodup_cons.2 ⟨fun h => hne [] (List.mem_append_left _ h) rfl, hws⟩
  have h1 := sum_tsub_length_le_of_nodup hnd m
  have h2 := sum_range_sub_mul_pow_add_le hα m
  have h3 := mul_length_le_add_deficit m (vs ++ [w])
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_nil, Nat.sub_zero, List.length_append, List.length_singleton,
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] at h1 h3 ⊢
  omega

/-! ## Arithmetic inversions -/

/-- **Logarithmic form.** If `m * c ≤ n + 2 * k ^ m` for every `m` (when `k ≥ 2`), then
`c * ⌊log_k c⌋ ≤ n + 2 * c`. For `k ≤ 1` the floor logarithm is `0` and the bound is trivial. -/
theorem mul_log_le_of_forall_mul_le {k c n : ℕ}
    (hc : 2 ≤ k → ∀ m : ℕ, m * c ≤ n + 2 * k ^ m) : c * Nat.log k c ≤ n + 2 * c := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rw [Nat.log_of_left_le_one (by omega)]
    omega
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · simp
  have h := hc hk (Nat.log k c)
  have hpow := Nat.pow_log_le_self k hpos.ne'
  rw [Nat.mul_comm]
  omega

private theorem logb_natCast_nonneg {k : ℝ} (hk : 1 < k) (n : ℕ) : 0 ≤ Real.logb k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.logb_nonneg hk (by exact_mod_cast hn)

/-- **Cover–Thomas form.** If `m * c ≤ n + 2 * k ^ m` for every `m`, with `k ≥ 2`, then
`c * (log_k n - log_k log_k n - 4) ≤ n`. The proof takes `m = ⌊log_k n - log_k log_k n⌋ - 2`, so
that `4 (log_k n) k ^ m ≤ n`, following [CoverThomas2006], Lemma 13.5.3. -/
theorem mul_logb_sub_le_of_forall_mul_le {k c n : ℕ} (hk : 2 ≤ k)
    (hc : ∀ m : ℕ, m * c ≤ n + 2 * k ^ m) :
    (c : ℝ) * (Real.logb k n - Real.logb k (Real.logb k n) - 4) ≤ n := by
  have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) < k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hkne : (k : ℝ) ≠ 1 := hk1.ne'
  have hlogk : 0 < Real.log k := Real.log_pos hk1
  set L := Real.logb k n with hL
  set t := L - Real.logb k L - 4 with ht
  have hc0 : (0 : ℝ) ≤ c := c.cast_nonneg
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  rcases le_or_gt t 0 with ht0 | ht0
  · nlinarith
  have hL0 : 0 ≤ L := logb_natCast_nonneg hk1 n
  have hLpos : 0 < L := by
    rcases hL0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at ht
      simp only [Real.logb_zero, sub_zero, zero_sub] at ht
      linarith
  have hn1 : (1 : ℝ) < n := by
    by_contra h
    replace h := not_lt.1 h
    have : L ≤ 0 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [hL, h0]; simp
      · exact Real.logb_nonpos hk1 (by exact_mod_cast h0.le) h
    linarith
  have hlogn : Real.log n = L * Real.log k := by
    rw [hL, Real.logb, div_mul_cancel₀ _ hlogk.ne']
  -- In the remaining case `log_k n ≥ 1`: otherwise `-log_k log_k n < 3`, so `t < 0`.
  have hL1 : 1 ≤ L := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
      norm_num at this ⊢
      linarith
    have hlogn2 : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show (2 : ℕ) ≤ n by exact_mod_cast hn1))
    have hneg : -Real.log L ≤ 1 / L - 1 := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hLpos)
      rw [Real.log_inv] at this
      simpa [one_div] using this
    have hlb : -Real.logb k L < 3 := by
      rw [Real.logb, ← neg_div, div_lt_iff₀ hlogk]
      have h2 : 1 / L = Real.log k / Real.log n := by
        rw [hlogn]; field_simp
      have hlogn0 : 0 < Real.log n := by linarith
      have h3 : 1 / L < 3 * Real.log k := by
        rw [h2, div_lt_iff₀ hlogn0]
        nlinarith
      linarith
    linarith
  have hlogbL : 0 ≤ Real.logb k L := Real.logb_nonneg hk1 hL1
  set u := L - Real.logb k L with hu
  have hu4 : 4 < u := by linarith
  set m : ℕ := ⌊u⌋₊ - 2 with hm
  have hfl' : u < ⌊u⌋₊ + 1 := Nat.lt_floor_add_one u
  have hfl : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hfl4 : 4 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu4.le)
  have hmR : (m : ℝ) = ⌊u⌋₊ - 2 := by
    rw [hm, Nat.cast_sub (by omega)]; norm_num
  -- `k ^ m * k ^ 2 * log_k n ≤ n`, since `m + 2 + log_k log_k n ≤ log_k n`.
  have hpow : (k : ℝ) ^ m * ((k : ℝ) ^ 2 * L) ≤ n := by
    have hexp : (m : ℝ) + 2 + Real.logb k L ≤ L := by rw [hmR]; linarith
    have := Real.rpow_le_rpow_of_exponent_le hk1.le hexp
    rw [Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_logb hk0 hkne hLpos, hL,
      Real.rpow_logb hk0 hkne (by linarith)] at this
    rw [← hL] at this
    simpa [Real.rpow_natCast, mul_assoc] using this
  have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hpow' : 4 * L * (k : ℝ) ^ m ≤ n := by
    have : 0 ≤ (k : ℝ) ^ m := by positivity
    nlinarith
  have hcm : (m : ℝ) * c ≤ n + 2 * (k : ℝ) ^ m := by exact_mod_cast hc m
  have htm : t * (2 * L + 1) ≤ 2 * L * m := by rw [hmR]; nlinarith
  have key : (c : ℝ) * t * (2 * L + 1) ≤ n * (2 * L + 1) := by
    have : 0 ≤ (k : ℝ) ^ m := by positivity
    nlinarith
  have h2L : 0 < 2 * L + 1 := by linarith
  nlinarith

/-- The slack `ε_n = min(1, (log_k log_k n + 4) / log_k n)` of [CoverThomas2006], Lemma 13.5.3
(there with `k = 2`). It tends to `0` (`tendsto_epsilon`). -/
noncomputable def epsilon (k n : ℕ) : ℝ :=
  min 1 ((Real.logb k (Real.logb k n) + 4) / Real.logb k n)

/-- `(1 - ε_n) log_k n` is at most `log_k n - log_k log_k n - 4` whenever the latter is relevant:
precisely, `c * ((1 - ε_n) log_k n) ≤ n` follows from the Cover–Thomas form. -/
private theorem mul_one_sub_epsilon_le {k c n : ℕ} (hk : 2 ≤ k)
    (h : (c : ℝ) * (Real.logb k n - Real.logb k (Real.logb k n) - 4) ≤ n) :
    (c : ℝ) * ((1 - epsilon k n) * Real.logb k n) ≤ n := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hL0 : 0 ≤ Real.logb k n := logb_natCast_nonneg hk1 n
  have hc0 : (0 : ℝ) ≤ c := c.cast_nonneg
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  unfold epsilon
  set L := Real.logb k n
  set r := (Real.logb k L + 4) / L
  rcases hL0.lt_or_eq with hLpos | hL
  · rcases le_total r 1 with hr | hr
    · rw [min_eq_right hr]
      have : (1 - r) * L = L - Real.logb k L - 4 := by
        simp only [r]; field_simp; ring
      rw [this]; exact h
    · rw [min_eq_left hr]; simp [hn0]
  · rw [← hL]; simp [hn0]

/-- **Cover–Thomas Lemma 13.5.3, arithmetic form.** If `m * c ≤ n + 2 * k ^ m` for every `m`
and `ε_n < 1`, then `c ≤ n / ((1 - ε_n) log_k n)`. -/
theorem le_div_of_forall_mul_le {k c n : ℕ} (hk : 2 ≤ k)
    (hc : ∀ m : ℕ, m * c ≤ n + 2 * k ^ m) (hε : epsilon k n < 1) (hn : 2 ≤ n) :
    (c : ℝ) ≤ n / ((1 - epsilon k n) * Real.logb k n) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hLpos : 0 < Real.logb k n := Real.logb_pos hk1 (by exact_mod_cast hn)
  rw [le_div_iff₀ (mul_pos (by linarith) hLpos)]
  exact mul_one_sub_epsilon_le hk (mul_logb_sub_le_of_forall_mul_le hk hc)

/-- The slack `ε_n` tends to `0`. -/
theorem tendsto_epsilon {k : ℕ} (hk : 2 ≤ k) :
    Filter.Tendsto (epsilon k) Filter.atTop (nhds 0) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hg : Filter.Tendsto (fun y : ℝ => (Real.logb k y + 4) / y) Filter.atTop (nhds 0) := by
    have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Filter.Tendsto (fun y : ℝ => 4 / y) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    have h3 := (h1.div_const (Real.log k)).add h2
    simp only [zero_div, add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with y hy
    rw [Real.logb]
    field_simp
  have hL : Filter.Tendsto (fun n : ℕ => Real.logb k n) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop hk1).comp tendsto_natCast_atTop_atTop
  have := (tendsto_const_nhds (x := (1 : ℝ))).min (hg.comp hL)
  unfold epsilon
  simpa [Function.comp_def] using this

/-! ## The distinct-parsing bound -/

/-- **Distinct-parsing bound, logarithmic form.** A list of `c` pairwise distinct words of total
length `n` over an alphabet of size `k` satisfies `c * ⌊log_k c⌋ ≤ n + 2 * c`. -/
theorem length_mul_log_le_of_nodup [Fintype α] {ws : List (List α)} (hws : ws.Nodup) :
    ws.length * Nat.log (Fintype.card α) ws.length ≤ ws.flatten.length + 2 * ws.length :=
  mul_log_le_of_forall_mul_le fun hk m => mul_length_le_of_nodup hk hws m

/-- **Distinct-parsing bound, Cover–Thomas form** ([CoverThomas2006], Lemma 13.5.3, for any
alphabet size `k ≥ 2`). A list of `c` pairwise distinct words of total length `n` satisfies
`c * (log_k n - log_k log_k n - 4) ≤ n`. -/
theorem length_mul_logb_sub_le_of_nodup [Fintype α] (hα : 2 ≤ Fintype.card α)
    {ws : List (List α)} (hws : ws.Nodup) :
    (ws.length : ℝ) * (Real.logb (Fintype.card α) ws.flatten.length -
      Real.logb (Fintype.card α) (Real.logb (Fintype.card α) ws.flatten.length) - 4) ≤
      ws.flatten.length :=
  mul_logb_sub_le_of_forall_mul_le hα fun m => mul_length_le_of_nodup hα hws m

/-- **Distinct-parsing bound** ([CoverThomas2006], Lemma 13.5.3, for any alphabet size `k ≥ 2`).
A distinct parsing of a word of length `n ≥ 2` into `c` phrases has
`c ≤ n / ((1 - ε_n) log_k n)`, where `ε_n → 0` (`tendsto_epsilon`). -/
theorem length_le_div_of_nodup [Fintype α] (hα : 2 ≤ Fintype.card α)
    {ws : List (List α)} (hws : ws.Nodup) (hn : 2 ≤ ws.flatten.length)
    (hε : epsilon (Fintype.card α) ws.flatten.length < 1) :
    (ws.length : ℝ) ≤ ws.flatten.length /
      ((1 - epsilon (Fintype.card α) ws.flatten.length) *
        Real.logb (Fintype.card α) ws.flatten.length) :=
  le_div_of_forall_mul_le hα (fun m => mul_length_le_of_nodup hα hws m) hε hn

end Cslib.Algorithms.Lean.LempelZiv
