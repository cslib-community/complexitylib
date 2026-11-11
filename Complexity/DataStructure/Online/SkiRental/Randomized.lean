/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Online.Randomized
public import Complexity.DataStructure.Online.SkiRental
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Randomized ski rental: the ratio `1 / (1 - (1 - 1/B)^B) ≤ e/(e-1)`, tight

This file determines the best expected competitive ratio of randomized online strategies for the
discrete ski-rental problem `SkiRental.problem B` (integer purchase price `B ≥ 1`, one request per
ski day) against an **oblivious adversary**, in the model of
`Complexity.DataStructure.Online.Randomized`. The ratio is

  `randomizedRatio B = 1 / (1 - (1 - 1/B)^B) = B^B / (B^B - (B-1)^B)`
  (`randomizedRatio_eq`),

for example `4/3` for `B = 2` and `27/19` for `B = 3`. It is at most and tends to
`e/(e-1) ≈ 1.582` (`randomizedRatio_le`, `tendsto_randomizedRatio`; monotonicity in `B` is not
proved), and it is below the deterministic `2 - 1/B` of `Complexity.DataStructure.Online.SkiRental`
for every `B ≥ 2` (`randomizedRatio_lt_two_sub`).

**Upper bound.** The strategy `randomRentThenBuy B` rents for `t ∈ {0, …, B-1}` days and buys on
day `t + 1`, choosing `t` with probability proportional to
`buyWeight B t = (B-1)^(B-1-t) * B^t = B^(B-1) * (1 - 1/B)^(B-1-t)` (`buyWeight_eq`), i.e. it buys
on day `i` with probability proportional to `(1 - 1/B)^(B-i)`. Its expected cost on `n` ski days is
exactly `randomizedRatio B * min n B` (`expectedCost_randomRentThenBuy`), so it is
`randomizedRatio B`-competitive with no additive constant (`randomRentThenBuy_isCompetitive`), hence
`e/(e-1)`-competitive (`randomRentThenBuy_isCompetitive_exp`). This equalizing strategy is due to
[Karlin, Manasse, McGeoch, and Owicki, *Competitive randomized algorithms for nonuniform
problems*][KarlinManasseMcGeochOwicki1994]; see also the textbook treatment of rent-or-buy in
[Borodin and El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998].

**Lower bound.** Every randomized strategy has a request sequence with `OPT ≥ 1` and
`randomizedRatio B * OPT ≤ E[ALG]` (`exists_randomized_witness`), so no randomized strategy is
`(c, 0)`-competitive for any `c < randomizedRatio B` (`not_isCompetitive_of_lt`). The proof is the
easy direction of Yao's principle (`RandStrategy.exists_le_mul_expectedCost`) with the adversary
distribution `adversary B`: ski `k + 1` days with weight `(B-1)^k * B^(B-2-k)` for `k < B - 1`, and
`2B - 1` days with weight `(B-1)^(B-1)`. Against it every deterministic strategy, which on these
lengths behaves like a rent-then-buy strategy (`SkiRental.exists_rentThenBuy_cost_eq`), has mean
cost at least `randomizedRatio B` times the mean optimum (`le_sum_advWeight_mul_cost`,
`sum_advWeight_mul_min`).

As in the deterministic file, ratios are stated with additive constant `0`: the deterministic
break-even strategy is already `(1, B - 1)`-competitive (`breakEven_isCompetitive_one`), so with an
additive constant the ratio question is trivial. The asymptotic form of the lower bound (no
`c < e/(e-1)` is achievable with any fixed additive constant once `B` is large) is not formalized.

## Main definitions

* `SkiRental.randomizedRatio`: `1 / (1 - (1 - 1/B)^B)`.
* `SkiRental.buyWeight`, `SkiRental.rentDays`, `SkiRental.randomRentThenBuy`: the equalizing
  randomized strategy.
* `SkiRental.advDays`, `SkiRental.advWeight`, `SkiRental.adversary`: the matching oblivious
  adversary distribution.

## Main results

* `randomizedRatio_eq`, `randomizedRatio_le`, `tendsto_randomizedRatio`,
  `randomizedRatio_lt_two_sub`: the ratio is `B^B / (B^B - (B-1)^B) ≤ e/(e-1)`, tends to `e/(e-1)`,
  and beats `2 - 1/B`.
* `expectedCost_randomRentThenBuy`, `randomRentThenBuy_isCompetitive`,
  `randomRentThenBuy_isCompetitive_exp`: the upper bound.
* `exists_randomized_witness`, `not_isCompetitive_of_lt`: the matching lower bound.

## References

* [A. R. Karlin, M. S. Manasse, L. A. McGeoch, and S. Owicki, *Competitive randomized algorithms
  for nonuniform problems*][KarlinManasseMcGeochOwicki1994]
* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

open scoped ENNReal Topology
open Filter Finset

public section

namespace Cslib.DataStructure.Online.SkiRental

/-! ### The ratio -/

/-- The optimal randomized competitive ratio for discrete ski rental with purchase price `B`:
`1 / (1 - (1 - 1/B)^B)`. -/
noncomputable def randomizedRatio (B : ℕ) : ℝ := 1 / (1 - (1 - 1 / (B : ℝ)) ^ B)

/-- `randomizedRatio B = B^B / (B^B - (B-1)^B)`; for instance `4/3` at `B = 2`. -/
theorem randomizedRatio_eq {B : ℕ} (hB : 1 ≤ B) :
    randomizedRatio B = (B : ℝ) ^ B / ((B : ℝ) ^ B - ((B : ℝ) - 1) ^ B) := by
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  rw [randomizedRatio, one_sub_div hB0, div_pow, one_sub_div (pow_ne_zero _ hB0), one_div_div]

/-- `randomizedRatio B` as an extended real is the ratio of the natural numbers `B^B` and
`B^B - (B-1)^B`. -/
theorem ofReal_randomizedRatio {B : ℕ} (hB : 1 ≤ B) :
    ENNReal.ofReal (randomizedRatio B) =
      ((B ^ B : ℕ) : ℝ≥0∞) / ((B ^ B - (B - 1) ^ B : ℕ) : ℝ≥0∞) := by
  have hlt : (B - 1) ^ B < B ^ B := Nat.pow_lt_pow_left (by omega) (by omega)
  have hcast : (((B ^ B - (B - 1) ^ B : ℕ)) : ℝ) = (B : ℝ) ^ B - ((B : ℝ) - 1) ^ B := by
    rw [Nat.cast_sub hlt.le]
    push_cast [Nat.cast_sub hB]
    ring
  have hpos : (0 : ℝ) < ((B ^ B - (B - 1) ^ B : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hlt
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos hpos,
    hcast, randomizedRatio_eq hB, Nat.cast_pow]

private theorem one_div_one_sub_exp_neg_one :
    1 / (1 - Real.exp (-1)) = Real.exp 1 / (Real.exp 1 - 1) := by
  have h1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
  rw [Real.exp_neg]
  field_simp [show Real.exp 1 - 1 ≠ 0 by linarith]

/-- `randomizedRatio B ≤ e/(e-1)`, from `(1 - 1/B)^B ≤ e⁻¹`. -/
theorem randomizedRatio_le {B : ℕ} (hB : 1 ≤ B) :
    randomizedRatio B ≤ Real.exp 1 / (Real.exp 1 - 1) := by
  have hle : (1 - 1 / (B : ℝ)) ^ B ≤ Real.exp (-1) :=
    Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hB)
  have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [randomizedRatio, ← one_div_one_sub_exp_neg_one]
  gcongr

/-- `randomizedRatio B → e/(e-1)` as `B → ∞`, from `(1 - 1/B)^B → e⁻¹`. -/
theorem tendsto_randomizedRatio :
    Tendsto randomizedRatio atTop (𝓝 (Real.exp 1 / (Real.exp 1 - 1))) := by
  have h : Tendsto (fun B : ℕ => (1 - 1 / (B : ℝ)) ^ B) atTop (𝓝 (Real.exp (-1))) := by
    have := Real.tendsto_one_add_div_pow_exp (-1)
    simpa only [neg_div, ← sub_eq_add_neg] using this
  have hne : 1 - Real.exp (-1) ≠ 0 := by
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  rw [← one_div_one_sub_exp_neg_one]
  exact tendsto_const_nhds.div (tendsto_const_nhds.sub h) hne

/-- For `B ≥ 2` randomization helps: `randomizedRatio B < 2 - 1/B`, the optimal deterministic
ratio (`SkiRental.breakEven_mul_cost_le`, `SkiRental.exists_ratio_violation_of_lt`). -/
theorem randomizedRatio_lt_two_sub {B : ℕ} (hB : 2 ≤ B) :
    randomizedRatio B < 2 - 1 / (B : ℝ) := by
  rcases hB.eq_or_lt with rfl | hB3
  · rw [randomizedRatio_eq (by norm_num)]
    norm_num
  · have he := Real.exp_one_gt_d9
    have h53 : Real.exp 1 / (Real.exp 1 - 1) < 5 / 3 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have hB' : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have h13 : 1 / (B : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hB'
    linarith [randomizedRatio_le (B := B) (by omega)]

/-! ### Arithmetic of the two distributions

Writing `B = m + 1`, these identities are the finite geometric sums behind the equalizing
strategy and the equalizing adversary. -/

private theorem sum_buy_aux (m n : ℕ) (hn : n ≤ m + 1) :
    ∑ t ∈ range n, m ^ (m - t) * (m + 1) ^ t + m ^ (m + 1) = (m + 1) ^ n * m ^ (m + 1 - n) := by
  induction n with
  | zero => rw [Finset.sum_range_zero, zero_add, pow_zero, one_mul, Nat.sub_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
    rw [show n + j - n = j by omega, show n + j + 1 - n = j + 1 by omega,
      show n + j + 1 - (n + 1) = j by omega]
    ring

private theorem sum_buy_mul_aux (m n : ℕ) (hn : n ≤ m + 1) :
    ∑ t ∈ range n, m ^ (m - t) * (m + 1) ^ t * (t + (m + 1)) =
      n * ((m + 1) ^ n * m ^ (m + 1 - n)) := by
  induction n with
  | zero => rw [Finset.sum_range_zero, zero_mul]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, m = n + j := ⟨m - n, by omega⟩
    rw [show n + j - n = j by omega, show n + j + 1 - n = j + 1 by omega,
      show n + j + 1 - (n + 1) = j by omega]
    ring

private theorem sum_Ico_buy_aux (m n : ℕ) (hn : n ≤ m + 1) :
    ∑ t ∈ Ico n (m + 1), m ^ (m - t) * (m + 1) ^ t + (m + 1) ^ n * m ^ (m + 1 - n) =
      (m + 1) ^ (m + 1) := by
  have h1 := sum_buy_aux m n hn
  have h2 := sum_buy_aux m (m + 1) le_rfl
  rw [← Finset.sum_range_add_sum_Ico _ hn, Nat.sub_self, pow_zero, mul_one] at h2
  omega

/-- Mean cost identity for the equalizing strategy: against `n ≤ B` ski days, the weighted cost
of the threshold strategies is `B^B * n`. -/
private theorem sum_buy_mul_cost_aux (m n : ℕ) (hn : n ≤ m + 1) :
    ∑ t ∈ range (m + 1), m ^ (m - t) * (m + 1) ^ t * (if n ≤ t then n else t + (m + 1)) =
      (m + 1) ^ (m + 1) * n := by
  have hlo : ∑ t ∈ range n, m ^ (m - t) * (m + 1) ^ t * (if n ≤ t then n else t + (m + 1)) =
      ∑ t ∈ range n, m ^ (m - t) * (m + 1) ^ t * (t + (m + 1)) :=
    Finset.sum_congr rfl fun t ht => by
      rw [ite_eq_right (by rw [Finset.mem_range] at ht; omega)]
  have hhi : ∑ t ∈ Ico n (m + 1), m ^ (m - t) * (m + 1) ^ t * (if n ≤ t then n else t + (m + 1)) =
      (∑ t ∈ Ico n (m + 1), m ^ (m - t) * (m + 1) ^ t) * n := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun t ht => by
      rw [ite_eq_left (by rw [Finset.mem_Ico] at ht; omega)]
  rw [← Finset.sum_range_add_sum_Ico _ hn, hlo, hhi, sum_buy_mul_aux m n hn,
    ← sum_Ico_buy_aux m n hn]
  ring

private theorem sum_adv_aux (m n : ℕ) (hn : n ≤ m) :
    ∑ k ∈ range n, m ^ k * (m + 1) ^ (m - 1 - k) + m ^ n * (m + 1) ^ (m - n) = (m + 1) ^ m := by
  induction n with
  | zero => rw [Finset.sum_range_zero, zero_add, pow_zero, one_mul, Nat.sub_zero]
  | succ n ih =>
    rw [← ih (by omega), Finset.sum_range_succ, add_assoc]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, m = n + 1 + j := ⟨m - n - 1, by omega⟩
    rw [show n + 1 + j - 1 - n = j by omega, show n + 1 + j - (n + 1) = j by omega,
      show n + 1 + j - n = j + 1 by omega]
    ring

private theorem sum_adv_mul_aux (m n : ℕ) (hn : n ≤ m) :
    ∑ k ∈ range n, m ^ k * (m + 1) ^ (m - 1 - k) * (k + 1) +
      (n + m + 1) * (m ^ n * (m + 1) ^ (m - n)) = (m + 1) ^ (m + 1) := by
  induction n with
  | zero => rw [Finset.sum_range_zero, Nat.sub_zero]; ring
  | succ n ih =>
    rw [← ih (by omega), Finset.sum_range_succ, add_assoc]
    congr 1
    obtain ⟨j, rfl⟩ : ∃ j, m = n + 1 + j := ⟨m - n - 1, by omega⟩
    rw [show n + 1 + j - 1 - n = j by omega, show n + 1 + j - (n + 1) = j by omega,
      show n + 1 + j - n = j + 1 by omega]
    ring

/-- Mean cost bound for the equalizing adversary: against the threshold strategy that rents for
`t` days, the weighted cost is at least `B^B`, with equality for `t < B`. -/
private theorem le_sum_adv_mul_cost_aux (m t : ℕ) :
    (m + 1) ^ (m + 1) ≤ m ^ m * (if 2 * m + 1 ≤ t then 2 * m + 1 else t + (m + 1)) +
      ∑ k ∈ range m, m ^ k * (m + 1) ^ (m - 1 - k) *
        (if k + 1 ≤ t then k + 1 else t + (m + 1)) := by
  rcases lt_or_ge t m with htm | hmt
  · -- the strategy buys before the long sequence ends: equality
    have hb := sum_adv_mul_aux m t htm.le
    have ha := sum_adv_aux m t htm.le
    have ha' := sum_adv_aux m m le_rfl
    rw [← Finset.sum_range_add_sum_Ico _ htm.le, Nat.sub_self, pow_zero, mul_one] at ha'
    have hlo : ∑ k ∈ range t, m ^ k * (m + 1) ^ (m - 1 - k) *
        (if k + 1 ≤ t then k + 1 else t + (m + 1)) =
        ∑ k ∈ range t, m ^ k * (m + 1) ^ (m - 1 - k) * (k + 1) :=
      Finset.sum_congr rfl fun k hk => by
        rw [ite_eq_left (by rw [Finset.mem_range] at hk; omega)]
    have hhi : ∑ k ∈ Ico t m, m ^ k * (m + 1) ^ (m - 1 - k) *
        (if k + 1 ≤ t then k + 1 else t + (m + 1)) =
        (∑ k ∈ Ico t m, m ^ k * (m + 1) ^ (m - 1 - k)) * (t + (m + 1)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k hk => by
        rw [ite_eq_right (by rw [Finset.mem_Ico] at hk; omega)]
    rw [ite_eq_right (by omega), ← Finset.sum_range_add_sum_Ico _ htm.le, hlo, hhi]
    have htail : ∑ k ∈ Ico t m, m ^ k * (m + 1) ^ (m - 1 - k) + m ^ m =
        m ^ t * (m + 1) ^ (m - t) := by omega
    rw [← htail] at hb
    rw [← hb]
    apply le_of_eq
    ring
  · -- the strategy rents through every short sequence: it pays at least `2B - 1` on the long one
    have hb := sum_adv_mul_aux m m le_rfl
    rw [Nat.sub_self, pow_zero, mul_one] at hb
    rw [Finset.sum_congr rfl (g := fun k => m ^ k * (m + 1) ^ (m - 1 - k) * (k + 1))
        (fun k hk => by rw [ite_eq_left (by rw [Finset.mem_range] at hk; omega)])]
    set c := if 2 * m + 1 ≤ t then 2 * m + 1 else t + (m + 1) with hc
    have hc' : 2 * m + 1 ≤ c := by rw [hc]; split_ifs <;> omega
    have h1 := Nat.mul_le_mul_left (m ^ m) hc'
    have h2 : (m + m + 1) * m ^ m = m ^ m * (2 * m + 1) := by ring
    omega

private theorem sum_natCast_div {ι : Type*} [Fintype ι] (w : ι → ℕ) {D : ℕ}
    (hD : ∑ i, w i = D) (hD0 : D ≠ 0) :
    ∑ i, ((w i : ℕ) : ℝ≥0∞) / D = 1 := by
  rw [← ENNReal.sum_div, ← Nat.cast_sum, hD]
  exact ENNReal.div_self (by exact_mod_cast hD0) (ENNReal.natCast_ne_top D)

private theorem tsum_natCast_div_mul {ι : Type*} [Fintype ι] (w f : ι → ℕ) (D : ℕ) :
    ∑' i, ((w i : ℕ) : ℝ≥0∞) / D * (f i : ℝ≥0∞) = ((∑ i, w i * f i : ℕ) : ℝ≥0∞) / D := by
  rw [tsum_fintype, Nat.cast_sum, ENNReal.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_mul, ENNReal.mul_div_right_comm]

/-! ### The equalizing randomized strategy -/

/-- Unnormalized probability that the equalizing strategy rents for `t < B` days and buys on day
`t + 1`: `(B-1)^(B-1-t) * B^t`. -/
@[expose]
def buyWeight (B t : ℕ) : ℕ := (B - 1) ^ (B - 1 - t) * B ^ t

/-- `buyWeight B t` is proportional to `(1 - 1/B)^(B-1-t)`, i.e. buying on day `i = t + 1` has
weight proportional to `(1 - 1/B)^(B-i)`. -/
theorem buyWeight_eq {B t : ℕ} (hB : 1 ≤ B) (ht : t < B) :
    (buyWeight B t : ℝ) = (B : ℝ) ^ (B - 1) * (1 - 1 / (B : ℝ)) ^ (B - 1 - t) := by
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hpow : (B : ℝ) ^ (B - 1) = (B : ℝ) ^ t * (B : ℝ) ^ (B - 1 - t) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, buyWeight, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hB, Nat.cast_one,
    one_sub_div hB0, div_pow]
  field_simp

/-- The weights sum to `B^B - (B-1)^B`. -/
theorem sum_range_buyWeight (B : ℕ) [NeZero B] :
    ∑ t ∈ range B, buyWeight B t = B ^ B - (B - 1) ^ B := by
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos B)).symm⟩
  have := sum_buy_aux m (m + 1) le_rfl
  simp only [buyWeight, Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one] at this ⊢
  omega

private theorem buyDenom_pos (B : ℕ) [NeZero B] : 0 < B ^ B - (B - 1) ^ B :=
  Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (Nat.sub_lt (NeZero.pos B) one_pos) (NeZero.ne B))

/-- The equalizing distribution of the number of rented days `t < B`. -/
noncomputable def rentDays (B : ℕ) [NeZero B] : PMF (Fin B) :=
  PMF.ofFintype (fun t => (buyWeight B t : ℝ≥0∞) / ((B ^ B - (B - 1) ^ B : ℕ) : ℝ≥0∞))
    (sum_natCast_div (fun t : Fin B => buyWeight B t)
      ((Fin.sum_univ_eq_sum_range (buyWeight B) B).trans (sum_range_buyWeight B))
      (buyDenom_pos B).ne')

@[simp]
theorem rentDays_apply (B : ℕ) [NeZero B] (t : Fin B) :
    rentDays B t = (buyWeight B t : ℝ≥0∞) / ((B ^ B - (B - 1) ^ B : ℕ) : ℝ≥0∞) := by
  rw [rentDays, PMF.ofFintype_apply]

/-- The equalizing randomized ski-rental strategy of [KarlinManasseMcGeochOwicki1994]: draw the
number of rented days `t` from `rentDays B`, then rent for `t` days and buy on day `t + 1`. -/
noncomputable def randomRentThenBuy (B : ℕ) [NeZero B] : RandStrategy (problem B) :=
  (rentDays B).map fun t : Fin B => rentThenBuy B t

/-- **Exact expected cost of the equalizing strategy.** On `n` ski days `randomRentThenBuy B`
pays `randomizedRatio B * min n B` in expectation, i.e. exactly `randomizedRatio B` times the
offline optimum. -/
theorem expectedCost_randomRentThenBuy (B : ℕ) [NeZero B] (reqs : List Unit) :
    RandStrategy.expectedCost (randomRentThenBuy B) false reqs =
      ENNReal.ofReal (randomizedRatio B) * (min reqs.length B : ℕ) := by
  have hB : 1 ≤ B := NeZero.pos B
  have hcost : ∀ t : Fin B, ((rentThenBuy B t).cost false reqs : ℝ≥0∞) =
      ((if reqs.length ≤ (t : ℕ) then reqs.length else t + B : ℕ) : ℝ≥0∞) := fun t => by
    rw [cost_rentThenBuy]
  rw [randomRentThenBuy, RandStrategy.expectedCost_map]
  simp only [rentDays_apply, hcost]
  rw [tsum_natCast_div_mul, Fin.sum_univ_eq_sum_range
    (fun t => buyWeight B t * (if reqs.length ≤ t then reqs.length else t + B)) B]
  have hsum : ∑ t ∈ range B, buyWeight B t * (if reqs.length ≤ t then reqs.length else t + B) =
      B ^ B * min reqs.length B := by
    obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
    simp only [buyWeight, Nat.add_sub_cancel]
    rcases le_or_gt reqs.length (m + 1) with hn | hn
    · rw [Nat.min_eq_left hn]
      exact sum_buy_mul_cost_aux m _ hn
    · -- beyond `B` days every threshold strategy has already bought
      rw [Nat.min_eq_right hn.le, ← sum_buy_mul_cost_aux m (m + 1) le_rfl]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hsum, ofReal_randomizedRatio hB, Nat.cast_mul, ENNReal.mul_div_right_comm]

/-- **Upper bound** [KarlinManasseMcGeochOwicki1994]: against every valid offline schedule, the
expected cost of `randomRentThenBuy B` is at most `randomizedRatio B` times the schedule's cost. -/
theorem expectedCost_randomRentThenBuy_le {B : ℕ} [NeZero B] {reqs : List Unit}
    {states : List Bool} (hv : (problem B).ValidSchedule false reqs states) :
    RandStrategy.expectedCost (randomRentThenBuy B) false reqs ≤
      ENNReal.ofReal (randomizedRatio B) * (problem B).scheduleCost false reqs states := by
  rw [expectedCost_randomRentThenBuy]
  gcongr
  exact min_le_scheduleCost hv

/-- `randomRentThenBuy B` is `randomizedRatio B`-competitive against an oblivious adversary, with
no additive constant. -/
theorem randomRentThenBuy_isCompetitive (B : ℕ) [NeZero B] :
    RandStrategy.IsCompetitive (randomRentThenBuy B) (ENNReal.ofReal (randomizedRatio B)) 0 := by
  rintro s₀ rfl reqs states hv
  rw [add_zero]
  exact expectedCost_randomRentThenBuy_le hv

/-- `randomRentThenBuy B` is `e/(e-1)`-competitive against an oblivious adversary, for every
purchase price `B ≥ 1`. -/
theorem randomRentThenBuy_isCompetitive_exp (B : ℕ) [NeZero B] :
    RandStrategy.IsCompetitive (randomRentThenBuy B)
      (ENNReal.ofReal (Real.exp 1 / (Real.exp 1 - 1))) 0 :=
  (randomRentThenBuy_isCompetitive B).mono
    (ENNReal.ofReal_le_ofReal (randomizedRatio_le (NeZero.pos B))) le_rfl

/-! ### The matching lower bound -/

/-- Number of ski days chosen by the adversary: `k + 1` for `some k` with `k < B - 1`, and
`2B - 1` for `none`. -/
@[expose]
def advDays (B : ℕ) : Option (Fin (B - 1)) → ℕ
  | none => 2 * B - 1
  | some k => k + 1

/-- Unnormalized adversary weights: `(B-1)^k * B^(B-2-k)` for `k + 1` days, and `(B-1)^(B-1)` for
`2B - 1` days. -/
@[expose]
def advWeight (B : ℕ) : Option (Fin (B - 1)) → ℕ
  | none => (B - 1) ^ (B - 1)
  | some k => (B - 1) ^ (k : ℕ) * B ^ (B - 1 - 1 - k)

private theorem sum_adv_eq (m : ℕ) (g : ℕ → ℕ) :
    ∑ o, advWeight (m + 1) o * g (advDays (m + 1) o) =
      m ^ m * g (2 * m + 1) + ∑ k ∈ range m, m ^ k * (m + 1) ^ (m - 1 - k) * g (k + 1) := by
  have h2 : ∑ i : Fin (m + 1 - 1), advWeight (m + 1) (some i) * g (advDays (m + 1) (some i)) =
      ∑ k ∈ range (m + 1 - 1), m ^ k * (m + 1) ^ (m - 1 - k) * g (k + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp only [advWeight, advDays, Nat.add_sub_cancel]
  rw [Fintype.sum_option, h2]
  congr 1

/-- The adversary weights sum to `B^(B-1)`. -/
theorem sum_advWeight (B : ℕ) [NeZero B] : ∑ o, advWeight B o = B ^ (B - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by have := NeZero.pos B; omega⟩
  have h := sum_adv_eq m (fun _ => 1)
  simp only [mul_one] at h
  have h2 := sum_adv_aux m m le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at h2
  rw [h, Nat.add_sub_cancel]
  omega

/-- Weighted offline optimum under the adversary: `∑ advWeight * min days B = B^B - (B-1)^B`. -/
theorem sum_advWeight_mul_min (B : ℕ) [NeZero B] :
    ∑ o, advWeight B o * min (advDays B o) B = B ^ B - (B - 1) ^ B := by
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by have := NeZero.pos B; omega⟩
  rw [sum_adv_eq m (fun n => min n (m + 1))]
  have hb := sum_adv_mul_aux m m le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hb
  have hmin : ∑ k ∈ range m, m ^ k * (m + 1) ^ (m - 1 - k) * min (k + 1) (m + 1) =
      ∑ k ∈ range m, m ^ k * (m + 1) ^ (m - 1 - k) * (k + 1) :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_range] at hk
      rw [Nat.min_eq_left (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [hmin, Nat.min_eq_right (by omega)]
  have : (m + m + 1) * m ^ m = m ^ m * (m + 1) + m ^ (m + 1) := by ring
  omega

/-- **Every deterministic strategy pays at least `B^B` against the weighted adversary**, i.e. at
least `randomizedRatio B` times the weighted optimum `B^B - (B-1)^B`. -/
theorem le_sum_advWeight_mul_cost (B : ℕ) [NeZero B] (A : DetStrategy (problem B)) :
    B ^ B ≤ ∑ o, advWeight B o * A.cost false (List.replicate (advDays B o) ()) := by
  obtain ⟨t, ht⟩ := exists_rentThenBuy_cost_eq A (2 * B - 1)
  have hle : ∀ o, advDays B o ≤ 2 * B - 1 := by
    rintro (_ | k)
    · exact le_rfl
    · have := k.isLt
      simp only [advDays]
      omega
  have hcost : ∀ o, A.cost false (List.replicate (advDays B o) ()) =
      if advDays B o ≤ t then advDays B o else t + B := fun o => by
    rw [ht _ (hle o), cost_rentThenBuy, List.length_replicate]
  simp only [hcost]
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by have := NeZero.pos B; omega⟩
  rw [sum_adv_eq m (fun n => if n ≤ t then n else t + (m + 1))]
  exact le_sum_adv_mul_cost_aux m t

private theorem one_le_min_advDays (B : ℕ) [NeZero B] (o : Option (Fin (B - 1))) :
    1 ≤ min (advDays B o) B := by
  have := NeZero.pos B
  cases o with
  | none => simp only [advDays]; omega
  | some k => simp only [advDays]; omega

/-- The oblivious adversary distribution on ski-day counts, with probabilities
`advWeight B o / B^(B-1)`. -/
noncomputable def adversary (B : ℕ) [NeZero B] : PMF (Option (Fin (B - 1))) :=
  PMF.ofFintype (fun o => (advWeight B o : ℝ≥0∞) / ((B ^ (B - 1) : ℕ) : ℝ≥0∞))
    (sum_natCast_div (advWeight B) (sum_advWeight B) (pow_pos (NeZero.pos B) _).ne')

@[simp]
theorem adversary_apply (B : ℕ) [NeZero B] (o : Option (Fin (B - 1))) :
    adversary B o = (advWeight B o : ℝ≥0∞) / ((B ^ (B - 1) : ℕ) : ℝ≥0∞) := by
  rw [adversary, PMF.ofFintype_apply]

/-- **Lower bound.** Every randomized ski-rental strategy `μ` has, against an oblivious adversary,
a request sequence and a valid offline schedule with `OPT ≥ 1` and
`randomizedRatio B * OPT ≤ E_μ[ALG]`. -/
theorem exists_randomized_witness (B : ℕ) [NeZero B] (μ : RandStrategy (problem B)) :
    ∃ reqs states, (problem B).ValidSchedule false reqs states ∧
      1 ≤ (problem B).scheduleCost false reqs states ∧
      ENNReal.ofReal (randomizedRatio B) * (problem B).scheduleCost false reqs states ≤
        RandStrategy.expectedCost μ false reqs := by
  have hB : 1 ≤ B := NeZero.pos B
  have hV0 : ((B ^ (B - 1) : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos hB _).ne'
  obtain ⟨o, -, ho⟩ := RandStrategy.exists_le_mul_expectedCost (adversary B) false
    (fun o => List.replicate (advDays B o) ())
    (fun o => ((B ^ B * min (advDays B o) B : ℕ) : ℝ≥0∞))
    ((B ^ B - (B - 1) ^ B : ℕ) : ℝ≥0∞)
    (by
      simp only [adversary_apply]
      rw [tsum_natCast_div_mul]
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hV0)
    (fun A => by
      simp only [adversary_apply]
      rw [tsum_natCast_div_mul, tsum_natCast_div_mul, ← mul_div_assoc, ← Nat.cast_mul]
      have h1 : ∑ o, advWeight B o * (B ^ B * min (advDays B o) B) =
          B ^ B * (B ^ B - (B - 1) ^ B) := by
        rw [← sum_advWeight_mul_min B, Finset.mul_sum]
        exact Finset.sum_congr rfl fun o _ => by ring
      have key : ∑ o, advWeight B o * (B ^ B * min (advDays B o) B) ≤
          (B ^ B - (B - 1) ^ B) *
            ∑ o, advWeight B o * A.cost false (List.replicate (advDays B o) ()) := by
        rw [h1, mul_comm]
        exact Nat.mul_le_mul_left _ (le_sum_advWeight_mul_cost B A)
      exact ENNReal.div_le_div_right (by exact_mod_cast key) _)
    μ
  dsimp only at ho
  obtain ⟨states, hv, hcost⟩ := exists_optimal_schedule B (List.replicate (advDays B o) ())
  rw [List.length_replicate] at hcost
  refine ⟨_, states, hv, hcost ▸ one_le_min_advDays B o, ?_⟩
  rw [hcost, ofReal_randomizedRatio hB, ← ENNReal.mul_div_right_comm, ← Nat.cast_mul]
  exact ENNReal.div_le_of_le_mul (ho.trans_eq (mul_comm _ _))

/-- No randomized ski-rental strategy is `(c, 0)`-competitive against an oblivious adversary for
any `c < randomizedRatio B`; with `randomRentThenBuy_isCompetitive`, `randomizedRatio B` is the
optimal randomized ratio. -/
theorem not_isCompetitive_of_lt {B : ℕ} [NeZero B] (μ : RandStrategy (problem B)) {c : ℝ≥0∞}
    (hc : c < ENNReal.ofReal (randomizedRatio B)) : ¬ RandStrategy.IsCompetitive μ c 0 := by
  intro h
  obtain ⟨reqs, states, hv, hpos, hle⟩ := exists_randomized_witness B μ
  have h1 := h false rfl reqs states hv
  rw [add_zero] at h1
  have hne : ((problem B).scheduleCost false reqs states : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hpos)
  have hlt : c * ((problem B).scheduleCost false reqs states : ℝ≥0∞) <
      ENNReal.ofReal (randomizedRatio B) * (problem B).scheduleCost false reqs states := by
    rw [mul_comm c, mul_comm (ENNReal.ofReal _)]
    exact ENNReal.mul_lt_mul_right hne (ENNReal.natCast_ne_top _) hc
  exact absurd (hle.trans h1) (not_le.mpr hlt)

end Cslib.DataStructure.Online.SkiRental
