/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.DDGTree
public import Complexity.Probability.Entropy
import Complexity.Probability.PMF.ToReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Knuth–Yao entropy bounds for sampling from fair coins

Every DDG tree generating a distribution `p` on a finite type reads at least `H(p)` fair bits in
expectation, and the Knuth–Yao tree `knuthYao p` reads fewer than `H(p) + 2`
([KnuthYao1976]; [CoverThomas2006], Theorems 5.11.1 and 5.11.3).

`knuthYao p` places a leaf labelled `a` at depth `k` exactly when the `k`-th binary digit
`⌊2ᵏ p a⌋ mod 2` of `p a` is `1`. Equivalently, it outputs `a` within `k` flips with probability
`⌊2ᵏ p a⌋ / 2ᵏ`. Its stopping time is stochastically smallest. For every generating tree `T` and
every `n`, `P(T_KY > n) ≤ P(T > n)`, because after `n` fair bits `T` can only have produced `a`
with dyadic probability `c / 2ⁿ ≤ p a`, so `c ≤ ⌊2ⁿ p a⌋`. Hence `knuthYao p` minimizes the
expected number of flips. Its expected cost is `∑ₐ ν(p a)`, where
`ν(x) = ∑ₙ (x - ⌊2ⁿ x⌋ / 2ⁿ)` is the sum of the binary-truncation errors of `x`. The bounds
`x log₂ (1 / x) ≤ ν(x) < x log₂ (1 / x) + 2x` for `0 < x ≤ 1` then give both entropy bounds.
Equality `ν(x) = x log₂ (1 / x)` holds exactly when `x` is `0` or a power of `1/2`, which
characterizes the dyadic case.

The entropy bounds are stated for distributions on a `Fintype`. The countable-support and
infinite-entropy cases of [CoverThomas2006], Section 5.11 are not formalized.

## Main definitions

* `Cslib.Probability.DDGTree.truncErr`, `.knuthYaoCost`: binary-truncation error and its sum.
* `Cslib.Probability.DDGTree.knuthYao`: the Knuth–Yao tree of a finite distribution.

## Main results

* `Cslib.Probability.DDGTree.knuthYao_generates`: the Knuth–Yao tree generates `p`.
* `Cslib.Probability.DDGTree.isLeast_expectedFlips_knuthYao`: it minimizes the expected number of
  flips among all trees generating `p`.
* `Cslib.Probability.DDGTree.entropy_le_expectedFlips`: `H(p) ≤ E[T]` for every generating tree.
* `Cslib.Probability.DDGTree.expectedFlips_knuthYao_lt`: `E[T_KY] < H(p) + 2`.
* `Cslib.Probability.DDGTree.exists_generates_expectedFlips_eq_entropy_iff`: some tree attains
  `E[T] = H(p)` exactly when every positive `p a` is a power of `1/2`.

## References

* [D. E. Knuth, A. C. Yao, *The complexity of nonuniform random number generation*][KnuthYao1976].
* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Section 5.11,
  Theorems 5.11.1–5.11.3.
-/

public section

open scoped ENNReal
open Filter Topology

namespace Cslib.Probability.DDGTree

/-! ## Binary-truncation errors -/

/-- Error of the `n`-digit binary truncation of `x`: `x - ⌊2ⁿ x⌋ / 2ⁿ`. -/
@[expose] noncomputable def truncErr (x : ℝ) (n : ℕ) : ℝ := x - ⌊(2 : ℝ) ^ n * x⌋₊ / 2 ^ n

/-- The Knuth–Yao cost `∑ₙ (x - ⌊2ⁿ x⌋ / 2ⁿ)` of a probability `x`. It is the contribution of
an outcome of probability `x` to the expected number of flips of the Knuth–Yao tree. -/
@[expose] noncomputable def knuthYaoCost (x : ℝ) : ℝ := ∑' n, truncErr x n

section Real

variable {x : ℝ}

theorem truncErr_eq (n : ℕ) :
    truncErr x n = ((2 : ℝ) ^ n * x - ⌊(2 : ℝ) ^ n * x⌋₊) * 2⁻¹ ^ n := by
  rw [truncErr, inv_pow, sub_mul, mul_comm ((2 : ℝ) ^ n) x, mul_assoc,
    mul_inv_cancel₀ (by positivity), mul_one, div_eq_mul_inv]

theorem truncErr_nonneg (hx : 0 ≤ x) (n : ℕ) : 0 ≤ truncErr x n := by
  rw [truncErr_eq]
  exact mul_nonneg (sub_nonneg.mpr (Nat.floor_le (by positivity))) (by positivity)

theorem truncErr_lt (n : ℕ) : truncErr x n < 2⁻¹ ^ n := by
  rw [truncErr_eq]
  have h := Nat.lt_floor_add_one ((2 : ℝ) ^ n * x)
  have hpos : (0 : ℝ) < 2⁻¹ ^ n := by positivity
  nlinarith

theorem truncErr_le (n : ℕ) : truncErr x n ≤ x := by
  rw [truncErr, sub_le_self_iff]
  positivity

theorem truncErr_eq_self {n : ℕ} (h : (2 : ℝ) ^ n * x < 1) : truncErr x n = x := by
  rw [truncErr, Nat.floor_eq_zero.mpr h]
  simp

theorem summable_truncErr (hx : 0 ≤ x) : Summable (truncErr x) :=
  Summable.of_nonneg_of_le (truncErr_nonneg hx) (fun n => (truncErr_lt n).le)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem knuthYaoCost_nonneg (hx : 0 ≤ x) : 0 ≤ knuthYaoCost x :=
  tsum_nonneg (truncErr_nonneg hx)

@[simp] theorem knuthYaoCost_zero : knuthYaoCost 0 = 0 := by
  simp [knuthYaoCost, truncErr]

/-- The exponent `m` with `2⁻ᵐ ≤ x < 2⁻ᵐ⁺¹`. -/
private theorem exists_scale (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ m : ℕ, 1 ≤ (2 : ℝ) ^ m * x ∧ (2 : ℝ) ^ m * x < 2 := by
  classical
  have hex : ∃ m : ℕ, 1 ≤ (2 : ℝ) ^ m * x := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x⁻¹ (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    rw [inv_lt_iff_one_lt_mul₀ hx] at hm
    linarith [mul_comm x ((2 : ℝ) ^ m)]
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hm : Nat.find hex with _ | m
  · simp only [pow_zero, one_mul]; linarith
  · have hlt := Nat.find_min hex (show m < Nat.find hex by omega)
    rw [not_le] at hlt
    rw [pow_succ]
    nlinarith

private theorem negMulLogb_le (hx : 0 < x) {m : ℕ} (hm : 1 ≤ (2 : ℝ) ^ m * x) :
    x * -Real.logb 2 x ≤ m * x := by
  have hlog : -(m : ℝ) ≤ Real.logb 2 x := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hx, Real.rpow_neg (by norm_num),
      Real.rpow_natCast, inv_le_iff_one_le_mul₀ (by positivity)]
    linarith [mul_comm x ((2 : ℝ) ^ m)]
  nlinarith

private theorem negMulLogb_gt (hx : 0 < x) {m : ℕ} (hm : (2 : ℝ) ^ m * x < 2) :
    ((m : ℝ) - 1) * x < x * -Real.logb 2 x := by
  have hlog : Real.logb 2 x < 1 - (m : ℝ) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hx, Real.rpow_sub (by norm_num),
      Real.rpow_one, Real.rpow_natCast, lt_div_iff₀ (by positivity)]
    linarith [mul_comm x ((2 : ℝ) ^ m)]
  nlinarith

/-- The first `m` truncations of `x < 2⁻ᵐ⁺¹` are `0`, so they contribute `m x`. -/
private theorem mul_le_knuthYaoCost (hx : 0 < x) {m : ℕ} (hm : (2 : ℝ) ^ m * x < 2) :
    m * x ≤ knuthYaoCost x := by
  have hsum := (summable_truncErr hx.le).sum_le_tsum (Finset.range m)
    (fun n _ => truncErr_nonneg hx.le n)
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_congr rfl (fun n hn => truncErr_eq_self ?_)]
  · simp
  · have hn : n + 1 ≤ m := Finset.mem_range.mp hn
    have h2 : (2 : ℝ) ^ (n + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hn
    rw [pow_succ] at h2
    nlinarith

/-- For `x ≥ 2⁻ᵐ`, the truncation errors are at most `x` for `n < m`, at most `x - 2⁻ᵐ` at
`n = m`, and below `2⁻ⁿ` afterwards. -/
private theorem knuthYaoCost_le (hx : 0 < x) {m : ℕ} (hm : 1 ≤ (2 : ℝ) ^ m * x) :
    knuthYaoCost x ≤ (m + 1) * x := by
  have hs := summable_truncErr hx.le
  rw [knuthYaoCost, ← hs.sum_add_tsum_nat_add (m + 1), Finset.sum_range_succ]
  have hfirst : ∑ n ∈ Finset.range m, truncErr x n ≤ m * x := by
    calc ∑ n ∈ Finset.range m, truncErr x n ≤ ∑ n ∈ Finset.range m, x :=
          Finset.sum_le_sum (fun n _ => truncErr_le n)
      _ = m * x := by simp
  have hmid : truncErr x m ≤ x - 2⁻¹ ^ m := by
    have h1 : (1 : ℝ) ≤ ⌊(2 : ℝ) ^ m * x⌋₊ := by
      exact_mod_cast (Nat.one_le_floor_iff _).mpr hm
    rw [truncErr, inv_pow, div_eq_mul_inv]
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
    nlinarith
  have htail : ∑' k, truncErr x (k + (m + 1)) ≤ 2⁻¹ ^ m := by
    have hgeom : Summable fun k : ℕ => (2⁻¹ : ℝ) ^ (k + (m + 1)) :=
      (summable_nat_add_iff (m + 1)).mpr
        (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    calc ∑' k, truncErr x (k + (m + 1)) ≤ ∑' k : ℕ, (2⁻¹ : ℝ) ^ (k + (m + 1)) :=
          Summable.tsum_le_tsum (fun k => (truncErr_lt _).le)
            ((summable_nat_add_iff (m + 1)).mpr hs) hgeom
      _ = 2⁻¹ ^ m := by
          simp only [pow_add, tsum_mul_right, tsum_geometric_inv_two]
          ring
  linarith

/-- Lower bound: an outcome of probability `x` costs at least its surprisal contribution. -/
theorem negMulLogb_le_knuthYaoCost (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * -Real.logb 2 x ≤ knuthYaoCost x := by
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  · obtain ⟨m, hm1, hm2⟩ := exists_scale hx hx1
    exact (negMulLogb_le hx hm1).trans (mul_le_knuthYaoCost hx hm2)

/-- Upper bound: an outcome of probability `x` costs less than its surprisal contribution plus
`2 x`. -/
theorem knuthYaoCost_lt_negMulLogb_add (hx : 0 < x) (hx1 : x ≤ 1) :
    knuthYaoCost x < x * -Real.logb 2 x + 2 * x := by
  obtain ⟨m, hm1, hm2⟩ := exists_scale hx hx1
  have h1 := knuthYaoCost_le hx hm1
  have h2 := negMulLogb_gt hx hm2
  linarith

theorem knuthYaoCost_le_negMulLogb_add (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    knuthYaoCost x ≤ x * -Real.logb 2 x + 2 * x := by
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  · exact (knuthYaoCost_lt_negMulLogb_add hx hx1).le

theorem knuthYaoCost_inv_two_pow (m : ℕ) : knuthYaoCost (2⁻¹ ^ m) = m * 2⁻¹ ^ m := by
  have hzero : ∀ n ∉ Finset.range m, truncErr (2⁻¹ ^ m) n = 0 := by
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp (Finset.mem_range.not.mp hn))
    have h : (2 : ℝ) ^ (m + j) * 2⁻¹ ^ m = ((2 ^ j : ℕ) : ℝ) := by
      push_cast
      rw [pow_add, inv_pow]
      field_simp
    rw [truncErr, h, Nat.floor_natCast]
    push_cast
    rw [pow_add, inv_pow]
    field_simp
    ring
  rw [knuthYaoCost, tsum_eq_sum hzero, Finset.sum_congr rfl fun n hn => truncErr_eq_self ?_]
  · simp
  · rw [inv_pow, mul_inv_lt_iff₀ (by positivity), one_mul]
    exact pow_lt_pow_right₀ (by norm_num) (Finset.mem_range.mp hn)

/-- The lower bound is tight exactly at `0` and at powers of `1/2`. -/
theorem knuthYaoCost_eq_negMulLogb_iff (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    knuthYaoCost x = x * -Real.logb 2 x ↔ x = 0 ∨ ∃ m : ℕ, x = 2⁻¹ ^ m := by
  constructor
  · intro h
    rcases hx0.eq_or_lt with rfl | hx
    · exact Or.inl rfl
    right
    obtain ⟨m, hm1, hm2⟩ := exists_scale hx hx1
    have h1 := negMulLogb_le hx hm1
    have h2 := mul_le_knuthYaoCost hx hm2
    have hlog : Real.logb 2 x = -m := by
      have h3 : x * -Real.logb 2 x = x * m := by
        rw [mul_comm x (m : ℝ)]
        exact le_antisymm h1 (h ▸ h2)
      have := mul_left_cancel₀ hx.ne' h3
      linarith
    refine ⟨m, ?_⟩
    have := Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hx
    rw [hlog, Real.rpow_neg (by norm_num), Real.rpow_natCast] at this
    rw [← this, inv_pow]
  · rintro (rfl | ⟨m, rfl⟩)
    · simp
    · rw [knuthYaoCost_inv_two_pow, inv_pow, Real.logb_inv, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      ring

end Real

/-! ## The Knuth–Yao tree -/

variable {α : Type*} [Fintype α]

/-- The number `⌊2ᵏ p a⌋` of depth-`k` positions of the Knuth–Yao tree lying at or below a leaf
labelled `a` (a leaf at depth `j ≤ k` counts `2 ^ (k - j)` times). Equivalently, `⌊2ᵏ p a⌋ / 2ᵏ`
is the probability that the tree outputs `a` within `k` flips. -/
noncomputable def knuthYaoCounts (p : PMF α) (k : ℕ) (a : α) : ℕ :=
  ⌊(2 : ℝ) ^ k * (p a).toReal⌋₊

/-- The Knuth–Yao tree of `p`: a leaf labelled `a` at depth `k` for each binary digit
`⌊2ᵏ p a⌋ mod 2 = 1` of `p a` (position `0` is the units digit, so `p a = 1` gives a root leaf). -/
noncomputable def knuthYao (p : PMF α) : DDGTree α := ofCounts (knuthYaoCounts p)

omit [Fintype α] in
private theorem knuthYaoCounts_mono (p : PMF α) (k : ℕ) (a : α) :
    2 * knuthYaoCounts p k a ≤ knuthYaoCounts p (k + 1) a := by
  unfold knuthYaoCounts
  apply Nat.le_floor
  push_cast
  have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 ^ k * (p a).toReal)
  rw [pow_succ]
  nlinarith

private theorem knuthYaoCounts_kraft (p : PMF α) (k : ℕ) :
    ∑ a, knuthYaoCounts p k a ≤ 2 ^ k := by
  have h : (∑ a, knuthYaoCounts p k a : ℝ) ≤ 2 ^ k := by
    calc (∑ a, knuthYaoCounts p k a : ℝ) ≤ ∑ a, (2 : ℝ) ^ k * (p a).toReal :=
          Finset.sum_le_sum fun a _ => Nat.floor_le (by positivity)
      _ = 2 ^ k := by rw [← Finset.mul_sum, PMF.sum_toReal, mul_one]
  exact_mod_cast h

/-- Within `n` flips, the Knuth–Yao tree outputs `a` with probability `⌊2ⁿ p a⌋ / 2ⁿ`, the
`n`-digit binary truncation of `p a`. -/
theorem run_knuthYao_some (p : PMF α) (n : ℕ) (a : α) :
    (knuthYao p).run n (some a) = ⌊(2 : ℝ) ^ n * (p a).toReal⌋₊ / 2 ^ n :=
  run_ofCounts (knuthYaoCounts_mono p) (knuthYaoCounts_kraft p) n a

private theorem run_knuthYao_some_eq_ofReal (p : PMF α) (n : ℕ) (a : α) :
    (knuthYao p).run n (some a) = ENNReal.ofReal ((p a).toReal - truncErr (p a).toReal n) := by
  rw [run_knuthYao_some, truncErr, sub_sub_cancel, ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem knuthYao_generates (p : PMF α) : (knuthYao p).Generates p := by
  intro a
  refine iSup_eq_of_tendsto ((knuthYao p).monotone_run a) ?_
  simp only [run_knuthYao_some_eq_ofReal]
  rw [← ENNReal.ofReal_toReal (p.apply_ne_top a)]
  refine ENNReal.tendsto_ofReal ?_
  have hzero : Tendsto (fun n => truncErr (p a).toReal n) atTop (𝓝 0) :=
    squeeze_zero (fun n => truncErr_nonneg ENNReal.toReal_nonneg n) (fun n => (truncErr_lt n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  simpa using (tendsto_const_nhds (x := (p a).toReal)).sub hzero

/-- The Knuth–Yao tree needs more than `n` flips with probability `∑ₐ (p a - ⌊2ⁿ p a⌋ / 2ⁿ)`. -/
theorem run_knuthYao_none (p : PMF α) (n : ℕ) :
    (knuthYao p).run n none = ENNReal.ofReal (∑ a, truncErr (p a).toReal n) := by
  have hsum := (knuthYao p).run_none_add_sum n
  have hle : ∑ a, (knuthYao p).run n (some a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsum ▸ le_add_self)
  refine (ENNReal.eq_sub_of_add_eq hle hsum).trans (ENNReal.eq_sub_of_add_eq hle ?_).symm
  simp only [run_knuthYao_some_eq_ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => sub_nonneg.mpr (truncErr_le n),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun a _ => truncErr_nonneg ENNReal.toReal_nonneg n)
      (Finset.sum_nonneg fun a _ => sub_nonneg.mpr (truncErr_le n)),
    ← Finset.sum_add_distrib]
  simp only [add_sub_cancel, PMF.sum_toReal, ENNReal.ofReal_one]

/-- The expected number of flips of the Knuth–Yao tree is `∑ₐ ν(p a)`. -/
theorem expectedFlips_knuthYao (p : PMF α) :
    (knuthYao p).expectedFlips = ENNReal.ofReal (∑ a, knuthYaoCost (p a).toReal) := by
  have hs : ∀ a, Summable (truncErr (p a).toReal) := fun a =>
    summable_truncErr ENNReal.toReal_nonneg
  rw [expectedFlips]
  simp only [run_knuthYao_none]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => Finset.sum_nonneg fun a _ => truncErr_nonneg ENNReal.toReal_nonneg n)
    (summable_sum fun a _ => hs a), Summable.tsum_finsetSum fun a _ => hs a]
  rfl

theorem entropy_le_sum_knuthYaoCost (p : PMF α) :
    PMF.entropy p ≤ ∑ a, knuthYaoCost (p a).toReal := by
  rw [PMF.entropy_eq_sum_surprisal]
  exact Finset.sum_le_sum fun a _ => negMulLogb_le_knuthYaoCost ENNReal.toReal_nonneg
    (PMF.toReal_apply_le_one p a)

theorem sum_knuthYaoCost_lt_entropy_add_two (p : PMF α) :
    ∑ a, knuthYaoCost (p a).toReal < PMF.entropy p + 2 := by
  rw [PMF.entropy_eq_sum_surprisal]
  obtain ⟨a₀, ha₀⟩ := p.support_nonempty
  have h2 : ∑ a, 2 * (p a).toReal = 2 := by rw [← Finset.mul_sum, PMF.sum_toReal, mul_one]
  rw [← h2, ← Finset.sum_add_distrib]
  refine Finset.sum_lt_sum
    (fun a _ => knuthYaoCost_le_negMulLogb_add ENNReal.toReal_nonneg (PMF.toReal_apply_le_one p a))
    ⟨a₀, Finset.mem_univ _, knuthYaoCost_lt_negMulLogb_add
      (ENNReal.toReal_pos ((p.mem_support_iff a₀).mp ha₀) (p.apply_ne_top a₀))
      (PMF.toReal_apply_le_one p a₀)⟩

/-- Stochastic dominance: for every tree generating `p` and every `n`, the Knuth–Yao tree is at
least as likely to have stopped within `n` flips. -/
theorem run_knuthYao_none_le {T : DDGTree α} {p : PMF α} (hT : T.Generates p) (n : ℕ) :
    (knuthYao p).run n none ≤ T.run n none := by
  have hsome : ∀ a, T.run n (some a) ≤ (knuthYao p).run n (some a) := by
    intro a
    obtain ⟨c, hc⟩ := T.exists_run_eq_div n (some a)
    have hp : T.run n (some a) ≤ p a := hT a ▸ T.run_le_outputProb n a
    rw [hc] at hp ⊢
    rw [run_knuthYao_some]
    gcongr
    apply Nat.le_floor
    have hp' := ENNReal.toReal_mono (p.apply_ne_top a) hp
    rw [ENNReal.toReal_div] at hp'
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hp'
    rw [div_le_iff₀ (by positivity)] at hp'
    linarith
  have hT1 := T.run_none_add_sum n
  have hK1 := (knuthYao p).run_none_add_sum n
  have hfin : ∑ a, (knuthYao p).run n (some a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hK1 ▸ le_add_self)
  have hle := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hsome a
  refine (ENNReal.add_le_add_iff_right hfin).mp ?_
  rw [hK1, ← hT1]
  exact add_le_add_right hle _

/-- Knuth–Yao optimality: no tree generating `p` uses fewer expected flips. -/
theorem expectedFlips_knuthYao_le {T : DDGTree α} {p : PMF α} (hT : T.Generates p) :
    (knuthYao p).expectedFlips ≤ T.expectedFlips :=
  tsum_le_tsum fun n => run_knuthYao_none_le hT n

theorem isLeast_expectedFlips_knuthYao (p : PMF α) :
    IsLeast {e | ∃ T : DDGTree α, T.Generates p ∧ T.expectedFlips = e}
      (knuthYao p).expectedFlips :=
  ⟨⟨knuthYao p, knuthYao_generates p, rfl⟩, fun _ ⟨_, hT, he⟩ =>
    he ▸ expectedFlips_knuthYao_le hT⟩

/-- **Entropy lower bound** ([CoverThomas2006], Theorem 5.11.1): every tree generating `p` reads
at least `H(p)` fair bits in expectation. -/
theorem entropy_le_expectedFlips {α : Type*} [Finite α] {T : DDGTree α} {p : PMF α}
    (hT : T.Generates p) : ENNReal.ofReal (PMF.entropy p) ≤ T.expectedFlips := by
  have := Fintype.ofFinite α
  refine le_trans ?_ (expectedFlips_knuthYao_le hT)
  rw [expectedFlips_knuthYao]
  exact ENNReal.ofReal_le_ofReal (entropy_le_sum_knuthYaoCost p)

/-- **Knuth–Yao upper bound** ([CoverThomas2006], Theorem 5.11.3): the Knuth–Yao tree reads fewer
than `H(p) + 2` fair bits in expectation. -/
theorem expectedFlips_knuthYao_lt (p : PMF α) :
    (knuthYao p).expectedFlips < ENNReal.ofReal (PMF.entropy p + 2) := by
  rw [expectedFlips_knuthYao]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [PMF.entropy_nonneg p])).mpr
    (sum_knuthYaoCost_lt_entropy_add_two p)

theorem exists_generates_expectedFlips_lt {α : Type*} [Finite α] (p : PMF α) :
    ∃ T : DDGTree α, T.Generates p ∧ T.expectedFlips < ENNReal.ofReal (PMF.entropy p + 2) :=
  have := Fintype.ofFinite α
  ⟨knuthYao p, knuthYao_generates p, expectedFlips_knuthYao_lt p⟩

private theorem toReal_eq_inv_two_pow_iff {x : ℝ≥0∞} (hx : x ≠ ⊤) (m : ℕ) :
    x.toReal = 2⁻¹ ^ m ↔ x = 2⁻¹ ^ m := by
  rw [← ENNReal.toReal_eq_toReal_iff' hx (by simp), ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]

/-- The Knuth–Yao tree attains the entropy exactly for dyadic distributions. -/
theorem expectedFlips_knuthYao_eq_entropy_iff (p : PMF α) :
    (knuthYao p).expectedFlips = ENNReal.ofReal (PMF.entropy p) ↔
      ∀ a ∈ p.support, ∃ m : ℕ, p a = 2⁻¹ ^ m := by
  rw [expectedFlips_knuthYao, ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun a _ => knuthYaoCost_nonneg ENNReal.toReal_nonneg)
    (PMF.entropy_nonneg p), PMF.entropy_eq_sum_surprisal]
  simp only [PMF.surprisal]
  rw [eq_comm, Finset.sum_eq_sum_iff_of_le fun a _ =>
      negMulLogb_le_knuthYaoCost ENNReal.toReal_nonneg (PMF.toReal_apply_le_one p a)]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun a => ?_
  rw [eq_comm, knuthYaoCost_eq_negMulLogb_iff ENNReal.toReal_nonneg (PMF.toReal_apply_le_one p a),
    PMF.mem_support_iff]
  constructor
  · rintro (h | ⟨m, hm⟩) hpa
    · exact absurd ((ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (p.apply_ne_top a)) hpa
    · exact ⟨m, (toReal_eq_inv_two_pow_iff (p.apply_ne_top a) m).mp hm⟩
  · intro h
    by_cases hpa : p a = 0
    · left; simp [hpa]
    · obtain ⟨m, hm⟩ := h hpa
      exact Or.inr ⟨m, (toReal_eq_inv_two_pow_iff (p.apply_ne_top a) m).mpr hm⟩

/-- **Dyadic case** ([CoverThomas2006], Theorem 5.11.2 and its converse): some tree generating `p`
reads exactly `H(p)` fair bits in expectation if and only if every positive probability `p a` is a
power of `1/2`. -/
theorem exists_generates_expectedFlips_eq_entropy_iff {α : Type*} [Finite α] (p : PMF α) :
    (∃ T : DDGTree α, T.Generates p ∧ T.expectedFlips = ENNReal.ofReal (PMF.entropy p)) ↔
      ∀ a ∈ p.support, ∃ m : ℕ, p a = 2⁻¹ ^ m := by
  have := Fintype.ofFinite α
  rw [← expectedFlips_knuthYao_eq_entropy_iff]
  constructor
  · rintro ⟨T, hT, he⟩
    exact le_antisymm (he ▸ expectedFlips_knuthYao_le hT) (entropy_le_expectedFlips
      (knuthYao_generates p))
  · intro h
    exact ⟨knuthYao p, knuthYao_generates p, h⟩

end Cslib.Probability.DDGTree
