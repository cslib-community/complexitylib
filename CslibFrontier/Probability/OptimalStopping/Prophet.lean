/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.OptimalStopping.Basic
public import Mathlib.Basic.NNReal.Basic
import CslibFrontier.Probability.PMF.TailQuantile
import CslibFrontier.Probability.PMF.Bind

/-!
# The prophet inequality

A gambler observes independent nonnegative values `X₁, …, Xₙ` one at a time, `Xᵢ` drawn from the
`i`-th law of `laws`, and may stop once, collecting the current value; a gambler who never stops
collects nothing. A prophet who sees all values in advance collects `E[max Xᵢ]`
(`expectedMax laws`). The *prophet inequality* of Krengel and Sucheston says that the gambler can
guarantee half of this, and Samuel-Cahn showed that a single threshold suffices: accept the first
value of at least (or more than) a fixed `t`.

`expectedMax_le_two_mul_expectedReward` is the threshold form proved here. Let `R` be the
probability that the rule accepts no value. If `t` and `R` lie on opposite sides of `E[max]/2` and
`1/2`, that is, `2t ≤ E[max]` and `1 ≤ 2R`, or `E[max] ≤ 2t` and `2R ≤ 1`, then the rule's
expected reward is at least `E[max]/2`. The proof bounds the reward from below by
`t (1 - R) + R ∑ᵢ E[(Xᵢ - t)⁺]` and the maximum from above by `t + ∑ᵢ (Xᵢ - t)⁺`, both arranged
without subtracting extended reals. Two choices of threshold make the hypothesis automatic:

* `t = E[max]/2` (Kleinberg–Weinberg; Roughgarden, Lecture 6):
  `expectedMax_le_two_mul_expectedReward_of_two_mul_eq` and
  `expectedMax_le_two_mul_expectedReward_half`;
* `t` a median of `max Xᵢ` (Samuel-Cahn): `expectedMax_le_two_mul_expectedReward_median`, where
  accepting values `≥ t` works when `t ≥ E[max]/2` and accepting values `> t` works when
  `t ≤ E[max]/2`. A median always exists (`exists_median_listMax`, from
  `PMF.exists_tail_quantile`), so some single threshold always works
  (`exists_expectedMax_le_two_mul_expectedReward`).

The factor `1/2` is optimal: for `tightLaws k`, a sure value `1` followed by `k + 1` with
probability `1/(k + 1)` and `0` otherwise, every rule, even one using the whole history, has
expected reward at most `1` while `E[max] = (2k + 1)/(k + 1)` (`exists_tightLaws_lt`).

The values are `ℝ≥0`-valued with arbitrary countable support. `E[max]` may be infinite; the
threshold form needs no integrability. A gambler who never stops gets `0`; Samuel-Cahn's rules,
which take the last value in that case, collect at least as much, so the bounds apply to them too.

## Main definitions

* `Cslib.Probability.OptimalStopping.Prophet.expectedReward`,
  `Cslib.Probability.OptimalStopping.Prophet.expectedMax`: the gambler's and the prophet's
  expected rewards.
* `Cslib.Probability.OptimalStopping.Prophet.thresholdRule`,
  `Cslib.Probability.OptimalStopping.Prophet.strictThresholdRule`: single-threshold rules.

## Main results

* `Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_two_mul_expectedReward`: the threshold
  form of the prophet inequality.
* `Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_two_mul_expectedReward_half`: the
  threshold `E[max]/2`.
* `Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_two_mul_expectedReward_median`: a
  median threshold.
* `Cslib.Probability.OptimalStopping.Prophet.exists_expectedMax_le_two_mul_expectedReward`:
  Samuel-Cahn's theorem without a median hypothesis.
* `Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_add_sum`: the prophet's bound
  `E[max] ≤ t + ∑ᵢ E[(Xᵢ - t)⁺]`.
* `Cslib.Probability.OptimalStopping.Prophet.exists_tightLaws_lt`: no constant above `1/2` holds.

## References

* [U. Krengel and L. Sucheston, *Semiamarts and finite values*][KrengelSucheston1977]
* [E. Samuel-Cahn, *Comparison of threshold stop rules and maximum for independent nonnegative
  random variables*][SamuelCahn1984]
* [R. Kleinberg and S. M. Weinberg, *Matroid prophet inequalities*][KleinbergWeinberg2012]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016], Lecture 6,
  Theorem 6.1
-/

public section

namespace Cslib.Probability.OptimalStopping.Prophet

open scoped ENNReal NNReal

/-- The largest value of a list, and `0` for the empty list. -/
@[expose] noncomputable def listMax : List ℝ≥0 → ℝ≥0
  | [] => 0
  | x :: xs => max x (listMax xs)

/-- The gambler collects the value at which it stops. -/
@[expose] def reward : List ℝ≥0 → List ℝ≥0 → ℝ≥0∞
  | [], _ => 0
  | x :: _, _ => x

/-- The expected reward of the stopping rule `stop` on independent values with laws `laws`. -/
@[expose] noncomputable def expectedReward (stop : List ℝ≥0 → Bool) (laws : List (PMF ℝ≥0)) :
    ℝ≥0∞ :=
  ∑' xs, jointLaw laws xs * payoff stop reward [] xs

/-- The prophet's expected reward, the expected maximum of the values. -/
@[expose] noncomputable def expectedMax (laws : List (PMF ℝ≥0)) : ℝ≥0∞ :=
  ∑' xs, jointLaw laws xs * (listMax xs : ℝ≥0∞)

/-- The rule that accepts the current value `x` exactly when `a x`, ignoring the history. -/
@[expose] def acceptRule (a : ℝ≥0 → Bool) : List ℝ≥0 → Bool
  | [] => false
  | x :: _ => a x

/-- Accept the first value of at least `t`. -/
@[expose] noncomputable def thresholdRule (t : ℝ≥0) : List ℝ≥0 → Bool :=
  acceptRule fun x => decide (t ≤ x)

/-- Accept the first value of more than `t`. -/
@[expose] noncomputable def strictThresholdRule (t : ℝ≥0) : List ℝ≥0 → Bool :=
  acceptRule fun x => decide (t < x)

/-- The probability that `acceptRule a` accepts no value. -/
@[expose] noncomputable def rejectProb (a : ℝ≥0 → Bool) (laws : List (PMF ℝ≥0)) : ℝ≥0∞ :=
  (jointLaw laws).toOuterMeasure {xs | ∀ x ∈ xs, a x = false}

/-- The reward of `acceptRule a` on the remaining values. -/
private noncomputable def acceptPayoff (a : ℝ≥0 → Bool) : List ℝ≥0 → ℝ≥0∞
  | [] => 0
  | x :: xs => if a x then (x : ℝ≥0∞) else acceptPayoff a xs

/-- The indicator that `acceptRule a` accepts no value. -/
private def rejectsAll (a : ℝ≥0 → Bool) : List ℝ≥0 → ℝ≥0∞
  | [] => 1
  | x :: xs => if a x then 0 else rejectsAll a xs

/-- `∑ᵢ (xᵢ - t)⁺`. -/
private noncomputable def excessSum (t : ℝ≥0) : List ℝ≥0 → ℝ≥0∞
  | [] => 0
  | x :: xs => ((x - t : ℝ≥0) : ℝ≥0∞) + excessSum t xs

private theorem payoff_acceptRule (a : ℝ≥0 → Bool) :
    ∀ past xs, payoff (acceptRule a) reward past xs = acceptPayoff a xs
  | _, [] => rfl
  | past, x :: xs => by
      rw [payoff_cons, acceptPayoff]
      change (if a x = true then (x : ℝ≥0∞) else _) = _
      rw [payoff_acceptRule a (x :: past) xs]

/-- No rule collects more than the maximum. -/
theorem payoff_le_listMax (stop : List ℝ≥0 → Bool) :
    ∀ past xs, payoff stop reward past xs ≤ (listMax xs : ℝ≥0∞)
  | _, [] => by simp [payoff_nil]
  | past, x :: xs => by
      rw [payoff_cons, listMax, ENNReal.coe_max]
      split_ifs
      · exact le_max_left _ _
      · exact (payoff_le_listMax stop (x :: past) xs).trans (le_max_right _ _)

/-- The gambler never beats the prophet. -/
theorem expectedReward_le_expectedMax (stop : List ℝ≥0 → Bool) (laws : List (PMF ℝ≥0)) :
    expectedReward stop laws ≤ expectedMax laws :=
  tsum_le_tsum fun xs => by gcongr; exact payoff_le_listMax stop [] xs

theorem listMax_lt_iff {τ : ℝ≥0} (hτ : 0 < τ) :
    ∀ xs : List ℝ≥0, listMax xs < τ ↔ ∀ x ∈ xs, x < τ
  | [] => by simp [listMax, hτ]
  | x :: xs => by simp [listMax, listMax_lt_iff hτ xs]

theorem listMax_le_iff (τ : ℝ≥0) : ∀ xs : List ℝ≥0, listMax xs ≤ τ ↔ ∀ x ∈ xs, x ≤ τ
  | [] => by simp [listMax]
  | x :: xs => by simp [listMax, listMax_le_iff τ xs]

private theorem listMax_le_add_excessSum (t : ℝ≥0) :
    ∀ xs, (listMax xs : ℝ≥0∞) ≤ t + excessSum t xs
  | [] => by simp [listMax]
  | x :: xs => by
      rw [listMax, ENNReal.coe_max, excessSum]
      refine max_le ?_ ((listMax_le_add_excessSum t xs).trans ?_)
      · calc (x : ℝ≥0∞) ≤ ((t + (x - t) : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast le_add_tsub
          _ ≤ t + (((x - t : ℝ≥0) : ℝ≥0∞) + excessSum t xs) := by
            rw [ENNReal.coe_add, ← add_assoc]; exact le_self_add
      · gcongr; exact le_add_self

private theorem expectedMax_le_add (t : ℝ≥0) (laws : List (PMF ℝ≥0)) :
    expectedMax laws ≤ t + ∑' xs, jointLaw laws xs * excessSum t xs :=
  calc expectedMax laws ≤ ∑' xs, jointLaw laws xs * ((t : ℝ≥0∞) + excessSum t xs) :=
        tsum_le_tsum fun xs => by gcongr; exact listMax_le_add_excessSum t xs
    _ = ∑' xs, (jointLaw laws xs * t + jointLaw laws xs * excessSum t xs) :=
        tsum_congr fun xs => mul_add _ _ _
    _ = _ := by rw [tsum_add, tsum_pmf_mul_const]

private theorem tsum_excessSum (t : ℝ≥0) : ∀ laws : List (PMF ℝ≥0),
    ∑' xs, jointLaw laws xs * excessSum t xs =
      (laws.map fun μ => ∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞)).sum
  | [] => by simp [excessSum]
  | μ :: laws => by
      rw [tsum_jointLaw_cons_mul, List.map_cons, List.sum_cons, ← tsum_excessSum t laws]
      simp only [excessSum, mul_add, tsum_add, tsum_pmf_mul_const]

/-- The prophet collects at most `t + ∑ᵢ E[(Xᵢ - t)⁺]`, for every cutoff `t`. -/
theorem expectedMax_le_add_sum (t : ℝ≥0) (laws : List (PMF ℝ≥0)) :
    expectedMax laws ≤ t + (laws.map fun μ => ∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞)).sum :=
  (expectedMax_le_add t laws).trans_eq (by rw [tsum_excessSum])

/-- For `n` i.i.d. values, `E[max] ≤ t + n E[(X - t)⁺]`. -/
theorem expectedMax_replicate_le (t : ℝ≥0) (μ : PMF ℝ≥0) (n : ℕ) :
    expectedMax (List.replicate n μ) ≤ t + n * ∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞) := by
  simpa [List.map_replicate, List.sum_replicate, nsmul_eq_mul] using
    expectedMax_le_add_sum t (List.replicate n μ)

private theorem rejectsAll_le_one (a : ℝ≥0 → Bool) : ∀ xs, rejectsAll a xs ≤ 1
  | [] => le_rfl
  | x :: xs => by
      rw [rejectsAll]
      split_ifs
      · exact zero_le
      · exact rejectsAll_le_one a xs

private theorem rejectsAll_eq (a : ℝ≥0 → Bool) :
    ∀ xs, rejectsAll a xs = if ∀ x ∈ xs, a x = false then 1 else 0
  | [] => by simp [rejectsAll]
  | x :: xs => by
      rw [rejectsAll, rejectsAll_eq a xs]
      by_cases hx : a x = true <;> simp [hx]

private theorem rejectProb_eq (a : ℝ≥0 → Bool) (laws : List (PMF ℝ≥0)) :
    rejectProb a laws = ∑' xs, jointLaw laws xs * rejectsAll a xs := by
  rw [rejectProb, PMF.toOuterMeasure_apply]
  refine tsum_congr fun xs => ?_
  by_cases h : ∀ x ∈ xs, a x = false <;> simp [Set.indicator_apply, rejectsAll_eq, h]

theorem rejectProb_le_one (a : ℝ≥0 → Bool) (laws : List (PMF ℝ≥0)) : rejectProb a laws ≤ 1 := by
  rw [rejectProb_eq]
  exact Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ (rejectsAll_le_one a)

/-- One step of the induction for `prophet_key`, with the tail's quantities abstracted. -/
private theorem prophet_step (μ : PMF ℝ≥0) {t : ℝ≥0} {a : ℝ≥0 → Bool}
    (ha₁ : ∀ x, t < x → a x = true) (ha₂ : ∀ x, a x = true → t ≤ x) {R S A : ℝ≥0∞}
    (hR : R ≤ 1) (ih : t + R * S ≤ A + t * R) :
    (t : ℝ≥0∞) + ((∑' x, μ x * (if a x then 0 else 1)) * R) *
        (∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞) + S) ≤
      ∑' x, μ x * (if a x then (x : ℝ≥0∞) else A) +
        t * ((∑' x, μ x * (if a x then 0 else 1)) * R) := by
  have hq : ∑' x, μ x * (if a x then (0 : ℝ≥0∞) else 1) ≤ 1 :=
    Cslib.Probability.PMF.tsum_mul_le_of_forall_le μ fun x => by split_ifs <;> simp
  have hqR : (∑' x, μ x * (if a x then (0 : ℝ≥0∞) else 1)) * R ≤ 1 := mul_le_one' hq hR
  have hpt : ∀ x : ℝ≥0, (t : ℝ≥0∞) + ((x - t : ℝ≥0) : ℝ≥0∞) + (if a x then 0 else 1) * (R * S) ≤
      (if a x then (x : ℝ≥0∞) else A) + (if a x then 0 else 1) * (t * R) := by
    intro x
    by_cases hx : a x = true
    · simp only [hx, ↓reduceIte, zero_mul, add_zero]
      rw [← ENNReal.coe_add, add_tsub_cancel_of_le (ha₂ x hx)]
    · have hxt : x ≤ t := not_lt.mp fun h => hx (ha₁ x h)
      have hx' : a x = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ↓reduceIte, one_mul, tsub_eq_zero_of_le hxt,
        ENNReal.coe_zero, add_zero]
      exact ih
  calc (t : ℝ≥0∞) + ((∑' x, μ x * (if a x then 0 else 1)) * R) *
        (∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞) + S)
      = t + ((∑' x, μ x * (if a x then 0 else 1)) * R) * ∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞) +
          (∑' x, μ x * (if a x then 0 else 1)) * (R * S) := by ring
    _ ≤ t + ∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞) +
          (∑' x, μ x * (if a x then 0 else 1)) * (R * S) := by
        gcongr; exact mul_le_of_le_one_left zero_le hqR
    _ = ∑' x, (μ x * t + μ x * ((x - t : ℝ≥0) : ℝ≥0∞) +
          μ x * (if a x then 0 else 1) * (R * S)) := by
        rw [tsum_add, tsum_add, tsum_pmf_mul_const, ENNReal.tsum_mul_right]
    _ = ∑' x, μ x * ((t : ℝ≥0∞) + ((x - t : ℝ≥0) : ℝ≥0∞) + (if a x then 0 else 1) * (R * S)) :=
        tsum_congr fun x => by ring
    _ ≤ ∑' x, μ x * ((if a x then (x : ℝ≥0∞) else A) + (if a x then 0 else 1) * (t * R)) :=
        tsum_le_tsum fun x => by gcongr μ x * ?_; exact hpt x
    _ = ∑' x, (μ x * (if a x then (x : ℝ≥0∞) else A) + μ x * (if a x then 0 else 1) * (t * R)) :=
        tsum_congr fun x => by ring
    _ = _ := by
        rw [tsum_add, ENNReal.tsum_mul_right]; ring

/-- The key inequality `t + R ∑ᵢ E[(Xᵢ - t)⁺] ≤ A + t R`, where `A` is the expected reward of
`acceptRule a` and `R` the probability that it accepts no value. -/
private theorem prophet_key {t : ℝ≥0} {a : ℝ≥0 → Bool} (ha₁ : ∀ x, t < x → a x = true)
    (ha₂ : ∀ x, a x = true → t ≤ x) : ∀ laws : List (PMF ℝ≥0),
    (t : ℝ≥0∞) + (∑' xs, jointLaw laws xs * rejectsAll a xs) *
        ∑' xs, jointLaw laws xs * excessSum t xs ≤
      ∑' xs, jointLaw laws xs * acceptPayoff a xs + t * ∑' xs, jointLaw laws xs * rejectsAll a xs
  | [] => by simp [rejectsAll, excessSum, acceptPayoff]
  | μ :: L => by
      have hRc : ∑' xs, jointLaw (μ :: L) xs * rejectsAll a xs =
          (∑' x, μ x * (if a x then 0 else 1)) * ∑' xs, jointLaw L xs * rejectsAll a xs := by
        rw [tsum_jointLaw_cons_mul, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun x => ?_
        by_cases hx : a x = true
        · simp only [rejectsAll, hx, ↓reduceIte, mul_zero, tsum_zero, zero_mul]
        · have hx' : a x = false := by simpa using hx
          simp only [rejectsAll, hx', Bool.false_eq_true, ↓reduceIte, mul_one]
      have hSc : ∑' xs, jointLaw (μ :: L) xs * excessSum t xs =
          ∑' x, μ x * ((x - t : ℝ≥0) : ℝ≥0∞) + ∑' xs, jointLaw L xs * excessSum t xs := by
        rw [tsum_jointLaw_cons_mul]
        simp only [excessSum, mul_add, tsum_add, tsum_pmf_mul_const]
      have hAc : ∑' xs, jointLaw (μ :: L) xs * acceptPayoff a xs =
          ∑' x, μ x * (if a x then (x : ℝ≥0∞) else ∑' xs, jointLaw L xs * acceptPayoff a xs) := by
        rw [tsum_jointLaw_cons_mul]
        refine tsum_congr fun x => ?_
        by_cases hx : a x = true
        · simp only [acceptPayoff, hx, ↓reduceIte, tsum_pmf_mul_const]
        · have hx' : a x = false := by simpa using hx
          simp only [acceptPayoff, hx', Bool.false_eq_true, ↓reduceIte]
      rw [hRc, hSc, hAc]
      exact prophet_step μ ha₁ ha₂
        (Cslib.Probability.PMF.tsum_mul_le_of_forall_le _ (rejectsAll_le_one a))
        (prophet_key ha₁ ha₂ L)

private theorem prophet_bound {t : ℝ≥0} {a : ℝ≥0 → Bool} (ha₁ : ∀ x, t < x → a x = true)
    (ha₂ : ∀ x, a x = true → t ≤ x) (laws : List (PMF ℝ≥0)) :
    (t : ℝ≥0∞) + rejectProb a laws * expectedMax laws ≤
      expectedReward (acceptRule a) laws + 2 * t * rejectProb a laws := by
  have hA : expectedReward (acceptRule a) laws = ∑' xs, jointLaw laws xs * acceptPayoff a xs :=
    tsum_congr fun xs => by rw [payoff_acceptRule]
  have key := prophet_key ha₁ ha₂ laws
  rw [← rejectProb_eq, ← hA] at key
  calc (t : ℝ≥0∞) + rejectProb a laws * expectedMax laws
      ≤ t + rejectProb a laws * (t + ∑' xs, jointLaw laws xs * excessSum t xs) := by
        gcongr; exact expectedMax_le_add t laws
    _ = (t + rejectProb a laws * ∑' xs, jointLaw laws xs * excessSum t xs) +
          t * rejectProb a laws := by ring
    _ ≤ (expectedReward (acceptRule a) laws + t * rejectProb a laws) + t * rejectProb a laws :=
        add_le_add key le_rfl
    _ = _ := by ring

/-- The arithmetic step: `t + R M ≤ A + 2 t R` gives `M ≤ 2 A` when `t` and `R` lie on opposite
sides of `M/2` and `1/2`. -/
private theorem le_two_mul_of_bound {t : ℝ≥0} {R M A : ℝ≥0∞}
    (hb : (t : ℝ≥0∞) + R * M ≤ A + 2 * t * R) (hR : R ≤ 1)
    (h : (2 * (t : ℝ≥0∞) ≤ M ∧ 1 ≤ 2 * R) ∨ (M ≤ 2 * t ∧ 2 * R ≤ 1)) : M ≤ 2 * A := by
  rcases eq_or_ne A ⊤ with hA | hA
  · simp [hA]
  have hR' : R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hR
  have hM : M ≠ ⊤ := by
    rcases h with ⟨-, h1⟩ | ⟨h1, -⟩
    · intro hM
      have hR0 : R ≠ 0 := by rintro rfl; simp at h1
      rw [hM, ENNReal.mul_top hR0, add_top, top_le_iff] at hb
      exact ENNReal.add_ne_top.mpr ⟨hA, by finiteness⟩ hb
    · exact ne_top_of_le_ne_top (by finiteness) h1
  lift R to ℝ≥0 using hR'
  lift M to ℝ≥0 using hM
  lift A to ℝ≥0 using hA
  norm_cast at hb h ⊢
  rw [← NNReal.coe_le_coe] at hb ⊢
  push_cast at hb ⊢
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : 2 * (t : ℝ) ≤ M := by exact_mod_cast h1
    have h2' : 1 ≤ 2 * (R : ℝ) := by exact_mod_cast h2
    nlinarith [mul_nonneg (sub_nonneg.mpr h1') (sub_nonneg.mpr h2')]
  · have h1' : (M : ℝ) ≤ 2 * t := by exact_mod_cast h1
    have h2' : 2 * (R : ℝ) ≤ 1 := by exact_mod_cast h2
    nlinarith [mul_nonneg (sub_nonneg.mpr h1') (sub_nonneg.mpr h2')]

/-- **The prophet inequality, threshold form.** Let `acceptRule a` accept every value above `t`
and only values of at least `t`, and let `R` be the probability that it accepts no value. If
`2t ≤ E[max]` and `1 ≤ 2R`, or `E[max] ≤ 2t` and `2R ≤ 1`, then its expected reward is at least
half the prophet's. -/
theorem expectedMax_le_two_mul_expectedReward {t : ℝ≥0} {a : ℝ≥0 → Bool}
    (ha₁ : ∀ x, t < x → a x = true) (ha₂ : ∀ x, a x = true → t ≤ x) (laws : List (PMF ℝ≥0))
    (h : (2 * (t : ℝ≥0∞) ≤ expectedMax laws ∧ 1 ≤ 2 * rejectProb a laws) ∨
      (expectedMax laws ≤ 2 * t ∧ 2 * rejectProb a laws ≤ 1)) :
    expectedMax laws ≤ 2 * expectedReward (acceptRule a) laws :=
  le_two_mul_of_bound (prophet_bound ha₁ ha₂ laws) (rejectProb_le_one a laws) h

/-- **The prophet inequality with threshold `E[max]/2`** (Kleinberg–Weinberg): whichever way ties
at the threshold are broken, the rule collects at least half the prophet's expected reward. -/
theorem expectedMax_le_two_mul_expectedReward_of_two_mul_eq (laws : List (PMF ℝ≥0)) {t : ℝ≥0}
    (ht : 2 * (t : ℝ≥0∞) = expectedMax laws) {a : ℝ≥0 → Bool}
    (ha₁ : ∀ x, t < x → a x = true) (ha₂ : ∀ x, a x = true → t ≤ x) :
    expectedMax laws ≤ 2 * expectedReward (acceptRule a) laws := by
  refine expectedMax_le_two_mul_expectedReward ha₁ ha₂ laws ?_
  rcases le_total 1 (2 * rejectProb a laws) with h | h
  · exact Or.inl ⟨ht.le, h⟩
  · exact Or.inr ⟨ht.ge, h⟩

/-- **The prophet inequality**: when `E[max]` is finite, accepting the first value of at least
`E[max]/2` collects at least half the prophet's expected reward. -/
theorem expectedMax_le_two_mul_expectedReward_half (laws : List (PMF ℝ≥0))
    (hM : expectedMax laws ≠ ⊤) :
    expectedMax laws ≤ 2 * expectedReward (thresholdRule (expectedMax laws / 2).toNNReal) laws := by
  refine expectedMax_le_two_mul_expectedReward_of_two_mul_eq laws ?_
    (fun x hx => decide_eq_true hx.le) (fun x hx => of_decide_eq_true hx)
  rw [ENNReal.coe_toNNReal (ENNReal.div_ne_top hM two_ne_zero)]
  exact ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- Samuel-Cahn's rule for a median `m` of `max Xᵢ` at or above `E[max]/2`: accepting the first
value of at least `m` collects at least half the prophet's expected reward. -/
theorem expectedMax_le_two_mul_expectedReward_thresholdRule_of_le (laws : List (PMF ℝ≥0))
    {m : ℝ≥0} (hm : (jointLaw laws).toOuterMeasure {xs | listMax xs < m} ≤ 1 / 2)
    (hM : expectedMax laws ≤ 2 * m) :
    expectedMax laws ≤ 2 * expectedReward (thresholdRule m) laws := by
  rcases eq_zero_or_pos m with rfl | hpos
  · have h0 : expectedMax laws = 0 := by simpa using hM
    rw [h0]
    exact zero_le
  have hR : rejectProb (fun x => decide (m ≤ x)) laws =
      (jointLaw laws).toOuterMeasure {xs | listMax xs < m} := by
    rw [rejectProb]
    congr 1
    ext xs
    simp [listMax_lt_iff hpos xs]
  refine expectedMax_le_two_mul_expectedReward (fun x hx => decide_eq_true hx.le)
    (fun x hx => of_decide_eq_true hx) laws (Or.inr ⟨hM, ?_⟩)
  rw [hR]
  calc 2 * (jointLaw laws).toOuterMeasure {xs | listMax xs < m} ≤ 2 * (1 / 2) := by gcongr
    _ = 1 := by rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Samuel-Cahn's rule for a median `m` of `max Xᵢ` at or below `E[max]/2`: accepting the first
value of more than `m` collects at least half the prophet's expected reward. -/
theorem expectedMax_le_two_mul_expectedReward_strictThresholdRule_of_le (laws : List (PMF ℝ≥0))
    {m : ℝ≥0} (hm : 1 / 2 ≤ (jointLaw laws).toOuterMeasure {xs | listMax xs ≤ m})
    (hM : 2 * (m : ℝ≥0∞) ≤ expectedMax laws) :
    expectedMax laws ≤ 2 * expectedReward (strictThresholdRule m) laws := by
  have hR : rejectProb (fun x => decide (m < x)) laws =
      (jointLaw laws).toOuterMeasure {xs | listMax xs ≤ m} := by
    rw [rejectProb]
    congr 1
    ext xs
    simp [listMax_le_iff m xs]
  refine expectedMax_le_two_mul_expectedReward (fun x hx => decide_eq_true hx)
    (fun x hx => (of_decide_eq_true hx).le) laws (Or.inl ⟨hM, ?_⟩)
  rw [hR]
  calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by
        rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
    _ ≤ _ := by gcongr

/-- **Samuel-Cahn's prophet inequality.** For a median `m` of `max Xᵢ`, accepting the first value
of at least `m`, or the first value of more than `m`, collects at least half the prophet's
expected reward. -/
theorem expectedMax_le_two_mul_expectedReward_median (laws : List (PMF ℝ≥0)) {m : ℝ≥0}
    (hlt : (jointLaw laws).toOuterMeasure {xs | listMax xs < m} ≤ 1 / 2)
    (hle : 1 / 2 ≤ (jointLaw laws).toOuterMeasure {xs | listMax xs ≤ m}) :
    expectedMax laws ≤ 2 * expectedReward (thresholdRule m) laws ∨
      expectedMax laws ≤ 2 * expectedReward (strictThresholdRule m) laws := by
  rcases le_total (expectedMax laws) (2 * m) with h | h
  · exact Or.inl (expectedMax_le_two_mul_expectedReward_thresholdRule_of_le laws hlt h)
  · exact Or.inr (expectedMax_le_two_mul_expectedReward_strictThresholdRule_of_le laws hle h)

/-- The maximum of independent values has a median. -/
theorem exists_median_listMax (laws : List (PMF ℝ≥0)) :
    ∃ m : ℝ≥0, (jointLaw laws).toOuterMeasure {xs | listMax xs < m} ≤ 1 / 2 ∧
      1 / 2 ≤ (jointLaw laws).toOuterMeasure {xs | listMax xs ≤ m} := by
  obtain ⟨m, hgt, hge⟩ := PMF.exists_tail_quantile ((jointLaw laws).map listMax)
    (q := 1 / 2) (by simp) (by norm_num)
  refine ⟨m, ?_⟩
  have hν (s : Set ℝ≥0) : ((jointLaw laws).map listMax).toOuterMeasure s =
      ((jointLaw laws).map listMax).toMeasure s :=
    (PMF.toMeasure_apply_eq_toOuterMeasure _ _).symm
  have hlt : (jointLaw laws).toOuterMeasure {xs | listMax xs < m} =
      ((jointLaw laws).map listMax).toMeasure (Set.Iio m) := by
    rw [← hν, PMF.toOuterMeasure_map_apply]; rfl
  have hle : (jointLaw laws).toOuterMeasure {xs | listMax xs ≤ m} =
      ((jointLaw laws).map listMax).toMeasure (Set.Iic m) := by
    rw [← hν, PMF.toOuterMeasure_map_apply]; rfl
  rw [hν] at hgt hge
  rw [hlt, hle]
  have hA := MeasureTheory.measure_add_measure_compl
    (μ := ((jointLaw laws).map listMax).toMeasure) (measurableSet_Iio (a := m))
  have hB := MeasureTheory.measure_add_measure_compl
    (μ := ((jointLaw laws).map listMax).toMeasure) (measurableSet_Iic (a := m))
  rw [Set.compl_Iio, MeasureTheory.measure_univ] at hA
  rw [Set.compl_Iic, MeasureTheory.measure_univ] at hB
  constructor
  · refine ENNReal.le_of_add_le_add_right
      (MeasureTheory.measure_ne_top ((jointLaw laws).map listMax).toMeasure (Set.Ici m)) ?_
    calc _ = (1 : ℝ≥0∞) := hA
      _ = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
      _ ≤ _ := by gcongr
  · refine ENNReal.le_of_add_le_add_right (a := 1 / 2) (by simp) ?_
    calc (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := ENNReal.add_halves 1
      _ = _ := hB.symm
      _ ≤ _ := by gcongr

/-- **Samuel-Cahn's prophet inequality.** For all independent nonnegative values there is a
single threshold `m` such that accepting the first value of at least `m`, or the first value of
more than `m`, collects at least half the prophet's expected reward. -/
theorem exists_expectedMax_le_two_mul_expectedReward (laws : List (PMF ℝ≥0)) :
    ∃ m : ℝ≥0, expectedMax laws ≤ 2 * expectedReward (thresholdRule m) laws ∨
      expectedMax laws ≤ 2 * expectedReward (strictThresholdRule m) laws := by
  obtain ⟨m, hlt, hle⟩ := exists_median_listMax laws
  exact ⟨m, expectedMax_le_two_mul_expectedReward_median laws hlt hle⟩

/-! ### Tightness -/

/-- The value `k + 1` with probability `1/(k + 1)`, and `0` otherwise. -/
noncomputable def longShot (k : ℕ) : PMF ℝ≥0 :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin (k + 1))).map
    fun i => if i.val = 0 then (k + 1 : ℝ≥0) else 0

theorem tsum_longShot_mul (k : ℕ) (f : ℝ≥0 → ℝ≥0∞) :
    ∑' x, longShot k x * f x = (f (k + 1) + k * f 0) / (k + 1) := by
  rw [longShot, Cslib.Probability.PMF.tsum_map_mul, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_one_ne_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [ENNReal.div_eq_inv_mul]

/-- The tight instance: a sure value `1`, then `longShot k`. -/
noncomputable def tightLaws (k : ℕ) : List (PMF ℝ≥0) := [PMF.pure 1, longShot k]

theorem tightLaws_eq (k : ℕ) : tightLaws k = [PMF.pure 1, longShot k] := by
  unfold tightLaws; rfl

/-- The expectation under a point mass is the value at the point. -/
theorem tsum_pure_mul {α : Type*} (a : α) (f : α → ℝ≥0∞) :
    ∑' x, PMF.pure a x * f x = f a := by
  rw [tsum_eq_single a fun b hb => by simp [PMF.pure_apply, hb]]
  simp

/-- On `tightLaws k`, every rule, even one using the whole history, collects at most `1`. -/
theorem expectedReward_tightLaws_le (k : ℕ) (stop : List ℝ≥0 → Bool) :
    expectedReward stop (tightLaws k) ≤ 1 := by
  rw [expectedReward, tightLaws, tsum_jointLaw_cons_mul, tsum_pure_mul, tsum_jointLaw_cons_mul]
  simp only [tsum_jointLaw_nil_mul]
  by_cases h1 : stop [1] = true
  · simp only [payoff_cons, h1, ↓reduceIte]
    exact (tsum_pmf_mul_const _ _).le.trans (by simp)
  · calc ∑' y, longShot k y * payoff stop reward [] [1, y]
        ≤ ∑' y, longShot k y * (y : ℝ≥0∞) := tsum_le_tsum fun y => by
          gcongr longShot k y * ?_
          simp only [payoff_cons, h1, Bool.false_eq_true, ↓reduceIte]
          exact (payoff_le_listMax stop [1] [y]).trans (by simp [listMax])
      _ = 1 := by
        rw [tsum_longShot_mul]
        simpa using ENNReal.div_self (a := (k : ℝ≥0∞) + 1) (by positivity) (by finiteness)

theorem expectedMax_tightLaws (k : ℕ) : expectedMax (tightLaws k) = (2 * k + 1) / (k + 1) := by
  rw [expectedMax, tightLaws, tsum_jointLaw_cons_mul, tsum_pure_mul, tsum_jointLaw_cons_mul]
  simp only [tsum_jointLaw_nil_mul]
  have h1 : (listMax [1, (k : ℝ≥0) + 1] : ℝ≥0∞) = k + 1 := by simp [listMax]
  have h0 : (listMax [1, 0] : ℝ≥0∞) = 1 := by simp [listMax]
  rw [tsum_longShot_mul]
  simp only [h1, h0, mul_one]
  congr 1
  ring

/-- **The factor `1/2` is optimal.** For every `c > 1/2` there are two independent finitely
supported values on which every stopping rule collects less than `c · E[max]`. -/
theorem exists_tightLaws_lt {c : ℝ≥0∞} (hc : 1 < 2 * c) :
    ∃ k, ∀ stop, expectedReward stop (tightLaws k) < c * expectedMax (tightLaws k) := by
  suffices h : ∃ k, 1 < c * expectedMax (tightLaws k) by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, fun stop => (expectedReward_tightLaws_le k stop).trans_lt hk⟩
  rcases eq_or_ne c ⊤ with rfl | hct
  · refine ⟨0, ?_⟩
    rw [expectedMax_tightLaws]
    simp
  lift c to ℝ≥0 using hct
  have hc1 : (1 : ℝ≥0) < 2 * c := by exact_mod_cast hc
  have hc' : (1 : ℝ) < 2 * c := by exact_mod_cast hc1
  obtain ⟨k, hk⟩ := exists_nat_gt ((1 - c) / (2 * c - 1) : ℝ)
  refine ⟨k, ?_⟩
  rw [div_lt_iff₀ (by linarith)] at hk
  have h1 : ((k : ℝ) + 1) < c * (2 * k + 1) := by nlinarith
  have h2 : ((k : ℝ≥0) + 1) < c * (2 * k + 1) := by
    rw [← NNReal.coe_lt_coe]; push_cast; exact h1
  have h3 : ((k : ℝ≥0∞) + 1) < c * (2 * k + 1) := by exact_mod_cast h2
  rw [expectedMax_tightLaws, ← mul_div_assoc,
    ENNReal.lt_div_iff_mul_lt (Or.inl (by positivity)) (Or.inl (by finiteness)), one_mul]
  exact h3

end Cslib.Probability.OptimalStopping.Prophet
