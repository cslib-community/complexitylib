/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
import Mathlib.Tactic.Linarith

/-!
# Conditional sampling inside a union of masks

Let `P` and `Q` be independent random masks of rates `p` and `q`. Their union `S` has rate
`p + q - p q`, and conditionally on `S`, the difference `P \ Q` selects each coordinate of `S`
independently with rate `conditionalSamplingRate p q = p (1 - q) / (p + q - p q)`
(`bernoulliAverage_union_difference`). The law is stated as an equality of finite expectations for
any rate `r` with `(p + q - p q) r = p (1 - q)`, so it avoids conditioning on events of probability
zero and covers degenerate rates. This is the coordinate-sampling step of Korten's proof of the
mirror-set lemma [Korten2026].

## Main definitions

* `Cslib.BitString.conditionalSamplingRate`: the conditional rate of `P \ Q` inside `P ∪ Q`.

## Main results

* `Cslib.BitString.bernoulliAverage_union_difference`: the joint law of `P ∪ Q` and
  `P \ Q`.
* `Cslib.BitString.bernoulliAverage_union_difference_subtype`: the same, with the difference
  as a mask on the coordinates of the union.
* `Cslib.BitString.conditionalSamplingRate_nonneg`,
  `Cslib.BitString.conditionalSamplingRate_le_one`,
  `Cslib.BitString.conditionalSamplingRate_le_div`: the conditional rate is a probability,
  at most `p / q`.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- The rate `p (1 - q) / (p + q - p q)` at which the difference `P \ Q` of independent masks of
rates `p` and `q` selects the coordinates of their union `P ∪ Q`. -/
noncomputable def conditionalSamplingRate (p q : ℝ) : ℝ :=
  p * (1 - q) / (p + q - p * q)

/-- The conditional rate solves `(p + q - p q) r = p (1 - q)` when the union has positive rate. -/
theorem mul_conditionalSamplingRate {p q : ℝ} (h : p + q - p * q ≠ 0) :
    (p + q - p * q) * conditionalSamplingRate p q = p * (1 - q) :=
  mul_div_cancel₀ _ h

private theorem add_sub_mul_pos {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    0 < p + q - p * q := by
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')]

/-- For `p ≥ 0` and `0 ≤ q ≤ 1`, the conditional rate is nonnegative. -/
theorem conditionalSamplingRate_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    0 ≤ conditionalSamplingRate p q :=
  div_nonneg (mul_nonneg hp (sub_nonneg.mpr hq'))
    (by nlinarith [mul_nonneg hp (sub_nonneg.mpr hq')])

/-- For `p ≥ 0` and `0 < q ≤ 1`, the conditional rate is at most one. -/
theorem conditionalSamplingRate_le_one {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    conditionalSamplingRate p q ≤ 1 := by
  apply (div_le_one (add_sub_mul_pos hp hq hq')).mpr
  linarith

/-- For `p ≥ 0` and `0 < q ≤ 1`, the conditional rate is at most `p / q`. -/
theorem conditionalSamplingRate_le_div {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hq' : q ≤ 1) :
    conditionalSamplingRate p q ≤ p / q := by
  apply (div_le_div_iff₀ (add_sub_mul_pos hp hq hq') hq).mpr
  nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hq'), mul_nonneg hp (sq_nonneg q)]

/-- **The joint law of `P ∪ Q` and `P \ Q`**: for independent masks `P` and `Q` of rates `p` and
`q`, the union and the difference are distributed as a mask `S` of rate `p + q - p q` and the
part inside `S` of an independent mask of rate `r`, when `(p + q - p q) r = p (1 - q)`. -/
theorem bernoulliAverage_union_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ) (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (ι → Bool) → (ι → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (fun T =>
        f S (fun i => S i && T i))) := by
  let g (z : ι → Bool × Bool) : ℝ := f (fun i => (z i).1) (fun i => (z i).2)
  refine (bernoulliAverage_bernoulliAverage_eq_sum p q (fun b c => (b || c, b && !c)) g).trans
    (Eq.trans ?_
      (bernoulliAverage_bernoulliAverage_eq_sum (p + q - p * q) r (fun s t => (s, s && t)) g).symm)
  refine sum_congr rfl fun a _ => congrArg _ (prod_congr rfl fun i _ => ?_)
  obtain ⟨b, c⟩ := a i
  cases b <;> cases c <;> simp only [Bool.or_self, Bool.or_true, Bool.or_false,
    Bool.not_true, Bool.not_false, Bool.and_self, Bool.and_true, Bool.and_false,
    Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true,
    and_self, and_true, and_false, ↓reduceIte, mul_zero, add_zero,
    zero_add] <;> linarith

/-- The joint law of `P ∪ Q` and `P \ Q`, with the difference as a mask on the coordinates of the
union. -/
theorem bernoulliAverage_union_difference_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q r : ℝ) (hr : (p + q - p * q) * r = p * (1 - q))
    (f : (S : ι → Bool) → ({i // S i = true} → Bool) → ℝ) :
    bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
      f (fun i => P i || Q i) (fun i => P i && !Q i))) =
      bernoulliAverage (p + q - p * q) (fun S => bernoulliAverage r (f S)) := by
  change bernoulliAverage p (fun P => bernoulliAverage q (fun Q =>
    (fun S R => f S (fun i => R i)) (fun i => P i || Q i)
      (fun i => P i && !Q i))) = _
  rw [bernoulliAverage_union_difference p q r hr (fun S R => f S (fun i => R i))]
  congr 1
  funext S
  have he (T : ι → Bool) : (fun i : {i // S i = true} => S i && T i) =
      (fun i : {i // S i = true} => T i) := by
    funext i
    simp only [i.property, Bool.true_and]
  simp_rw [he]
  exact bernoulliAverage_restrict r S (f S)

end Cslib.BitString
