/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.RootMetric
public import Complexity.Foundations.Probability.HeavyCount
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional rarity and deterministic mean errors

A rare row event reduces the integrated contribution of a deterministic endpoint error
by its conditional probability, even when endpoint retention events are dependent.
The conditioning slice includes both the source and the endpoint. Empty slices and empty
environments are allowed: the hypotheses use cardinalities instead of conditional division.

The error table `b x y` is independent of the environment. The row quantity may depend on
which endpoints were retained, provided its power is bounded by the sum of endpoint error
powers. This includes the retained-row supremum used in the compression argument.
Arbitrary random noise cannot use the same rarity factor, since it may be concentrated on
the rare event.

These are the integrated, exponent-parametric assertions in the proof of
[OpenAI2026LogSpace, Lemma 8.4, Section 8.4], at revision `7ef5c0cc`. They apply in particular
to fourth moments. They do not assert the recursive estimator's induction or space bound.

## Main results

* `Cslib.rowNormPow_event_le`: conditional rarity contracts deterministic endpoint errors.
* `Cslib.vertexNormPow_event_le_rowNormPow`: the corresponding bound for a row error dominated
  by the endpoint error powers.
* `Cslib.vertexNormPow_kthLargest_event_le`: rarity bounds the actual retained-row maximum.
* `Cslib.vertexNormPow_heavyCountEvent_le`: the bound with the concrete heavy-count event and
  its explicit factor derived from the row-mass and conditional pair estimates.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, Lemma 8.4, revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

private theorem sum_masked_const_le {ι : Type*} [Fintype ι]
    (E F : Ω → ι → Prop) [∀ σ i, Decidable (E σ i)] [∀ σ i, Decidable (F σ i)]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {q : ℝ}
    (h : ∀ i, (#{σ | E σ i} : ℝ) ≤ q * #{σ | F σ i}) :
    (∑ σ, ∑ i, if E σ i then w i else 0) ≤
      q * ∑ σ, ∑ i, if F σ i then w i else 0 := by
  rw [sum_comm, sum_comm (f := fun σ i => if F σ i then w i else 0), mul_sum]
  refine sum_le_sum fun i _ => ?_
  simp only [← sum_filter, sum_const, nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (h i) (hw i)).trans_eq (by ring)

variable {s : ℕ} {N u : ℝ} {X Y Θ : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
  [∀ σ x, Decidable (Θ σ x)]

/-- Conditional rarity on each source/endpoint slice contracts the integrated power norm of
a deterministic error table. The exponent is positive; zero powers do not preserve masking.
No independence between the two masks or the row event is required. -/
theorem rowNormPow_event_le (hs : s ≠ 0) (hNu : 0 ≤ N * u) {q : ℝ}
    (hrare : ∀ x y, (#{σ | X σ x ∧ Y σ y ∧ Θ σ x} : ℝ) ≤
      q * #{σ | X σ x ∧ Y σ y}) (b : V → V → ℝ) :
    rowNormPow s N u X Y (fun σ x y => if Θ σ x then b x y else 0) ≤
      q * rowNormPow s N u X Y (fun _ x y => b x y) := by
  have hsum := sum_masked_const_le
    (fun σ (i : V × V) => X σ i.1 ∧ Y σ i.2 ∧ Θ σ i.1)
    (fun σ (i : V × V) => X σ i.1 ∧ Y σ i.2)
    (fun i => |b i.1 i.2| ^ s) (fun _ => by positivity) (fun i => hrare i.1 i.2)
  have hpoint (σ : Ω) :
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V),
        |if Θ σ x then b x y else 0| ^ s) =
      ∑ i : V × V, if X σ i.1 ∧ Y σ i.2 ∧ Θ σ i.1 then |b i.1 i.2| ^ s else 0 := by
    rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : X σ x <;> by_cases hΘ : Θ σ x <;> simp [hx, hΘ, sum_filter, hs]
  have hpoint' (σ : Ω) :
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), |b x y| ^ s) =
      ∑ i : V × V, if X σ i.1 ∧ Y σ i.2 then |b i.1 i.2| ^ s else 0 := by
    rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : X σ x <;> simp [hx, sum_filter]
  simp only [rowNormPow, expect_eq_sum_div_card, card_univ, hpoint, hpoint']
  calc
    _ ≤ (N * u)⁻¹ *
        ((q * ∑ σ, ∑ i : V × V,
          if X σ i.1 ∧ Y σ i.2 then |b i.1 i.2| ^ s else 0) / Fintype.card Ω) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)) (inv_nonneg.mpr hNu)
    _ = _ := by ring

/-- A retained-row supremum, or any row error dominated by the sum of deterministic endpoint
error powers, gains the same conditional rarity factor. Dependence of the row quantity on the
retained set is allowed; the endpoint magnitudes `b x y` are fixed. -/
theorem vertexNormPow_event_le_rowNormPow (hs : s ≠ 0) (hNu : 0 ≤ N * u) {q : ℝ}
    (hrare : ∀ x y, (#{σ | X σ x ∧ Y σ y ∧ Θ σ x} : ℝ) ≤
      q * #{σ | X σ x ∧ Y σ y}) (b : V → V → ℝ) (v : Ω → V → ℝ)
    (hv : ∀ σ x, X σ x → |v σ x| ^ s ≤
      ∑ y ∈ ({y | Y σ y} : Finset V), |b x y| ^ s) :
    vertexNormPow s N u X (fun σ x => if Θ σ x then v σ x else 0) ≤
      q * rowNormPow s N u X Y (fun _ x y => b x y) := by
  calc
    _ ≤ rowNormPow s N u X Y (fun σ x y => if Θ σ x then b x y else 0) := by
      unfold vertexNormPow rowNormPow
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      refine sum_le_sum fun x hx => ?_
      by_cases hΘ : Θ σ x
      · simp only [hΘ, ↓reduceIte]
        exact hv σ x (mem_filter.mp hx).2
      · simp [hΘ, hs]
    _ ≤ _ := rowNormPow_event_le hs hNu hrare b

omit [Fintype V] in
private theorem abs_kthLargest_pow_le_sum (S : Finset V) (b : V → ℝ)
    (hs : s ≠ 0) : |kthLargest 1 S (fun y => |b y|)| ^ s ≤ ∑ y ∈ S, |b y| ^ s := by
  classical
  have hmem : kthLargest 1 S (fun y => |b y|) ∈
      insert 0 ((S.filter fun y => 1 ≤ #{w ∈ S | |b y| ≤ |b w|}).image fun y => |b y|) :=
    max'_mem _ _
  rcases mem_insert.mp hmem with hz | hmem
  · rw [hz, abs_zero, zero_pow hs]
    positivity
  · obtain ⟨y, hy, heq⟩ := mem_image.mp hmem
    rw [← heq, abs_abs]
    exact single_le_sum (f := fun y => |b y| ^ s)
      (fun _ _ => by positivity) (mem_filter.mp hy).1

/-- Conditional rarity controls the maximum deterministic error magnitude among retained
endpoints, with zero as the maximum of an empty row. -/
theorem vertexNormPow_kthLargest_event_le (hs : s ≠ 0) (hNu : 0 ≤ N * u) {q : ℝ}
    (hrare : ∀ x y, (#{σ | X σ x ∧ Y σ y ∧ Θ σ x} : ℝ) ≤
      q * #{σ | X σ x ∧ Y σ y}) (b : V → V → ℝ) :
    vertexNormPow s N u X (fun σ x =>
      if Θ σ x then kthLargest 1 {y | Y σ y} (fun y => |b x y|) else 0) ≤
      q * rowNormPow s N u X Y (fun _ x y => b x y) :=
  vertexNormPow_event_le_rowNormPow hs hNu hrare b _
    (fun _ _ _ => abs_kthLargest_pow_le_sum _ _ hs)

open Classical in
/-- **The heavy-count rarity gain for a retained-row mean error.** The pair bound is stated on
the actual source/usage-endpoint slice. The rank channel `Y` may have a wider rate than `Yt`;
only the explicit conditional bound is used. This is the mean-error portion of
[OpenAI2026LogSpace, Lemma 8.4], with an explicit constant and arbitrary positive exponent. -/
theorem vertexNormPow_heavyCountEvent_le (hs : s ≠ 0) (hNu : 0 ≤ N * u)
    (X Y Yt : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Yt σ y)]
    {a ρ c M : ℝ} {n : ℕ} (ha : 0 ≤ a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hc : 0 ≤ c) (hn : 0 < n) (d : V → V → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (hmass : ∀ x, a * ∑ y, d x y ≤ M)
    (hpair : ∀ x y w, ρ / 4 < d x w → w ≠ y →
      (#{σ | X σ x ∧ Yt σ y ∧ Y σ w} : ℝ) ≤
        c * a * #{σ | X σ x ∧ Yt σ y}) (b : V → V → ℝ) :
    vertexNormPow s N u X (fun σ x =>
      if Probability.heavyCountEvent Y univ (d x) ρ n σ then
        kthLargest 1 {y | Yt σ y} (fun y => |b x y|) else 0) ≤
      (2 * (1 + 4 * c * M) / ((n : ℝ) * ρ)) *
        rowNormPow s N u X Yt (fun _ x y => b x y) := by
  classical
  refine vertexNormPow_kthLargest_event_le hs hNu (fun x y => ?_) b
  have h := Probability.card_filter_heavyCountEvent_le Y
    ({σ | X σ x ∧ Yt σ y} : Finset Ω) univ y ha hρ hρ1 hc (fun w _ => hd x w) (hmass x)
    (fun w _ hdw hwy => ?_) hn
  · simpa only [filter_filter, and_assoc] using h
  · simpa only [filter_filter, and_assoc] using hpair x y w hdw hwy

end Cslib
