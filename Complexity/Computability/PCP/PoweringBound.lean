/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Power
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The powering bound

Powering amplifies the value of a regular constraint graph on an expander
[Dinur, Section 5][Dinur2005]. For a killing rate `q ≥ 2` and walks truncated at
`T = 4 |α| (q - 1)` steps, the value of the powered constraint graph `R.power T q` is at least

`(q - 1) / (4 |α| ^ 2 + 16 |α| ^ 4 + 128 |α| ^ 5 / (1 - μ)) * min (UNSAT R) (1 / T ^ 2)`

when the spectral expansion of `R` is at most `μ < 1` (`le_unsatVal_power`). The factor grows
linearly with `q`, while the alphabet of the powered constraint graph depends on `q`, `|α|` and the
degree of `R` only: this is the gap amplification of Dinur's proof. The proof follows Dinur's
[Arora and Barak, Chapter 22][AroraBarak09], along killed walks [Radhakrishnan2006]
[Dinur, Section 9][Dinur2005], which gain a factor linear in their expected length where Dinur's
walks of fixed length `t` gain `√t`; as their lengths are random already, `R` needs no self-loops.

* **Decoding.** A labelling `A` of the powered constraint graph is decoded into the labelling
  `R.decode T q A` of `R`: the label of `v` is the one most often *reported* about `v` by the far
  ends of the killed walks from `v` (`report`), so that a proportion at least `1 / |α|` of them
  report it (`inv_card_le_expect_report_eq_decode`). Killed at step `ℓ`, a killed walk is a
  uniformly random walk of length `ℓ`, so the walks of length at most `H` reporting the decoded
  label, weighted by the law of the kill time, have total weight at least
  `1 / |α| - (1 - 1 / q) ^ (H + 1)` (`inv_card_sub_le_sum_truthProb`).
* **First moment.** A killed walk is *hit* at a step (`Cslib.PCP.RegularConstraintGraph.Hit`) when
  the decoding violates the dart crossed there while both ends of the walk hold truthful opinions
  about it, and a killed walk hit at some step is violated. Split at a step, a uniformly random
  killed walk crosses a uniformly random dart, and the pieces before and after are independent
  uniformly random walks (`expect_killTime_eq_and_hit`), whose lengths, up to the truncation, are
  independent with the law of the kill time. So a uniformly random killed walk is hit at least
  `(q - 1) (1 / |α| - (1 - 1 / q) ^ (H + 1)) ^ 2 ε` times on average, where `ε` is the proportion of
  the darts violated by the decoding (`le_expect_numHits`).
* **Second moment.** Two steps `i < j` of a uniformly random walk cross violated darts with
  probability at most `ε ^ 2 + λ ^ (j - (i + 1)) ε`, where `λ` is the spectral expansion of `R`
  (`expect_mem_unsatEdges_mul_le`), so the number of hits has second moment at most its first
  moment plus `T ^ 2 ε ^ 2 + 2 T ε / (1 - λ)` (`expect_numHits_sq_le`).
* **The second moment method.** The number of hits is nonzero with probability at least the square
  of its first moment over its second moment, which bounds the proportion of violated killed walks
  (`le_unsatFrac_power`, `le_unsatVal_power_of_le`).

Probabilities are uniform averages `𝔼` of indicators, over the darts of the powered constraint
graph, that is over uniformly random starts, labels and kill signals.

## Main definitions

* `Cslib.PCP.RegularConstraintGraph.numHits`: the number of steps at which a killed walk is hit.

## Main results

* `Cslib.PCP.RegularConstraintGraph.expect_killTime_eq_and_hit`: the crossing count.
* `Cslib.PCP.RegularConstraintGraph.le_expect_numHits`: the first moment.
* `Cslib.PCP.RegularConstraintGraph.expect_numHits_sq_le`: the second moment.
* `Cslib.PCP.RegularConstraintGraph.le_unsatFrac_power`,
  `Cslib.PCP.RegularConstraintGraph.le_unsatVal_power_of_le`: the powering bound, for any admissible
  constants.
* `Cslib.PCP.RegularConstraintGraph.le_unsatVal_power_min`: the standard first-moment coefficient,
  retaining a supplied soundness threshold in the second-moment bound.
* `Cslib.PCP.RegularConstraintGraph.le_unsatVal_power`: the powering bound, with explicit
  parameters.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib

open Finset
open scoped BigOperators

/-! ### Auxiliary inequalities -/

section Auxiliary

/-- The weights `x ^ (j - (i + 1))` of the steps `j` after a step `i` sum to at most
`1 / (1 - x)`, for `0 ≤ x < 1`. -/
private theorem sum_ite_lt_pow_le {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) (T i : ℕ) :
    ∑ j ∈ range T, (if i < j then x ^ (j - (i + 1)) else 0) ≤ 1 / (1 - x) := by
  rw [sum_ite, sum_const_zero, add_zero,
    show {j ∈ range T | i < j} = Ico (i + 1) T by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega,
    sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [range_eq_Ico]
  simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := T - (i + 1)) hx₀ hx₁

/-- The ratio `a ^ 2 / (a + P)` of the second moment method grows with `a`: if `e ^ 2 ≤ x (e + P)`
and `0 ≤ a ≤ e`, then `a ^ 2 ≤ x (a + P)`. -/
private theorem sq_le_mul_add_of_le {a e x P : ℝ} (ha : 0 ≤ a) (hae : a ≤ e) (hP : 0 ≤ P)
    (hx : 0 ≤ x) (h : e ^ 2 ≤ x * (e + P)) : a ^ 2 ≤ x * (a + P) := by
  rcases (add_nonneg (ha.trans hae) hP).eq_or_lt with h₀ | h₀
  · have : a = 0 := by linarith
    subst this
    simpa using mul_nonneg hx hP
  · have h₁ : a ^ 2 * (e + P) ≤ e ^ 2 * (a + P) := by
      nlinarith [mul_nonneg (mul_nonneg ha (ha.trans hae)) (sub_nonneg.2 hae),
        mul_nonneg hP (mul_nonneg (sub_nonneg.2 hae) (add_nonneg ha (ha.trans hae)))]
    have h₂ : e ^ 2 * (a + P) ≤ x * (e + P) * (a + P) :=
      mul_le_mul_of_nonneg_right h (add_nonneg ha hP)
    nlinarith

/-- Truncating the increasing second-moment ratio at any nonnegative threshold gives a linear
bound below that threshold, with its exact denominator retained. -/
private theorem mul_min_le_div {c B B' T ε u δ : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) (hBB : B ≤ B')
    (hu : 0 ≤ u) (huε : u ≤ ε) (hδ : 0 ≤ δ) :
    c ^ 2 / (c + T ^ 2 * δ + B') * min u δ ≤ c ^ 2 * ε / (c + T ^ 2 * ε + B) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  set m := min u δ
  have hm₀ : 0 ≤ m := le_min hu hδ
  have hmε : m ≤ ε := (min_le_left _ _).trans huε
  have hTm : T ^ 2 * m ≤ T ^ 2 * δ :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg T)
  have hε₀ : 0 ≤ ε := hm₀.trans hmε
  calc c ^ 2 / (c + T ^ 2 * δ + B') * m = c ^ 2 * m / (c + T ^ 2 * δ + B') := by ring
    _ ≤ c ^ 2 * m / (c + T ^ 2 * m + B) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ ≤ c ^ 2 * ε / (c + T ^ 2 * ε + B) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) (add_nonneg hc.le hB)) (sub_nonneg.2 hmε)]

/-- **Bernoulli's inequality**, for the survival of killed walks: for `q ≥ 2` and `K ≥ 1`, a walk
killed before each step with probability `1 / q` survives its first `2 K (q - 1)` steps with
probability at most `1 / (2 K)`. -/
private theorem one_sub_inv_pow_le {q K : ℕ} (hq : 2 ≤ q) (hK : 1 ≤ K) :
    (1 - (q : ℝ)⁻¹) ^ (2 * K * (q - 1)) ≤ (2 * K : ℝ)⁻¹ := by
  have hq₁ : (0 : ℝ) < q - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hr : 1 - (q : ℝ)⁻¹ = (1 + ((q : ℝ) - 1)⁻¹)⁻¹ := by
    field_simp
    ring
  have hn : ((2 * K * (q - 1) : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ = 2 * K := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
    field_simp
  have hb := one_add_mul_le_pow (a := ((q : ℝ) - 1)⁻¹) (by linarith [inv_pos.2 hq₁])
    (2 * K * (q - 1))
  rw [hn] at hb
  rw [hr, inv_pow]
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  exact inv_anti₀ (by positivity) (by linarith)

end Auxiliary

namespace PCP

open RotationMap

namespace RegularConstraintGraph

variable {V D α : Type*} (R : RegularConstraintGraph V D α) (T q : ℕ) [NeZero q]

/-! ### The crossing count -/

/-- A walk of length `ℓ`, split at its step `i` into the dart `y.1` crossed there, the reverse
`y.2.1` of the steps before it and the steps `y.2.2` after it, is *hit* when `σ` violates the dart
and the reports along `y.2.1` and `y.2.2` about the two ends of the dart are truthful. -/
private def SplitHit (A : V → WalkLabels D T → α) (σ : V → α) {ℓ i : ℕ} (hi : i ≤ T)
    (hj : ℓ - (i + 1) ≤ T) (y : (V × D) × (Fin i → D) × (Fin (ℓ - (i + 1)) → D)) : Prop :=
  ¬ R.toConstraintGraph.Satisfies σ y.1 ∧ R.report T A hi (y.1.1, y.2.1) = σ y.1.1 ∧
    R.report T A hj ((R.graph.rot y.1).1, y.2.2) = σ (R.graph.rot y.1).1

/-- A killed walk killed at step `ℓ < T` is hit at its step `i < ℓ` exactly when its walk of length
`ℓ`, split at step `i`, is hit. -/
private theorem hit_iff_splitHit (A : V → WalkLabels D T → α) (σ : V → α)
    (p : V × (Fin T → D) × (Fin T → Fin q)) (hℓ : killTime p.2.2 < T) {i : ℕ}
    (hi : i < killTime p.2.2) :
    R.Hit T q A σ p i ↔ R.SplitHit T A σ (hi.le.trans hℓ.le) ((Nat.sub_le _ _).trans hℓ.le)
      (R.graph.splitWalk ⟨i, hi⟩ (p.1, Fin.take _ hℓ.le p.2.1)) := by
  let y := R.graph.splitWalk ⟨i, hi⟩ (p.1, Fin.take _ hℓ.le p.2.1)
  have e₁ : y.1 = R.graph.walkDart (p.1, p.2.1) ⟨i, hi.trans hℓ⟩ :=
    R.graph.walkDart_take (p.1, p.2.1) hℓ.le ⟨i, hi⟩
  -- the reverse of the steps before step `i` leads back to the start of `p`
  have e₂ : R.report T A (hi.le.trans hℓ.le) (y.1.1, y.2.1) =
      A p.1 (.take i (hi.le.trans hℓ.le) p.2.1) := by
    rw [show (y.1.1, y.2.1) =
        (R.graph.pow i).rot (p.1, Fin.take i hi.le (Fin.take _ hℓ.le p.2.1)) from
      Prod.ext (R.graph.fst_rot_pow_take (p.1, Fin.take _ hℓ.le p.2.1) hi.le).symm rfl,
      report_rot_pow]
    rfl
  -- the steps after step `i` lead on to the end of `p`, and their reverse is read there
  have e₃ : R.report T A ((Nat.sub_le _ _).trans hℓ.le) ((R.graph.rot y.1).1, y.2.2) =
      A ((R.graph.killedPow T q).rot p).1 (.take (killTime p.2.2 - (i + 1))
        ((Nat.sub_le _ _).trans (killTime_le _)) ((R.graph.killedPow T q).rot p).2.1) := by
    rw [show ((R.graph.rot y.1).1, y.2.2) =
        R.graph.walkDrop (p.1, Fin.take _ hℓ.le p.2.1) (i + 1) from
      Prod.ext (R.graph.fst_rot_walkDart _ ⟨i, hi⟩) rfl,
      report, R.graph.rot_pow_walkDrop, R.graph.rot_pow_killTime T q p]
    rfl
  have e₄ : σ (R.graph.rot y.1).1 =
      R.truthful T σ ((R.graph.killedPow T q).rot p).1 (.take (killTime p.2.2 - (i + 1))
        ((Nat.sub_le _ _).trans (killTime_le _)) ((R.graph.killedPow T q).rot p).2.1) := by
    change σ (R.graph.rot (R.graph.walkDart (p.1, Fin.take _ hℓ.le p.2.1) ⟨i, hi⟩)).1 = _
    rw [R.truthful_take_rot_killedPow T q σ p (Nat.sub_le _ _),
      Nat.sub_sub_self (Nat.succ_le_of_lt hi), R.graph.fst_rot_walkDart _ ⟨i, hi⟩]
    exact congrArg σ (R.graph.walkAt_take (p.1, p.2.1) hℓ.le (Nat.succ_le_of_lt hi))
  rw [SplitHit, e₂, e₃, e₄, e₁, walkDart_fst, ← R.truthful_take T σ p.1 (hi.le.trans hℓ.le)]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hi, h⟩⟩

open Classical in
/-- **The crossing count** [Dinur, Section 5.1][Dinur2005]: a uniformly random killed walk is
killed at its step `ℓ < T` and hit at its step `i < ℓ` with probability `(1 - 1 / q) ^ ℓ / q` times
the average over the darts `d` violated by `σ` of the product of the proportion of the walks of
length `i` from the start of `d` and the proportion of the walks of length `ℓ - (i + 1)` from the
end of `d` whose far ends report `σ` truthfully. Split at step `i`, the killed walk crosses a
uniformly random dart, and its pieces before and after are independent uniformly random walks. -/
theorem expect_killTime_eq_and_hit [Fintype V] [Fintype D] [Nonempty D]
    (A : V → WalkLabels D T → α) (σ : V → α) {ℓ i : ℕ} (hℓ : ℓ < T) (hi : i < ℓ) :
    𝔼 p : V × (Fin T → D) × (Fin T → Fin q),
        (if killTime p.2.2 = ℓ ∧ R.Hit T q A σ p i then 1 else 0 : ℝ) =
      (1 - (q : ℝ)⁻¹) ^ ℓ / q * 𝔼 d : V × D,
        (if d ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) * R.truthProb T A σ d.1 i *
          R.truthProb T A σ (R.graph.rot d).1 (ℓ - (i + 1)) := by
  have hiT : i ≤ T := hi.le.trans hℓ.le
  have hjT : ℓ - (i + 1) ≤ T := (Nat.sub_le _ _).trans hℓ.le
  -- the right-hand side, as an average over the walks of length `ℓ` split at step `i`
  have hrhs : 𝔼 d : V × D, (if d ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) *
        R.truthProb T A σ d.1 i * R.truthProb T A σ (R.graph.rot d).1 (ℓ - (i + 1)) =
      𝔼 w : V × (Fin ℓ → D),
        if R.SplitHit T A σ hiT hjT (R.graph.splitWalk ⟨i, hi⟩ w) then 1 else 0 := by
    rw [R.graph.expect_splitWalk ⟨i, hi⟩ fun y ↦ if R.SplitHit T A σ hiT hjT y then 1 else 0]
    refine expect_congr rfl fun d _ ↦ ?_
    have h (r : Fin i → D) (s : Fin (ℓ - (i + 1)) → D) :
        (if R.SplitHit T A σ hiT hjT (d, r, s) then 1 else 0 : ℝ) =
          (if d ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) *
            (if R.report T A hiT (d.1, r) = σ d.1 then 1 else 0) *
              (if R.report T A hjT ((R.graph.rot d).1, s) = σ (R.graph.rot d).1 then 1 else 0) := by
      simp only [SplitHit, ConstraintGraph.mem_unsatEdges]
      by_cases h₁ : R.toConstraintGraph.Satisfies σ d <;>
        by_cases h₂ : R.report T A hiT (d.1, r) = σ d.1 <;>
        by_cases h₃ : R.report T A hjT ((R.graph.rot d).1, s) = σ (R.graph.rot d).1 <;>
        simp only [h₁, h₂, h₃, not_true_eq_false, not_false_eq_true, true_and, false_and,
          and_false, ↓reduceIte, mul_one, mul_zero]
    simp only [h, truthProb, dite_eq_left hiT, dite_eq_left hjT, ← mul_expect, ← expect_mul,
      mul_assoc]
  rw [hrhs, ← expect_prod_ite_killTime_eq hℓ]
  refine expect_congr rfl fun p _ ↦ ?_
  by_cases h : killTime p.2.2 = ℓ
  · subst h
    simp only [true_and, ite_true, R.hit_iff_splitHit T q A σ p hℓ hi]
  · simp [h]

/-! ### The first moment -/

open Classical in
/-- The number of steps at which the killed walk `p` is hit by the labelling `A` of the powered
constraint graph, relative to the labelling `σ` of `R`. -/
noncomputable def numHits (A : V → WalkLabels D T → α) (σ : V → α)
    (p : V × (Fin T → D) × (Fin T → Fin q)) : ℕ :=
  #{i ∈ range T | R.Hit T q A σ p i}

open Classical in
/-- The number of hits is the sum of the indicators of the hits at the steps before `T`. -/
private theorem numHits_eq_sum (A : V → WalkLabels D T → α) (σ : V → α)
    (p : V × (Fin T → D) × (Fin T → Fin q)) :
    (R.numHits T q A σ p : ℝ) = ∑ i ∈ range T, if R.Hit T q A σ p i then 1 else 0 := by
  rw [numHits, card_filter]
  push_cast
  rfl

open Classical in
/-- A killed walk hit at step `i` is killed at a single step `i + j + 1`, so the indicators over
`j ∈ range (H + 1)` sum to at most the indicator of `R.Hit T q A σ p i`. -/
private theorem sum_ite_killTime_eq_and_hit_le (A : V → WalkLabels D T → α) (σ : V → α)
    (H i : ℕ) (p : V × (Fin T → D) × (Fin T → Fin q)) :
    ∑ j ∈ range (H + 1), (if killTime p.2.2 = i + j + 1 ∧ R.Hit T q A σ p i then 1 else 0 : ℝ) ≤
      if R.Hit T q A σ p i then 1 else 0 := by
  by_cases h : R.Hit T q A σ p i
  · have hk := h.lt_killTime
    simp only [h, and_true, ↓reduceIte]
    rw [sum_congr rfl fun j _ ↦ if_congr (show killTime p.2.2 = i + j + 1 ↔
      j = killTime p.2.2 - (i + 1) by omega) rfl rfl, sum_ite_eq']
    split_ifs <;> norm_num
  · simp [h]

/-- The kill time `i + j + 1` has `q - 1` times the product of the probabilities of `i` and `j`, so
`(q - 1) * (b * (∑ i, P i * x i) * (∑ j, P j * y j))` expands as the double sum with weight
`P (i + j + 1)`. -/
private theorem sub_one_mul_sum_mul_sum_eq (H : ℕ) (b : ℝ) (x y : ℕ → ℝ) :
    ((q : ℝ) - 1) * (b * ((∑ i ∈ range (H + 1), (1 - (q : ℝ)⁻¹) ^ i / q * x i) *
      ∑ j ∈ range (H + 1), (1 - (q : ℝ)⁻¹) ^ j / q * y j)) =
      ∑ i ∈ range (H + 1), ∑ j ∈ range (H + 1),
        (1 - (q : ℝ)⁻¹) ^ (i + j + 1) / q * (b * x i * y j) := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  rw [sum_mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [pow_succ, pow_add]
  field_simp

open Classical in
/-- **The first moment** [Dinur, Lemma 5.1][Dinur2005]: for `2 H + 1 < T`, a uniformly random
killed walk is hit by a labelling `A` of the powered constraint graph, relative to its plurality
decoding, at least `(q - 1) (1 / |α| - (1 - 1 / q) ^ (H + 1)) ^ 2` times the proportion of the darts
violated by the decoding many times on average.

The killed walks hit at a step `i ≤ H` and killed at step `i + j + 1` for `j ≤ H` are counted by
the crossing count `expect_killTime_eq_and_hit`, and the probability `(1 - 1 / q) ^ (i + j + 1) / q`
of the kill time is `q - 1` times the product of those of the kill times `i` and `j`. So the count
factors, at every violated dart, into a product of two weighted proportions of truthful walks, one
from each end of the dart, each of which is bounded below by plurality
(`inv_card_sub_le_sum_truthProb`). -/
theorem le_expect_numHits [Fintype V] [Fintype D] [Nonempty D] [Fintype α] [Nonempty α]
    (A : V → WalkLabels D T → α) {H : ℕ} (hH : 2 * H + 1 < T)
    (hα : (1 - (q : ℝ)⁻¹) ^ (H + 1) ≤ (Fintype.card α : ℝ)⁻¹) :
    ((q : ℝ) - 1) * ((Fintype.card α : ℝ)⁻¹ - (1 - (q : ℝ)⁻¹) ^ (H + 1)) ^ 2 *
        R.toConstraintGraph.unsatFrac (R.decode T q A) ≤
      𝔼 p, (R.numHits T q A (R.decode T q A) p : ℝ) := by
  set σ := R.decode T q A
  set β := (Fintype.card α : ℝ)⁻¹ - (1 - (q : ℝ)⁻¹) ^ (H + 1)
  set P : ℕ → ℝ := fun ℓ ↦ (1 - (q : ℝ)⁻¹) ^ ℓ / q
  set b : V × D → ℝ := fun d ↦ if d ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0
  set S : V → ℝ := fun u ↦ ∑ ℓ ∈ range (H + 1), P ℓ * R.truthProb T A σ u ℓ
  have hq₁ : (0 : ℝ) ≤ q - 1 := sub_nonneg.2 (Nat.one_le_cast.2 NeZero.one_le)
  have hβ : 0 ≤ β := sub_nonneg.2 hα
  have hb (d : V × D) : 0 ≤ b d := by positivity
  have hS (u : V) : β ≤ S u := R.inv_card_sub_le_sum_truthProb T q A u (by omega)
  calc ((q : ℝ) - 1) * β ^ 2 * R.toConstraintGraph.unsatFrac σ
      = 𝔼 d, (q - 1) * (b d * (β * β)) := by
        rw [← ConstraintGraph.expect_mem_unsatEdges, mul_expect]
        exact expect_congr rfl fun d _ ↦ by simp only [b]; ring
    _ ≤ 𝔼 d, (q - 1) * (b d * (S d.1 * S (R.graph.rot d).1)) :=
        expect_le_expect fun d _ ↦ mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul (hS _) (hS _) hβ (hβ.trans (hS _))) (hb d)) hq₁
    _ = ∑ i ∈ range (H + 1), ∑ j ∈ range (H + 1), P (i + j + 1) *
          𝔼 d, b d * R.truthProb T A σ d.1 i * R.truthProb T A σ (R.graph.rot d).1 j := by
        simp only [S, P, sub_one_mul_sum_mul_sum_eq q H, expect_sum_comm, mul_expect]
    _ = ∑ i ∈ range (H + 1), ∑ j ∈ range (H + 1),
          𝔼 p, (if killTime p.2.2 = i + j + 1 ∧ R.Hit T q A σ p i then 1 else 0 : ℝ) := by
        refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
        rw [mem_range] at hi hj
        rw [R.expect_killTime_eq_and_hit T q A σ (by omega) (by omega),
          show i + j + 1 - (i + 1) = j by omega]
    _ ≤ ∑ i ∈ range (H + 1), 𝔼 p, (if R.Hit T q A σ p i then 1 else 0 : ℝ) := by
        refine sum_le_sum fun i _ ↦ ?_
        rw [← expect_sum_comm]
        exact expect_le_expect fun p _ ↦ R.sum_ite_killTime_eq_and_hit_le T q A σ H i p
    _ ≤ ∑ i ∈ range T, 𝔼 p, (if R.Hit T q A σ p i then 1 else 0 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
          fun i _ _ ↦ expect_nonneg fun p _ ↦ by positivity
    _ = 𝔼 p, (R.numHits T q A σ p : ℝ) := by
        simp only [numHits_eq_sum, expect_sum_comm]

/-! ### The second moment -/

section SecondMoment

variable [Fintype V] [Fintype D]

open Classical in
/-- The square of the number of hits of a walk `p` is at most its number of hits plus the number
of ordered pairs of distinct steps that cross darts violated by `σ`. -/
private theorem numHits_sq_le_add_sum (A : V → WalkLabels D T → α) (σ : V → α)
    (p : V × (Fin T → D) × (Fin T → Fin q)) :
    (R.numHits T q A σ p : ℝ) ^ 2 ≤ R.numHits T q A σ p + ∑ i : Fin T, ∑ j : Fin T,
      if i = j then 0 else
        (if R.graph.walkDart (p.1, p.2.1) i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) *
          if R.graph.walkDart (p.1, p.2.1) j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0 := by
  set h : Fin T → ℝ := fun i ↦ if R.Hit T q A σ p i then 1 else 0
  set c : Fin T → ℝ := fun i ↦
    if R.graph.walkDart (p.1, p.2.1) i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0
  have hN : (R.numHits T q A σ p : ℝ) = ∑ i, h i := by
    rw [numHits_eq_sum, ← Fin.sum_univ_eq_sum_range]
  -- a hit at step `i` crosses a violated dart
  have hhc (i : Fin T) : h i ≤ c i := by
    simp only [h, c]
    split_ifs with h₁ h₂
    · exact le_rfl
    · exact absurd ((ConstraintGraph.mem_unsatEdges).2 h₁.2.1) h₂
    · exact zero_le_one
    · exact le_rfl
  have hh₀ (i : Fin T) : 0 ≤ h i := by
    simp only [h]
    positivity
  rw [hN, sq, sum_mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ ↦ ?_
  calc ∑ j, h i * h j
      ≤ ∑ j, ((if i = j then h j else 0) + if i = j then 0 else c i * c j) := by
        refine sum_le_sum fun j _ ↦ ?_
        by_cases hij : i = j
        · subst hij
          simp only [↓reduceIte, add_zero, h]
          split_ifs <;> norm_num
        · simp only [hij, ↓reduceIte, zero_add]
          exact mul_le_mul (hhc i) (hhc j) (hh₀ j) ((hh₀ i).trans (hhc i))
    _ = h i + ∑ j, if i = j then 0 else c i * c j := by
        rw [sum_add_distrib, Fintype.sum_ite_eq]

open Classical in
/-- Two darts of a uniformly random walk at steps `i < j` are both violated by `σ` with probability
at most `ε ^ 2 + λ ^ (j - (i + 1)) ε`, where `ε` is the proportion of violated darts and `λ` the
spectral expansion: up to that error, the two darts are independent. -/
theorem expect_mem_unsatEdges_mul_le (σ : V → α) {i j : Fin T} (hij : i < j) :
    𝔼 w : V × (Fin T → D),
        (if R.graph.walkDart w i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0 : ℝ) *
          (if R.graph.walkDart w j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) ≤
      R.toConstraintGraph.unsatFrac σ ^ 2 +
        R.graph.spectralExpansion ^ (j - (i + 1) : ℕ) * R.toConstraintGraph.unsatFrac σ := by
  set b : V × D → ℝ := fun d ↦ if d ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0
  change 𝔼 w : V × (Fin T → D), b (R.graph.walkDart w i) * b (R.graph.walkDart w j) ≤ _
  have h := R.graph.abs_expect_walkDart_mul_walkDart_sub_le hij b
  have hb : 𝔼 d, b d = R.toConstraintGraph.unsatFrac σ :=
    R.toConstraintGraph.expect_mem_unsatEdges σ
  have hb₂ : 𝔼 d, b d ^ 2 = R.toConstraintGraph.unsatFrac σ := by
    rw [← hb]
    exact expect_congr rfl fun d _ ↦ by simp only [b]; split_ifs <;> norm_num
  rw [hb, hb₂] at h
  have hlam : 0 ≤ R.graph.spectralExpansion ^ (j - (i + 1) : ℕ) :=
    pow_nonneg R.graph.spectralExpansion_nonneg _
  have := R.toConstraintGraph.unsatFrac_nonneg σ
  nlinarith [(abs_le.1 h).2, mul_nonneg hlam (sq_nonneg (R.toConstraintGraph.unsatFrac σ))]

open Classical in
/-- Two distinct crossings are almost independent: two steps `i, j : Fin T` of a random walk both
cross darts violated by `σ` with probability at most `ε ^ 2 + ε * g i j + ε * g j i`, where
`g i j = λ ^ (j - (i + 1))` for `i < j` and `0` otherwise. -/
private theorem ite_expect_walkDart_mem_unsatEdges_mul_le (σ : V → α) (i j : Fin T) :
    (if i = j then 0 else 𝔼 p : V × (Fin T → D) × (Fin T → Fin q),
      (if R.graph.walkDart (p.1, p.2.1) i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0 : ℝ) *
        if R.graph.walkDart (p.1, p.2.1) j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) ≤
      R.toConstraintGraph.unsatFrac σ ^ 2 +
        R.toConstraintGraph.unsatFrac σ *
          (if i < j then R.graph.spectralExpansion ^ (j - (i + 1) : ℕ) else 0) +
        R.toConstraintGraph.unsatFrac σ *
          (if j < i then R.graph.spectralExpansion ^ (i - (j + 1) : ℕ) else 0) := by
  have hε : 0 ≤ R.toConstraintGraph.unsatFrac σ := R.toConstraintGraph.unsatFrac_nonneg σ
  have hlam₀ : 0 ≤ R.graph.spectralExpansion := R.graph.spectralExpansion_nonneg
  have hg (a b : Fin T) :
      0 ≤ if a < b then R.graph.spectralExpansion ^ (b - (a + 1) : ℕ) else 0 := by positivity
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [ite_eq_right hij.ne, Fintype.expect_comp_fst_snd_fst (γ := Fin T → Fin q)
      (fun w ↦ (if R.graph.walkDart w i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) *
        (if R.graph.walkDart w j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0)),
      ite_eq_left hij]
    linarith [R.expect_mem_unsatEdges_mul_le T σ hij, mul_nonneg hε (hg j i)]
  · rw [ite_eq_left rfl]
    have := mul_nonneg hε (hg i i)
    positivity
  · rw [ite_eq_right hij.ne', show (𝔼 p : V × (Fin T → D) × (Fin T → Fin q),
        (if R.graph.walkDart (p.1, p.2.1) i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0 : ℝ) *
          if R.graph.walkDart (p.1, p.2.1) j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) =
        𝔼 p : V × (Fin T → D) × (Fin T → Fin q),
        (if R.graph.walkDart (p.1, p.2.1) j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0 : ℝ) *
          if R.graph.walkDart (p.1, p.2.1) i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0 from
        expect_congr rfl fun p _ ↦ mul_comm _ _,
      Fintype.expect_comp_fst_snd_fst (γ := Fin T → Fin q)
      (fun w ↦ (if R.graph.walkDart w j ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0) *
        (if R.graph.walkDart w i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0)),
      ite_eq_left hij]
    linarith [R.expect_mem_unsatEdges_mul_le T σ hij, mul_nonneg hε (hg i j)]

open Classical in
/-- **The second moment** [Dinur, Lemma 5.2][Dinur2005]: on an expander, the number of hits of a
uniformly random killed walk has second moment at most its first moment plus
`T ^ 2 ε ^ 2 + 2 T ε / (1 - λ)`, where `ε` is the proportion of the darts violated by `σ` and
`λ < 1` the spectral expansion. A hit is a step crossing a violated dart, and two steps `i < j` of
a random walk both cross violated darts with probability at most `ε ^ 2 + λ ^ (j - (i + 1)) ε`
(`expect_mem_unsatEdges_mul_le`); the errors sum to a geometric series at every step. -/
theorem expect_numHits_sq_le (A : V → WalkLabels D T → α) (σ : V → α)
    (hlam : R.graph.spectralExpansion < 1) :
    𝔼 p, (R.numHits T q A σ p : ℝ) ^ 2 ≤
      𝔼 p, (R.numHits T q A σ p : ℝ) + T ^ 2 * R.toConstraintGraph.unsatFrac σ ^ 2 +
        2 * T * R.toConstraintGraph.unsatFrac σ / (1 - R.graph.spectralExpansion) := by
  set ε := R.toConstraintGraph.unsatFrac σ
  set lam := R.graph.spectralExpansion
  set c : Fin T → V × (Fin T → D) × (Fin T → Fin q) → ℝ := fun i p ↦
    if R.graph.walkDart (p.1, p.2.1) i ∈ R.toConstraintGraph.unsatEdges σ then 1 else 0
  set g : Fin T → Fin T → ℝ := fun i j ↦ if i < j then lam ^ (j - (i + 1) : ℕ) else 0
  have hε : 0 ≤ ε := R.toConstraintGraph.unsatFrac_nonneg σ
  have hlam₀ : 0 ≤ lam := R.graph.spectralExpansion_nonneg
  -- the errors sum to a geometric series at every step
  have hgsum : ∑ i, ∑ j, g i j ≤ T * (1 / (1 - lam)) := by
    calc ∑ i, ∑ j, g i j ≤ ∑ _i : Fin T, 1 / (1 - lam) := by
          refine sum_le_sum fun i _ ↦ ?_
          simpa [g] using (Fin.sum_univ_eq_sum_range
            (fun j ↦ if (i : ℕ) < j then lam ^ (j - (i + 1)) else 0) T).le.trans
            (sum_ite_lt_pow_le hlam₀ hlam T i)
      _ = T * (1 / (1 - lam)) := by simp
  calc 𝔼 p, (R.numHits T q A σ p : ℝ) ^ 2
      ≤ 𝔼 p, ((R.numHits T q A σ p : ℝ) + ∑ i, ∑ j, if i = j then 0 else c i p * c j p) :=
        expect_le_expect fun p _ ↦ numHits_sq_le_add_sum R T q A σ p
    _ = 𝔼 p, (R.numHits T q A σ p : ℝ) +
          ∑ i, ∑ j, if i = j then 0 else 𝔼 p, c i p * c j p := by
        rw [expect_add_distrib, expect_sum_comm]
        simp only [expect_sum_comm]
        congr 1
        refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
        split_ifs <;> simp
    _ ≤ 𝔼 p, (R.numHits T q A σ p : ℝ) +
          ∑ i : Fin T, ∑ j : Fin T, (ε ^ 2 + ε * g i j + ε * g j i) := by
        gcongr with i _ j _
        exact ite_expect_walkDart_mem_unsatEdges_mul_le R T q σ i j
    _ ≤ 𝔼 p, (R.numHits T q A σ p : ℝ) + T ^ 2 * ε ^ 2 + 2 * T * ε / (1 - lam) := by
        have hsum : ∑ i : Fin T, ∑ j : Fin T, (ε ^ 2 + ε * g i j + ε * g j i) =
            T ^ 2 * ε ^ 2 + ε * ∑ i, ∑ j, g i j + ε * ∑ i, ∑ j, g i j := by
          simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          rw [sum_comm (f := fun i j ↦ g j i)]
          ring
        rw [hsum, show 2 * (T : ℝ) * ε / (1 - lam) = 2 * (ε * (T * (1 / (1 - lam)))) by ring]
        linarith [mul_le_mul_of_nonneg_left hgsum hε]

open Classical in
/-- A killed walk hit at some step is violated: the proportion of the killed walks hit at some step
is at most the proportion of the darts of the powered constraint graph violated by `A`. -/
private theorem expect_numHits_ne_zero_le (A : V → WalkLabels D T → α) (σ : V → α) :
    𝔼 p, (if (R.numHits T q A σ p : ℝ) = 0 then 0 else 1) ≤
      (R.power T q).toConstraintGraph.unsatFrac A := by
  rw [← ConstraintGraph.expect_mem_unsatEdges]
  refine expect_le_expect fun p _ ↦ ?_
  by_cases h : (R.numHits T q A σ p : ℝ) = 0
  · rw [ite_eq_left h]
    split_ifs <;> norm_num
  · obtain ⟨i, hi⟩ : ({i ∈ range T | R.Hit T q A σ p i} : Finset ℕ).Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro h'
      exact h (by simp [numHits, h'])
    rw [ite_eq_right h, ite_eq_left (ConstraintGraph.mem_unsatEdges.2
      (R.not_satisfies_of_hit (mem_filter.1 hi).2))]

end SecondMoment

/-! ### The powering bound -/

section Bound

variable [Fintype V] [Fintype D] [Fintype α] [Nonempty α]

/-- **The powering bound** [Dinur, Section 5][Dinur2005], for a labelling: on a constraint graph
whose spectral expansion is `λ < 1`, a labelling `A` of the powered constraint graph violates a
proportion at least `c ^ 2 ε / (c + T ^ 2 ε + 2 T / (1 - λ))` of its darts, where `ε` is the
proportion of the darts violated by its plurality decoding, for `2 H + 1 < T` and any
`0 ≤ c ≤ (q - 1) (1 / |α| - (1 - 1 / q) ^ (H + 1)) ^ 2`.

By the second moment method, the number `N` of hits of a uniformly random killed walk, which is
nonzero only on violated killed walks, is nonzero with probability at least `(𝔼 N) ^ 2 / 𝔼 N ^ 2`,
where `𝔼 N ≥ c ε` (`le_expect_numHits`) and `𝔼 N ^ 2 ≤ 𝔼 N + T ^ 2 ε ^ 2 + 2 T ε / (1 - λ)`
(`expect_numHits_sq_le`). -/
theorem le_unsatFrac_power [Nonempty D] (A : V → WalkLabels D T → α) {H : ℕ} (hH : 2 * H + 1 < T)
    (hα : (1 - (q : ℝ)⁻¹) ^ (H + 1) ≤ (Fintype.card α : ℝ)⁻¹) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : c ≤ ((q : ℝ) - 1) * ((Fintype.card α : ℝ)⁻¹ - (1 - (q : ℝ)⁻¹) ^ (H + 1)) ^ 2)
    (hlam : R.graph.spectralExpansion < 1) :
    c ^ 2 * R.toConstraintGraph.unsatFrac (R.decode T q A) /
        (c + T ^ 2 * R.toConstraintGraph.unsatFrac (R.decode T q A) +
          2 * T / (1 - R.graph.spectralExpansion)) ≤
      (R.power T q).toConstraintGraph.unsatFrac A := by
  set ε := R.toConstraintGraph.unsatFrac (R.decode T q A)
  set lam := R.graph.spectralExpansion
  set N := fun p ↦ (R.numHits T q A (R.decode T q A) p : ℝ)
  set x := (R.power T q).toConstraintGraph.unsatFrac A
  have hε : 0 ≤ ε := R.toConstraintGraph.unsatFrac_nonneg _
  have hx : 0 ≤ x := (R.power T q).toConstraintGraph.unsatFrac_nonneg _
  have hlam' : 0 < 1 - lam := sub_pos.2 hlam
  -- the first moment
  have h₁ : c * ε ≤ 𝔼 p, N p :=
    (mul_le_mul_of_nonneg_right hc hε).trans (R.le_expect_numHits T q A hH hα)
  -- the second moment
  have h₂ := R.expect_numHits_sq_le T q A (R.decode T q A) hlam
  -- the second moment method
  have h₃ : (𝔼 p, N p) ^ 2 ≤ x * (𝔼 p, N p + (T ^ 2 * ε ^ 2 + 2 * T * ε / (1 - lam))) := by
    refine (Fintype.sq_expect_le_dens_mul_expect_sq N).trans (mul_le_mul ?_
      (h₂.trans_eq (add_assoc _ _ _)) (expect_nonneg fun p _ ↦ sq_nonneg _) hx)
    rw [← Fintype.expect_boole]
    exact le_of_eq_of_le (expect_congr rfl fun p _ ↦ ite_not _ _ _)
      (R.expect_numHits_ne_zero_le T q A (R.decode T q A))
  have h₄ := sq_le_mul_add_of_le (mul_nonneg hc₀ hε) h₁ (by positivity) hx h₃
  rcases hε.eq_or_lt with h₀ | h₀
  · rw [← h₀]
    simpa using hx
  have hT : (0 : ℝ) < T := Nat.cast_pos.2 (by omega)
  have h₅ : ε * (c ^ 2 * ε) ≤ ε * (x * (c + T ^ 2 * ε + 2 * T / (1 - lam))) :=
    calc ε * (c ^ 2 * ε) = (c * ε) ^ 2 := by ring
      _ ≤ x * (c * ε + (T ^ 2 * ε ^ 2 + 2 * T * ε / (1 - lam))) := h₄
      _ = ε * (x * (c + T ^ 2 * ε + 2 * T / (1 - lam))) := by ring
  rw [div_le_iff₀ (by positivity)]
  exact le_of_mul_le_mul_left h₅ h₀

/-- **The powering bound** [Dinur, Section 5][Dinur2005], with a supplied nonnegative threshold
`δ`. Retaining its contribution to the denominator permits a larger final amplification gap. -/
theorem le_unsatVal_power_of_le (H : ℕ) (hH : 2 * H + 1 < T)
    (hα : (1 - (q : ℝ)⁻¹) ^ (H + 1) ≤ (Fintype.card α : ℝ)⁻¹) {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : c ≤ ((q : ℝ) - 1) * ((Fintype.card α : ℝ)⁻¹ - (1 - (q : ℝ)⁻¹) ^ (H + 1)) ^ 2) {μ : ℝ}
    (hμ : R.graph.spectralExpansion ≤ μ) (hμ₁ : μ < 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    c ^ 2 / (c + T ^ 2 * δ + 2 * T / (1 - μ)) * min R.toConstraintGraph.unsatVal δ ≤
      (R.power T q).toConstraintGraph.unsatVal := by
  have hlam : R.graph.spectralExpansion < 1 := hμ.trans_lt hμ₁
  have hB : 0 ≤ 2 * (T : ℝ) / (1 - R.graph.spectralExpansion) :=
    div_nonneg (by positivity) (sub_pos.2 hlam).le
  have hBB : 2 * (T : ℝ) / (1 - R.graph.spectralExpansion) ≤ 2 * T / (1 - μ) :=
    div_le_div_of_nonneg_left (by positivity) (sub_pos.2 hμ₁) (by linarith)
  rcases isEmpty_or_nonempty D with hD | hD
  · -- without labels, `R` has no darts and its value is zero
    have h₀ : R.toConstraintGraph.unsatVal = 0 := by
      refine le_antisymm ?_ R.toConstraintGraph.unsatVal_nonneg
      refine (R.toConstraintGraph.unsatVal_le fun _ ↦ Classical.arbitrary α).trans_eq ?_
      simp [ConstraintGraph.unsatFrac]
    rw [h₀, min_eq_left (by positivity), mul_zero]
    exact (R.power T q).toConstraintGraph.unsatVal_nonneg
  refine ((R.power T q).toConstraintGraph.le_unsatVal_iff).2 fun A ↦ ?_
  exact (mul_min_le_div hc₀ hB hBB R.toConstraintGraph.unsatVal_nonneg
    (R.toConstraintGraph.unsatVal_le _) hδ).trans (R.le_unsatFrac_power T q A hH hα hc₀ hc hlam)

/-- The standard killed-walk cutoff supplies first-moment coefficient `(q - 1) / (4 |α|²)`.
The soundness threshold remains a parameter, independently of the walk length. -/
theorem le_unsatVal_power_min (hq : 2 ≤ q) (hT : T = 4 * Fintype.card α * (q - 1)) {μ : ℝ}
    (hμ : R.graph.spectralExpansion ≤ μ) (hμ₁ : μ < 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    let c : ℝ := (q - 1) / (4 * Fintype.card α ^ 2)
    c ^ 2 / (c + T ^ 2 * δ + 2 * T / (1 - μ)) * min R.toConstraintGraph.unsatVal δ ≤
      (R.power T q).toConstraintGraph.unsatVal := by
  set K := Fintype.card α
  have hK : 1 ≤ K := Fintype.card_pos
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hq' : (1 : ℝ) ≤ q - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  -- the killed walks surviving their first `2 |α| (q - 1)` steps are few
  have hm : 1 ≤ K * (q - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hH : 2 * (2 * K * (q - 1) - 1) + 1 < T := by
    rw [hT, show 4 * K * (q - 1) = 4 * (K * (q - 1)) by ring,
      show 2 * K * (q - 1) = 2 * (K * (q - 1)) by ring]
    omega
  have hsurv : (1 - (q : ℝ)⁻¹) ^ (2 * K * (q - 1) - 1 + 1) ≤ (2 * K : ℝ)⁻¹ := by
    rw [Nat.sub_add_cancel (by rw [show 2 * K * (q - 1) = 2 * (K * (q - 1)) by ring]; omega)]
    exact one_sub_inv_pow_le hq hK
  have h2K : (2 * K : ℝ)⁻¹ ≤ (K : ℝ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  set c : ℝ := (q - 1) / (4 * K ^ 2)
  have hc₀ : 0 ≤ c := by positivity
  have hc : c ≤ ((q : ℝ) - 1) * ((K : ℝ)⁻¹ - (1 - (q : ℝ)⁻¹) ^ (2 * K * (q - 1) - 1 + 1)) ^ 2 := by
    have h : (2 * K : ℝ)⁻¹ ≤ (K : ℝ)⁻¹ - (1 - (q : ℝ)⁻¹) ^ (2 * K * (q - 1) - 1 + 1) := by
      have : (K : ℝ)⁻¹ = 2 * (2 * K : ℝ)⁻¹ := by field_simp
      linarith
    calc c = (q - 1) * ((2 * K : ℝ)⁻¹) ^ 2 := by simp only [c]; field_simp; ring
      _ ≤ _ := by gcongr
  exact R.le_unsatVal_power_of_le T q _ hH (hsurv.trans h2K) hc₀ hc hμ hμ₁ hδ

/-- **The powering bound** [Dinur, Section 5][Dinur2005]: the standard cutoff gains a factor
linear in `q`, up to threshold `1 / T²`. The more precise `le_unsatVal_power_min` permits larger
thresholds without repeating the probabilistic argument. -/
theorem le_unsatVal_power (hq : 2 ≤ q) (hT : T = 4 * Fintype.card α * (q - 1)) {μ : ℝ}
    (hμ : R.graph.spectralExpansion ≤ μ) (hμ₁ : μ < 1) :
    ((q : ℝ) - 1) / (4 * Fintype.card α ^ 2 + 16 * Fintype.card α ^ 4 +
        128 * Fintype.card α ^ 5 / (1 - μ)) * min R.toConstraintGraph.unsatVal (1 / T ^ 2) ≤
      (R.power T q).toConstraintGraph.unsatVal := by
  set K := Fintype.card α
  have hK : 1 ≤ K := Fintype.card_pos
  have hq' : (1 : ℝ) ≤ q - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hμ' : 0 < 1 - μ := sub_pos.2 hμ₁
  have hT₀ : 0 < T := by rw [hT]; exact Nat.mul_pos (by lia) (by lia)
  have hcancel : (T : ℝ) ^ 2 * (1 / (T : ℝ) ^ 2) = 1 := by
    have : (T : ℝ) ≠ 0 := by exact_mod_cast hT₀.ne'
    field_simp
  have hpow := R.le_unsatVal_power_min T q hq hT hμ hμ₁ (δ := 1 / T ^ 2) (by positivity)
  dsimp only at hpow
  rw [hcancel] at hpow
  set c : ℝ := (q - 1) / (4 * K ^ 2)
  refine le_trans ?_ hpow
  gcongr ?_ * _
  · exact le_min R.toConstraintGraph.unsatVal_nonneg (by positivity)
  -- the factor `c ^ 2 / (c + 1 + 2 T / (1 - μ))` grows linearly with `q`
  have hTc : (T : ℝ) = 4 * K * (q - 1) := by
    rw [hT]
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  rw [hTc, div_le_div_iff₀ (by positivity) (by positivity)]
  have e : c ^ 2 * (4 * K ^ 2 + 16 * K ^ 4 + 128 * K ^ 5 / (1 - μ)) =
      c * (q - 1) + (q - 1) ^ 2 + (q - 1) * (2 * (4 * K * (q - 1)) / (1 - μ)) := by
    simp only [c]
    field_simp
    ring
  rw [e]
  have : 0 ≤ (q - 1 : ℝ) * (2 * (4 * K * (q - 1)) / (1 - μ)) := by positivity
  nlinarith

end Bound

end RegularConstraintGraph

end PCP

end Cslib
