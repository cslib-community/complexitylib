/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Perturbation
public import Complexity.Foundations.Analysis.RowCompression.Preloss
public import Complexity.Foundations.Analysis.RowCompression.SentinelIteration
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deriving sentinel comparison bounds from clipped prefix errors

Suppose fewer than `K` true first entries exceed `L₀`, and the actual raw prefixes have small
clipped errors. Replace first entries above `16 * (L₀ + 1)` by that common sentinel and clear
only their later first increments. The modified calculation has bounded actual input ranks and
thresholds, and the original marked entries remain in the compression identity region.

The ceilings and the total-variation hypothesis of
`Cslib.RowCompression.iterate_sentinelState_of_sum_abs_lt` are derived here, rather than assumed.
The comparison reference has the true row plus the same small initial loss and no increments.
The finite error budget is the exact `28`-weighted sum supplied by absolute update stability.
No upper bound on the largest true entry, original compressed input, or final output error is
assumed.

For a first-overflow application, start the local calculation from the already-added input of
that group, use a zero first local increment, and then use the subsequent actual increments.
Both the initial and first local prefix errors then concern the overflow group's raw input.
This does not require an error estimate for the preceding global prefix.

This supplies the small-heavy-set sentinel comparison in the proof of
[OpenAI2026LogSpace, Section 8.3, Lemma 8.3]. Upper saturation and the row-output comparison,
the case of at least `K` large true entries, and the full relative-stability estimate remain
separate. Sentinels are analytical devices, not objects stored by the compression algorithm.

## Main results

* `Cslib.RowCompression.abs_sub_le_of_clippedError_le`: small clipped errors give the actual
  relative first-channel and absolute second-channel bounds.
* `Cslib.RowCompression.iterate_sentinelState_of_clippedError_le`: actual sentinel coupling
  from clipped prefix budgets and a strict true-heavy-count bound.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.3, proof of Lemma 8.3, the branch with fewer than `K` entries above `L₀`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.RowCompression

open Finset

/-- Below one, clipping discards no information. The first target may be arbitrarily large. -/
theorem abs_sub_le_of_clippedError_le {d v ε : ℝ} {w : Fin 2 → ℝ}
    (hd : 0 ≤ d) (hε : ε < 1) (he : clippedError d v w ≤ ε) :
    |w 0 - d| ≤ (1 + d) * ε ∧ |w 1 - v| ≤ ε := by
  have hfirst : |w 0 - d| / (1 + d) ≤ ε :=
    (min_le_iff.mp ((le_max_left _ _).trans he)).resolve_left (not_le.mpr hε)
  have hsecond : |w 1 - v| ≤ ε :=
    (min_le_iff.mp ((le_max_right _ _).trans he)).resolve_left (not_le.mpr hε)
  refine ⟨?_, hsecond⟩
  simpa only [mul_comm] using (div_le_iff₀ (by linarith : 0 < 1 + d)).mp hfirst

private def budget (ε : ℕ → ℝ) (m : ℕ) : ℝ :=
  28 ^ m * ε 0 + ∑ i ∈ range m, 28 ^ (m - i) * (ε i + ε (i + 1))

private theorem budget_nonneg {ε : ℕ → ℝ} {m : ℕ} (hε : ∀ i ≤ m, 0 ≤ ε i) :
    0 ≤ budget ε m := by
  apply add_nonneg (mul_nonneg (by positivity) (hε 0 (Nat.zero_le m)))
  refine sum_nonneg fun i hi => mul_nonneg (by positivity) (add_nonneg ?_ ?_)
  · exact hε i (mem_range.mp hi).le
  · exact hε (i + 1) (mem_range.mp hi)

private theorem budget_mono {ε : ℕ → ℝ} {j m : ℕ}
    (hε : ∀ i ≤ m, 0 ≤ ε i) (hj : j ≤ m) : budget ε j ≤ budget ε m := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj)
      (hε 0 (Nat.zero_le m))
  calc
    _ ≤ ∑ i ∈ range j, (28 : ℝ) ^ (m - i) * (ε i + ε (i + 1)) := by
      refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right hj i)) ?_
      exact add_nonneg (hε i ((mem_range.mp hi).le.trans hj))
        (hε (i + 1) ((mem_range.mp hi).trans_le hj))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono hj) fun i hi _ =>
      mul_nonneg (by positivity)
        (add_nonneg (hε i (mem_range.mp hi).le) (hε (i + 1) (mem_range.mp hi)))

private theorem sum_errors_le_budget {ε : ℕ → ℝ} {m : ℕ}
    (hε : ∀ i ≤ m, 0 ≤ ε i) :
    ε 0 + ∑ i ∈ range m, (ε i + ε (i + 1)) ≤ budget ε m := by
  apply add_le_add
  · exact le_mul_of_one_le_left (hε 0 (Nat.zero_le m)) (one_le_pow₀ (by norm_num))
  · exact sum_le_sum fun i hi => le_mul_of_one_le_left
      (add_nonneg (hε i (mem_range.mp hi).le) (hε (i + 1) (mem_range.mp hi)))
      (one_le_pow₀ (by norm_num))

private theorem error_le_budget {ε : ℕ → ℝ} {m i : ℕ}
    (hε : ∀ i ≤ m, 0 ≤ ε i) (hi : i ≤ m) : ε i ≤ budget ε m := by
  have hsum := sum_errors_le_budget hε
  have hs0 : 0 ≤ ∑ k ∈ range m, (ε k + ε (k + 1)) :=
    sum_nonneg fun k hk => add_nonneg (hε k (mem_range.mp hk).le)
      (hε (k + 1) (mem_range.mp hk))
  cases i with
  | zero => exact (le_add_of_nonneg_right hs0).trans hsum
  | succ i =>
    have hsingle := single_le_sum (s := range m) (f := fun k => ε k + ε (k + 1))
      (fun k hk => add_nonneg (hε k (mem_range.mp hk).le) (hε (k + 1) (mem_range.mp hk)))
      (mem_range.mpr hi)
    have hi0 := hε i (Nat.le_of_lt hi)
    have h00 := hε 0 (Nat.zero_le m)
    linarith

private theorem input_budget_le {ε : ℕ → ℝ} {m i : ℕ}
    (hε : ∀ k ≤ m, 0 ≤ ε k) (hi : i < m) :
    budget ε i + (ε i + ε (i + 1)) ≤ budget ε m := by
  apply le_trans (b := budget ε (i + 1)) _ (budget_mono hε hi)
  unfold budget
  rw [sum_range_succ]
  simp only [Nat.add_sub_cancel_left, pow_one]
  conv_rhs => rw [← add_assoc]
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.le_succ i)) (hε 0 (Nat.zero_le m))
    · refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le_sub_right (Nat.le_succ i) k)) ?_
      exact add_nonneg (hε k ((mem_range.mp hk).le.trans hi.le))
        (hε (k + 1) ((mem_range.mp hk).trans_le hi.le))
  · exact le_mul_of_one_le_left (add_nonneg (hε i hi.le) (hε (i + 1) hi)) (by norm_num)

variable {ι : Type*}

private theorem sentinel_reference_bounds {s : Finset ι} {K : ℕ} {η L₀ z : ℝ}
    {truth loss : ι → Fin 2 → ℝ} (hη : 0 ≤ η) (hL₀ : η ≤ L₀) (hK : 0 < K) (hz : z ≤ η)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ η / 2)
    (hloss : ∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2)
    (hcount : #{y ∈ s | L₀ < truth y 0} < K) :
    let marked := {y ∈ s | 16 * (L₀ + 1) < truth y 0}
    let b := sentinelState marked (16 * (L₀ + 1)) ⟨z, truth + loss⟩
    (∀ y ∈ s, -η ≤ b.row y 0) ∧ (∀ y ∈ s, |b.row y 1| ≤ η) ∧
      firstRank s K b.defaultValue b.row ≤ 2 * L₀ := by
  classical
  let marked := {y ∈ s | 16 * (L₀ + 1) < truth y 0}
  let b := sentinelState marked (16 * (L₀ + 1)) ⟨z, truth + loss⟩
  change (∀ y ∈ s, -η ≤ b.row y 0) ∧ (∀ y ∈ s, |b.row y 1| ≤ η) ∧
    firstRank s K b.defaultValue b.row ≤ 2 * L₀
  have hL₀0 : 0 ≤ L₀ := hη.trans hL₀
  have hshape : (∀ y ∈ s, -η ≤ b.row y 0) ∧ (∀ y ∈ s, |b.row y 1| ≤ η) := by
    constructor
    · intro y hy
      by_cases hm : y ∈ marked
      · change -η ≤ sentinelFirst marked (16 * (L₀ + 1)) (truth + loss) y 0
        rw [sentinelFirst_zero_of_mem hm]
        linarith
      · change -η ≤ sentinelFirst marked (16 * (L₀ + 1)) (truth + loss) y 0
        rw [sentinelFirst_of_not_mem hm]
        have hl := (abs_le.mp (hloss y hy 0)).1
        change -η ≤ truth y 0 + loss y 0
        linarith [hfirst y hy]
    · intro y hy
      change |sentinelFirst marked (16 * (L₀ + 1)) (truth + loss) y 1| ≤ η
      rw [sentinelFirst_one]
      exact (abs_add_le _ _).trans (by linarith [hsecond y hy, hloss y hy 1])
  refine ⟨hshape.1, hshape.2, max_le (by change z ≤ 2 * L₀; linarith) ?_⟩
  by_contra hq
  have hcard := (lt_kthLargest_iff hK (by positivity : 0 ≤ 2 * L₀)).mp (lt_of_not_ge hq)
  have hsub : ({y ∈ s | 2 * L₀ < b.row y 0} : Finset ι) ⊆
      {y ∈ s | L₀ < truth y 0} := by
    intro y hy
    obtain ⟨hys, hy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hys, ?_⟩
    by_cases hm : y ∈ marked
    · have hlarge := (mem_filter.mp hm).2
      linarith
    · change 2 * L₀ < sentinelFirst marked (16 * (L₀ + 1)) (truth + loss) y 0 at hy
      rw [sentinelFirst_of_not_mem hm] at hy
      have hl := (abs_le.mp (hloss y hys 0)).2
      change 2 * L₀ < truth y 0 + loss y 0 at hy
      linarith
  exact (not_le.mpr hcount) (hcard.trans (card_le_card hsub))

open Classical in
/-- **Sentinel coupling from actual clipped-prefix budgets.** The threshold and variation
conditions of the removal induction follow from the true heavy-count branch and the weighted
prefix budget. `loss` is the common initial preloss; it is not a final-error hypothesis.

Only marked first increments are cleared. Both original marked channels follow their actual
raw prefixes, and all positive-prefix padded ranks agree exactly. -/
theorem iterate_sentinelState_of_clippedError_le {s : Finset ι} {n : ℕ → ℕ} {K : ℕ}
    {ρ : ℕ → ℝ} {η L₀ z : ℝ} {truth raw₀ loss : ι → Fin 2 → ℝ}
    {Δ : ℕ → ι → Fin 2 → ℝ} {ε : ℕ → ℝ} (m : ℕ)
    (hη : 0 ≤ η) (hL₀ : η ≤ L₀) (hzη : z ≤ η) (hK : 0 < K)
    (hKn : ∀ i < m, K ≤ n i) (hρ : ∀ i < m, ρ i ≤ η)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ η / 2)
    (hloss : ∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2)
    (hcount : #{y ∈ s | L₀ < truth y 0} < K)
    (hε : ∀ i ≤ m, 0 ≤ ε i)
    (herr : ∀ i ≤ m, ∀ y ∈ s,
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw₀ i y) ≤ ε i)
    (hsmall : (1 + 16 * (L₀ + 1)) *
      (28 ^ m * ε 0 + ∑ i ∈ range m, 28 ^ (m - i) * (ε i + ε (i + 1))) ≤ 1 / 8) :
    let L := 16 * (L₀ + 1)
    let R := 2 * L₀ + 1
    let marked := {y ∈ s | L < truth y 0}
    let a : State ι := ⟨z, raw₀ + loss⟩
    let original := iterate s n (fun _ => K) ρ Δ a
    let modified := iterate s n (fun _ => K) ρ
      (fun i => sentinelFirst marked 0 (Δ i)) (sentinelState marked L a)
    ∀ j ≤ m, modified j = sentinelState marked L (original j) ∧
      (∀ y ∈ marked, (original j).row y = uncompressedRow Δ a.row j y) ∧
      (0 < j → firstRank s K (original j).defaultValue (original j).row =
        firstRank s K (modified j).defaultValue (modified j).row ∧
          firstRank s K (modified j).defaultValue (modified j).row ≤ R) := by
  classical
  let L := 16 * (L₀ + 1)
  let R := 2 * L₀ + 1
  let c := 1 + L
  let marked := {y ∈ s | L < truth y 0}
  let a : State ι := ⟨z, raw₀ + loss⟩
  let b : State ι := ⟨z, truth + loss⟩
  let a' := sentinelState marked L a
  let b' := sentinelState marked L b
  let Δ' := fun i => sentinelFirst marked 0 (Δ i)
  let A := iterate s n (fun _ => K) ρ Δ' a'
  let B := iterate s n (fun _ => K) ρ (fun _ => 0) b'
  have hL₀0 : 0 ≤ L₀ := hη.trans hL₀
  have hc1 : 1 ≤ c := by dsimp only [c, L]; linarith
  have hc0 : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hc1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hL : 3 * R < L := by dsimp only [R, L]; linarith
  have hmarked : marked ⊆ s := filter_subset _ _
  have hsmall' : c * budget ε m ≤ 1 / 8 := hsmall
  have hE : budget ε m ≤ 1 / 8 :=
    (le_mul_of_one_le_left (budget_nonneg hε) hc1).trans hsmall'
  have hεlt (i : ℕ) (hi : i ≤ m) : ε i < 1 := by
    have h := (error_le_budget hε hi).trans hE
    linarith
  have hraw (i : ℕ) (hi : i ≤ m) (y : ι) (hy : y ∈ s) :
      |uncompressedRow Δ raw₀ i y 0 - truth y 0| ≤ (1 + truth y 0) * ε i ∧
        |uncompressedRow Δ raw₀ i y 1 - truth y 1| ≤ ε i :=
    abs_sub_le_of_clippedError_le (hfirst y hy) (hεlt i hi) (herr i hi y hy)
  have hincr (i : ℕ) (hi : i < m) (y : ι) (hy : y ∈ s) :
      |Δ i y 0| ≤ (1 + truth y 0) * (ε i + ε (i + 1)) ∧
        |Δ i y 1| ≤ ε i + ε (i + 1) := by
    have hbefore := hraw i hi.le y hy
    have hafter := hraw (i + 1) hi y hy
    have heq (ν : Fin 2) : Δ i y ν =
        (uncompressedRow Δ raw₀ (i + 1) y ν - truth y ν) -
          (uncompressedRow Δ raw₀ i y ν - truth y ν) := by
      rw [uncompressedRow_succ]
      ring
    constructor
    · rw [heq 0]
      exact (abs_sub _ _).trans (by linarith [hbefore.1, hafter.1])
    · rw [heq 1]
      exact (abs_sub _ _).trans (by linarith [hbefore.2, hafter.2])
  have hoff (y : ι) (hy : y ∈ s) (hm : y ∉ marked) : truth y 0 ≤ L := by
    exact not_lt.mp fun h => hm (mem_filter.mpr ⟨hy, h⟩)
  have hinit (y : ι) (hy : y ∈ s) (ν : Fin 2) : |a'.row y ν - b'.row y ν| ≤ c * ε 0 := by
    have hr := hraw 0 (Nat.zero_le m) y hy
    simp only [uncompressedRow_zero] at hr
    fin_cases ν
    · by_cases hm : y ∈ marked
      · change |sentinelFirst marked L a.row y 0 - sentinelFirst marked L b.row y 0| ≤ _
        rw [sentinelFirst_zero_of_mem hm, sentinelFirst_zero_of_mem hm, sub_self, abs_zero]
        exact mul_nonneg hc0 (hε 0 (Nat.zero_le m))
      · change |sentinelFirst marked L a.row y 0 - sentinelFirst marked L b.row y 0| ≤ _
        rw [sentinelFirst_of_not_mem hm, sentinelFirst_of_not_mem hm]
        change |raw₀ y 0 + loss y 0 - (truth y 0 + loss y 0)| ≤ _
        rw [add_sub_add_right_eq_sub]
        exact hr.1.trans (mul_le_mul_of_nonneg_right (by dsimp only [c]; linarith [hoff y hy hm])
          (hε 0 (Nat.zero_le m)))
    · change |sentinelFirst marked L a.row y 1 - sentinelFirst marked L b.row y 1| ≤ _
      rw [sentinelFirst_one, sentinelFirst_one]
      change |raw₀ y 1 + loss y 1 - (truth y 1 + loss y 1)| ≤ _
      rw [add_sub_add_right_eq_sub]
      exact hr.2.trans (le_mul_of_one_le_left (hε 0 (Nat.zero_le m)) hc1)
  have hΔ' (i : ℕ) (hi : i < m) (y : ι) (hy : y ∈ s) (ν : Fin 2) :
      |Δ' i y ν - (0 : ι → Fin 2 → ℝ) y ν| ≤ c * (ε i + ε (i + 1)) := by
    have hsum0 := add_nonneg (hε i hi.le) (hε (i + 1) hi)
    simp only [Pi.zero_apply, sub_zero]
    fin_cases ν
    · by_cases hm : y ∈ marked
      · change |sentinelFirst marked 0 (Δ i) y 0| ≤ _
        rw [sentinelFirst_zero_of_mem hm, abs_zero]
        exact mul_nonneg hc0 hsum0
      · change |sentinelFirst marked 0 (Δ i) y 0| ≤ _
        rw [sentinelFirst_of_not_mem hm]
        exact (hincr i hi y hy).1.trans (mul_le_mul_of_nonneg_right
          (by dsimp only [c]; linarith [hoff y hy hm]) hsum0)
    · change |sentinelFirst marked 0 (Δ i) y 1| ≤ _
      rw [sentinelFirst_one]
      exact (hincr i hi y hy).2.trans (le_mul_of_one_le_left hsum0 hc1)
  have hreference := sentinel_reference_bounds hη hL₀ hK hzη hfirst hsecond hloss hcount
  change (∀ y ∈ s, -η ≤ b'.row y 0) ∧ (∀ y ∈ s, |b'.row y 1| ≤ η) ∧
    firstRank s K b'.defaultValue b'.row ≤ 2 * L₀ at hreference
  have hstates (i : ℕ) (hi : i ≤ m) :
      |(A i).defaultValue - (B i).defaultValue| ≤ c * budget ε i ∧
        ∀ y ∈ s, ∀ ν, |(A i).row y ν - (B i).row y ν| ≤ c * budget ε i := by
    have hz' : |a'.defaultValue - b'.defaultValue| ≤ c * ε 0 := by
      change |z - z| ≤ _
      simpa only [sub_self, abs_zero] using mul_nonneg hc0 (hε 0 (Nat.zero_le m))
    have hs := iterate_stability_of_increment_error (ρ := ρ)
      (mul_nonneg hc0 (hε 0 (Nat.zero_le m))) hz' hinit i
      (fun k hk => hK.trans_le (hKn k (hk.trans_le hi))) (fun _ _ => hK)
      (fun k hk => mul_nonneg hc0
        (add_nonneg (hε k (hk.le.trans hi)) (hε (k + 1) (hk.trans_le hi))))
      (fun k hk => hΔ' k (hk.trans_le hi))
    have heq : (28 : ℝ) ^ i * (c * ε 0) +
        ∑ k ∈ range i, 28 ^ (i - k) * (c * (ε k + ε (k + 1))) = c * budget ε i := by
      simp only [budget, mul_add, mul_sum]
      congr 1
      · ring
      · apply sum_congr rfl
        intro k _
        ring
    rw [heq] at hs
    exact hs
  have hceil (i : ℕ) (hi : i < m) :
      firstRank s K (A i).defaultValue (inputRow s n (fun _ => K) ρ Δ' a' i) ≤ R ∧
        stepThreshold s n (fun _ => K) ρ Δ' a' i ≤ R := by
    let D := c * (budget ε i + (ε i + ε (i + 1)))
    have hD0 : 0 ≤ D := mul_nonneg hc0 (add_nonneg
      (budget_nonneg fun k hk => hε k (hk.trans hi.le))
      (add_nonneg (hε i hi.le) (hε (i + 1) hi)))
    have hD : D ≤ 1 / 8 :=
      (mul_le_mul_of_nonneg_left (input_budget_le hε hi) hc0).trans hsmall'
    have hs := hstates i hi.le
    have hzD : |(A i).defaultValue - (B i).defaultValue| ≤ D :=
      hs.1.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
        (add_nonneg (hε i hi.le) (hε (i + 1) hi))) hc0)
    have hwD (y : ι) (hy : y ∈ s) (ν : Fin 2) :
        |inputRow s n (fun _ => K) ρ Δ' a' i y ν - (B i).row y ν| ≤ D := by
      have hd := hΔ' i hi y hy ν
      simp only [Pi.zero_apply, sub_zero] at hd
      change |(A i).row y ν + Δ' i y ν - (B i).row y ν| ≤ _
      calc
        _ = |((A i).row y ν - (B i).row y ν) + Δ' i y ν| := by congr 1; ring
        _ ≤ |(A i).row y ν - (B i).row y ν| + |Δ' i y ν| := abs_add_le _ _
        _ ≤ c * budget ε i + c * (ε i + ε (i + 1)) := add_le_add (hs.2 y hy ν) hd
        _ = D := by dsimp only [D]; ring
    have hqref : firstRank s K (B i).defaultValue (B i).row ≤ 2 * L₀ :=
      reference_iterate_firstRank_le hη (by linarith) hK hreference.1 hreference.2.1
        hreference.2.2 i (fun k hk => hKn k (hk.trans hi)) (fun k hk => hρ k (hk.trans hi))
    have huref : threshold s (n i) (ρ i) (B i).defaultValue (B i).row ≤ 2 * L₀ := by
      have h := reference_stepThreshold_le hη (by linarith) hK hreference.1 hreference.2.1
        hreference.2.2 i (fun k hk => hKn k (hk.trans_lt hi))
        (fun k hk => hρ k (hk.trans_lt hi))
      simpa only [stepThreshold, inputRow, add_zero] using h
    have hqdiff : |firstRank s K (A i).defaultValue
        (inputRow s n (fun _ => K) ρ Δ' a' i) -
          firstRank s K (B i).defaultValue (B i).row| ≤ D :=
      (abs_max_sub_max_le_max _ _ _ _).trans
        (max_le hzD (abs_kthLargest_sub_kthLargest_le hK hD0 (fun y hy => hwD y hy 0)))
    have hudiff := abs_threshold_sub_threshold_le (ρ := ρ i) (hK.trans_le (hKn i hi))
      hD0 hzD hwD
    constructor
    · have h := (le_abs_self _).trans hqdiff
      change firstRank s K (A i).defaultValue (inputRow s n (fun _ => K) ρ Δ' a' i) -
        firstRank s K (B i).defaultValue (B i).row ≤ D at h
      dsimp only [R]
      linarith
    · have h := (le_abs_self _).trans hudiff
      change threshold s (n i) (ρ i) (A i).defaultValue
        (inputRow s n (fun _ => K) ρ Δ' a' i) -
          threshold s (n i) (ρ i) (B i).defaultValue (B i).row ≤ D at h
      change threshold s (n i) (ρ i) (A i).defaultValue
        (inputRow s n (fun _ => K) ρ Δ' a' i) ≤ R
      dsimp only [R]
      linarith
  have hvar (y : ι) (hy : y ∈ marked) :
      3 * R + ∑ i ∈ range m, |Δ i y 0| < a.row y 0 := by
    have hys := hmarked hy
    have hd := (mem_filter.mp hy).2
    have hraw₀ := (hraw 0 (Nat.zero_le m) y hys).1
    simp only [uncompressedRow_zero] at hraw₀
    have hlo := (abs_le.mp hraw₀).1
    have hlosslo := (abs_le.mp (hloss y hys 0)).1
    have hs : ∑ i ∈ range m, |Δ i y 0| ≤
        (1 + truth y 0) * ∑ i ∈ range m, (ε i + ε (i + 1)) := by
      rw [mul_sum]
      exact sum_le_sum fun i hi => (hincr i (mem_range.mp hi) y hys).1
    have he : (1 + truth y 0) * (ε 0 + ∑ i ∈ range m, (ε i + ε (i + 1))) ≤
        (1 + truth y 0) / 8 := by
      have h := mul_le_mul_of_nonneg_left ((sum_errors_le_budget hε).trans hE)
        (by linarith [hfirst y hys] : 0 ≤ 1 + truth y 0)
      linarith
    change 3 * R + ∑ i ∈ range m, |Δ i y 0| < raw₀ y 0 + loss y 0
    dsimp only [L] at hd
    dsimp only [R]
    nlinarith
  exact iterate_sentinelState_of_sum_abs_lt m hmarked hK hKn hR hL hvar
    (fun i hi => (hceil i hi).1) (fun i hi => (hceil i hi).2)

end Cslib.RowCompression
