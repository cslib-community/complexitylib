/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Reduction
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialExpectation
import Mathlib.Algebra.Module.BigOperators

/-!
# Expected cost of the reduction from 3SUM to subset convolution

The expectations of the random cost terms of `threeSumM` in the running-time analysis of
[ChanItakuraMaYu2026], Theorem 2.3, as exact sums over the uniform random choices.

* **Queries** (`sum_length_rankedTargets`): summed over all seeds, the number of queries whose
  target hash has `k` binary digits `1` below `2 ^ d ≤ p` is `|C| (d choose k) (p - 1) p`; that
  is, `E |C*| = |C| (d choose 2 t) / p`.
* **Bad elements** (`mul_sum_length_bad_le`): for duplicate-free `A` with elements below `M`,
  `d ∑_{q ∈ window} |A_bad(q)| ≤ |A| ^ 2 log₂ M`, since every bad element has a partner whose
  difference the prime divides.
* **Total cost for one prime** (`mul_sum_time_threeSumM_le`): summed over the `μ`-tuples of seeds,
  `p ∑ time ≤ #seeds ^ μ (p (3 |A| + 3 |B| + |C| + |A_bad| |B| + |A| |B_bad| + μ G₀) +
  μ G₁ |C| (d choose 2 t))` with `G₀ = 2 |A| + 2 |B| + |C| + 3 (d + 1) Pre` and
  `G₁ = 2 + 3 (d + 1) Q`, where `Pre` and `Q` are the binomial sums of `time_trialM`.

The first and third arguments, and the average over a uniform prime of the window
(`avgTimeOf_le`), live in `TrialExpectation` for any reduction `reduceM` and any target set
(`sum_length_filter_target`, `mul_sum_time_reduceM_le`); the base-`r` reduction of Theorem 3.4
uses them in `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorExpectation`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.sum_length_rankedTargets`
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.mul_sum_time_threeSumM_le`

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- **The expected number of ranked queries**: summed over all seeds, the queries whose target
hash has `k` binary digits `1` below `2 ^ d ≤ p` number `|C| (d choose k) (p - 1) p`. -/
theorem sum_length_rankedTargets {d : ℕ} (hp : 2 ^ d ≤ p) (k : ℕ) (C : List ℕ) :
    ∑ s ∈ seeds p, (C.filter fun c => decide (Ranked d k (s.target c))).length =
      C.length * (d.choose k * ((p - 1) * p)) := by
  simpa only [card_ranked] using sum_length_filter_target (p := p)
    (T := (range (2 ^ d)).filter fun x => Ranked d k x)
    (fun z hz => (mem_range.mp (mem_filter.mp hz).1).trans_le hp)
    (fun z => by simp only [mem_filter, mem_range]; exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩) C

omit [Fact p.Prime] in
/-- The cost of one trial and its reported values, bounded by the work on the ranked queries. -/
private theorem trial_time_add_le {d t s : ℕ} (σ : Seed p) (A B C : List ℕ) (hs : s ≤ 2 * t) :
    let Ag := A.filter fun a => decide (Isolated p A a)
    let Bg := B.filter fun b => decide (Isolated p B b)
    (trialM d t s σ Ag Bg C).time + (C.filter fun c => decide (Accepts d t σ Ag Bg c)).length ≤
      (2 * A.length + 2 * B.length + C.length + 3 * (d + 1) * ∑ j ∈ range (s + 1), d.choose j) +
        (2 + 3 * (d + 1) * ∑ j ∈ Icc s (2 * t), (2 * t).choose j) *
          (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).length := by
  intro Ag Bg
  rw [time_trialM σ Ag Bg C hs]
  have h1 : (starLeft d t σ Ag).length ≤ A.length :=
    (List.length_filter_le _ _).trans (List.length_filter_le _ _)
  have h2 : (starRight d t σ Bg).length ≤ B.length :=
    (List.length_filter_le _ _).trans (List.length_filter_le _ _)
  have h3 : Ag.length ≤ A.length := List.length_filter_le _ _
  have h4 : Bg.length ≤ B.length := List.length_filter_le _ _
  have h5 : (C.filter fun c => decide (Accepts d t σ Ag Bg c)).length ≤
      (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).length := by
    simp only [← List.countP_eq_length_filter]
    exact List.countP_mono_left fun c _ h => by simpa using (of_decide_eq_true h).1
  set n := (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).length
  nlinarith

/-- **The total cost over all seed tuples for one prime** `p ≥ 2 ^ d`: with
`Pre = ∑_{j ≤ s} (d choose j)` and `Q = ∑_{s ≤ j ≤ 2 t} (2 t choose j)`,
`p ∑ time ≤ #seeds ^ μ (p (3 |A| + 3 |B| + |C| + |A_bad| |B| + |A| |B_bad| +
μ (2 |A| + 2 |B| + |C| + 3 (d + 1) Pre)) + μ (2 + 3 (d + 1) Q) |C| (d choose 2 t))`. -/
theorem mul_sum_time_threeSumM_le {d t s μ : ℕ} (hp : 2 ^ d ≤ p) (hs : s ≤ 2 * t)
    (A B C : List ℕ) :
    p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
        (threeSumM d t s p (List.ofFn ss) A B C).time ≤
      #(seeds p) ^ μ * (p * (3 * A.length + 3 * B.length + C.length +
        (A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length +
        μ * (2 * A.length + 2 * B.length + C.length +
          3 * (d + 1) * ∑ j ∈ range (s + 1), d.choose j)) +
        μ * ((2 + 3 * (d + 1) * ∑ j ∈ Icc s (2 * t), (2 * t).choose j) *
          (C.length * d.choose (2 * t)))) :=
  mul_sum_time_reduceM_le (trialSpec_trialM hs) A B C
    (fun σ => trial_time_add_le (d := d) (t := t) σ A B C hs)
    (by rw [sum_length_rankedTargets hp]; ring)

end Cslib.Algorithms.Lean.SubsetConvThreeSum
