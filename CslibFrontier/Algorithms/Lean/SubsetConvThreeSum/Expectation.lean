/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Reduction
import CslibFrontier.Foundations.Data.Nat.LargePrimeDivisors
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
* **Markov** (`card_time_gt_mul_le`): the tuples whose cost exceeds `T` number at most
  `∑ time / T`.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.sum_length_rankedTargets`
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.mul_sum_length_bad_le`
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.mul_sum_time_threeSumM_le`
* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_time_gt_mul_le`

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset

private theorem length_filter_eq_sum {l : List ℕ} (P : ℕ → Prop) [DecidablePred P] :
    (l.filter fun x => decide (P x)).length = (l.map fun x => if P x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : P x <;> simp [h, ih, Nat.add_comm]

private theorem list_sum_comm {α : Type*} (l : List ℕ) (s : Finset α) (f : ℕ → α → ℕ) :
    ∑ a ∈ s, (l.map fun x => f x a).sum = (l.map fun x => ∑ a ∈ s, f x a).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [sum_add_distrib, ih]

variable {p : ℕ} [Fact p.Prime]

/-- **The expected number of ranked queries**: summed over all seeds, the queries whose target
hash has `k` binary digits `1` below `2 ^ d ≤ p` number `|C| (d choose k) (p - 1) p`. -/
theorem sum_length_rankedTargets {d : ℕ} (hp : 2 ^ d ≤ p) (k : ℕ) (C : List ℕ) :
    ∑ s ∈ seeds p, (C.filter fun c => decide (Ranked d k (s.target c))).length =
      C.length * (d.choose k * ((p - 1) * p)) := by
  simp only [length_filter_eq_sum]
  rw [list_sum_comm]
  have hc : ∀ c, ∑ s ∈ seeds p, (if Ranked d k (s.target c) then 1 else 0) =
      d.choose k * ((p - 1) * p) := fun c => by
    rw [← card_filter, card_eq_sum_card_fiberwise (f := fun s : Seed p => s.target c)
      (t := (range (2 ^ d)).filter fun x => Ranked d k x)]
    · rw [← card_ranked d k, ← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun z hz => ?_
      have hz' := (mem_filter.mp hz).2
      rw [filter_filter, ← card_seeds_target c ((hz'.1).trans_le hp)]
      congr 1
      refine filter_congr fun s _ => ?_
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hz', h⟩
    · intro s hs
      exact mem_filter.mpr ⟨mem_range.mpr (mem_filter.mp hs).2.1, (mem_filter.mp hs).2⟩
  simp only [hc, List.map_const', List.sum_replicate, smul_eq_mul]

/-- An element that is not isolated has a partner in its residue class. -/
theorem exists_ne_of_not_isolated {q : ℕ} {A : List ℕ} (hA : A.Nodup) {a : ℕ} (ha : a ∈ A)
    (hbad : ¬ Isolated q A a) : ∃ a' ∈ A, a' ≠ a ∧ (a' : ZMod q) = a := by
  by_contra h
  push Not at h
  apply hbad
  unfold Isolated
  rw [List.countP_congr (q := fun x => decide (x = a)) fun x hx => by
    constructor
    · intro hx'
      have := of_decide_eq_true hx'
      by_contra hne
      exact h x hx (by simpa using hne) this
    · intro hx'
      rw [of_decide_eq_true hx']
      simp]
  exact (List.countP_congr fun x _ => by simp [beq_iff_eq]).trans (List.count_eq_one_of_mem hA ha)

/-- A prime divides the difference of two numbers exactly when they are congruent. -/
theorem natCast_eq_iff_dvd_natAbs {q a a' : ℕ} :
    (a' : ZMod q) = a ↔ q ∣ ((a : ℤ) - a').natAbs := by
  rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs,
    ← ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast; rfl

/-- **Few bad elements on average over the prime window**: for duplicate-free `A` with elements
below `M`, `d ∑_{q ∈ window} |A_bad(q)| ≤ |A| ^ 2 log₂ M`. -/
theorem mul_sum_length_bad_le {A : List ℕ} (hA : A.Nodup) {M d : ℕ} (hM : ∀ a ∈ A, a < M) :
    d * ∑ q ∈ primeWindow d, (A.filter fun a => decide (¬ Isolated q A a)).length ≤
      A.length * A.length * Nat.log 2 M := by
  have hdist : ∀ a ∈ A, ∀ a' ∈ A, a' ≠ a → ((a : ℤ) - a').natAbs ≠ 0 ∧
      ((a : ℤ) - a').natAbs ≤ M := fun a ha a' ha' hne => by
    have h1 := hM a ha; have h2 := hM a' ha'
    constructor <;> omega
  -- each bad element is charged to its partners
  have hq : ∀ q, (A.filter fun a => decide (¬ Isolated q A a)).length ≤
      (A.map fun (a : ℕ) => (A.map fun (a' : ℕ) =>
        if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0).sum).sum := fun q => by
    rw [length_filter_eq_sum]
    refine List.sum_le_sum fun a ha => ?_
    by_cases hbad : Isolated q A a
    · simp [hbad]
    · obtain ⟨a', ha', hne, hcong⟩ := exists_ne_of_not_isolated hA ha hbad
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun (a' : ℕ) =>
        if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0) ha')
      simp only [hne, ne_eq, not_false_eq_true, natCast_eq_iff_dvd_natAbs.mp hcong, and_self,
        ite_true] at this
      simpa [hbad] using this
  calc d * ∑ q ∈ primeWindow d, (A.filter fun a => decide (¬ Isolated q A a)).length
      ≤ d * ∑ q ∈ primeWindow d, (A.map fun (a : ℕ) => (A.map fun (a' : ℕ) =>
          if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0).sum).sum :=
        Nat.mul_le_mul_left _ (sum_le_sum fun q _ => hq q)
    _ = (A.map fun (a : ℕ) => (A.map fun (a' : ℕ) => d * ∑ q ∈ primeWindow d,
          (if a' ≠ a ∧ q ∣ ((a : ℤ) - a').natAbs then 1 else 0)).sum).sum := by
        rw [list_sum_comm, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun a _ => ?_
        rw [list_sum_comm, ← List.sum_map_mul_left]
    _ ≤ (A.map fun _ => (A.map fun _ => Nat.log 2 M).sum).sum := by
        refine List.sum_le_sum fun a ha => List.sum_le_sum fun a' ha' => ?_
        by_cases hne : a' ≠ a
        · obtain ⟨hz, hle⟩ := hdist a ha a' ha' hne
          simp only [ne_eq, hne, not_false_eq_true, true_and]
          rw [← card_filter, mul_comm]
          exact (Nat.card_filter_dvd_mul_le_log (fun q hq => ⟨(mem_primeWindow.mp hq).1,
            (mem_primeWindow.mp hq).2.1⟩) hz).trans (Nat.log_mono_right hle)
        · simp [hne]
    _ = A.length * A.length * Nat.log 2 M := by
        simp only [List.map_const', List.sum_replicate, smul_eq_mul]
        ring

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
          (C.length * d.choose (2 * t)))) := by
  set K₀ := 3 * A.length + 3 * B.length + C.length +
    (A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
    A.length * (B.filter fun b => decide (¬ Isolated p B b)).length
  set G₀ := 2 * A.length + 2 * B.length + C.length + 3 * (d + 1) * ∑ j ∈ range (s + 1), d.choose j
  set G₁ := 2 + 3 * (d + 1) * ∑ j ∈ Icc s (2 * t), (2 * t).choose j
  set c : Seed p → ℕ := fun σ => (C.filter fun c => decide (Ranked d (2 * t) (σ.target c))).length
  -- the cost of one tuple
  have hpt : ∀ ss : Fin μ → Seed p, (threeSumM d t s p (List.ofFn ss) A B C).time ≤
      K₀ + ∑ i, (G₀ + G₁ * c (ss i)) := fun ss => by
    have ht := time_threeSumM (d := d) (t := t) (s := s) (List.ofFn ss) A B C hs
    dsimp only at ht
    rw [ht]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
    have := sum_le_sum fun i (_ : i ∈ univ) => trial_time_add_le (d := d) (t := t) (ss i) A B C hs
    rw [sum_add_distrib] at this
    simp only [K₀, G₀, G₁, c] at this ⊢
    omega
  have hsumc : ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p), ∑ i, G₁ * c (ss i) =
      μ * (G₁ * (#(seeds p) ^ (μ - 1) * ∑ σ ∈ seeds p, c σ)) := by
    rw [sum_comm]
    simp only [Fintype.sum_piFinset_apply, Fintype.card_fin, smul_eq_mul, ← mul_sum, sum_const,
      card_univ]
    ring
  have hc : ∑ σ ∈ seeds p, c σ = C.length * (d.choose (2 * t) * ((p - 1) * p)) :=
    sum_length_rankedTargets hp (2 * t) C
  have hcard : #(seeds p) = (p - 1) * p ^ 2 := card_seeds
  calc p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
        (threeSumM d t s p (List.ofFn ss) A B C).time
      ≤ p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
          (K₀ + ∑ i, G₀ + ∑ i, G₁ * c (ss i)) := by
        refine Nat.mul_le_mul_left _ (sum_le_sum fun ss _ => (hpt ss).trans_eq ?_)
        rw [sum_add_distrib]; ring
    _ = p * (#(seeds p) ^ μ * (K₀ + μ * G₀)) +
          p * (μ * (G₁ * (#(seeds p) ^ (μ - 1) * ∑ σ ∈ seeds p, c σ))) := by
        rw [sum_add_distrib, hsumc, sum_const, Fintype.card_piFinset_const, smul_eq_mul, sum_const,
          card_univ, Fintype.card_fin, smul_eq_mul]
        ring
    _ ≤ _ := by
        rw [hc]
        rcases Nat.eq_zero_or_pos μ with rfl | hμ
        · simp
        · have hpow : #(seeds p) ^ (μ - 1) * #(seeds p) = #(seeds p) ^ μ := by
            rw [← pow_succ]; congr 1; omega
          have : p * (μ * (G₁ * (#(seeds p) ^ (μ - 1) *
              (C.length * (d.choose (2 * t) * ((p - 1) * p)))))) =
              #(seeds p) ^ (μ - 1) * #(seeds p) * (μ * (G₁ * (C.length * d.choose (2 * t)))) := by
            rw [hcard]; ring
          rw [this, hpow]
          nlinarith [Nat.zero_le (#(seeds p) ^ μ)]

/-- **Markov's inequality** for the cost: at most `∑ cost / T` tuples cost more than `T`. -/
theorem card_time_gt_mul_le {α : Type*} (S : Finset α) (f : α → ℕ) (T : ℕ) :
    #(S.filter fun x => T < f x) * T ≤ ∑ x ∈ S, f x := by
  calc #(S.filter fun x => T < f x) * T = ∑ _x ∈ S.filter fun x => T < f x, T := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ x ∈ S.filter fun x => T < f x, f x := sum_le_sum fun x hx => (mem_filter.mp hx).2.le
    _ ≤ ∑ x ∈ S, f x := sum_le_sum_of_subset (filter_subset _ _)

end Cslib.Algorithms.Lean.SubsetConvThreeSum
