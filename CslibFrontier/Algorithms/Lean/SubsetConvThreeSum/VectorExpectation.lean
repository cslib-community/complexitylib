/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.TrialExpectation
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.BalancedCount
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorReduction
import CslibFrontier.Foundations.Combinatorics.CubeCounts

/-!
# Expected cost of the base-`r` reduction

The expected `TimeM` cost of the base-`r` reduction `vthreeSumM` of [ChanItakuraMaYu2026],
Theorem 3.4 ("Running time analysis", p. 13), as exact sums over the uniform random choices, for
given `r`, `d`, `s`, `μ` and window exponent `e`.

* **Balanced queries** (`sum_length_balancedTargets`): summed over all seeds, the queries whose
  target hash is balanced number `|C| #balancedVecs (p - 1) p` for `r ^ d ≤ p`; that is,
  `E |C*| = |C| #balancedVecs / p` (the paper's `E[C*] = Θ̃(r^d / p) |C|`).
* **One trial** (`vtrial_time_add_le`): a trial's ticks plus its reported values are at most
  `G₀ + G₁ |C*|`, with `G₀ = |A| + |B| + |C| + (t + 1) (|A| + |B| + 3 (r d + 1) H)` and
  `G₁ = 2 + (t + 1) 3 (r d + 1) Q`, where `t = balancedSize r d`,
  `H = #{x ∈ [r]^d : |x| ≤ s}` and `Q = ∑_{j ≤ t - s} (t choose j)` bounds the high cells below a
  balanced query (`card_Iic_filter_le_sum_le`). The `t + 1` is the paper's loop over the splits.
* **One prime** (`mul_sum_time_vthreeSumM_le`): summed over the `μ`-tuples of seeds,
  `p ∑ time ≤ #seeds ^ μ (p (3 |A| + 3 |B| + |C| + |A_bad| |B| + |A| |B_bad| + μ G₀) +
  μ G₁ |C| #balancedVecs)`, by the shared `mul_sum_time_reduceM_le`.
* **Expected cost** (`avg_time_vthreeSumM_le`): for duplicate-free `A`, `B` below `M`, `e ≥ 1` and
  `r ^ d ≤ 2 ^ e`, the expected cost `avgTimeOf` over a uniform prime of `[2 ^ e, 2 ^ (e + 1))`
  and `μ` uniform seeds is at most
  `3 |A| + 3 |B| + |C| + μ G₀ + μ G₁ |C| #balancedVecs / 2 ^ e +
  (|A| ^ 2 |B| + |A| |B| ^ 2) log₂ M / (e #window)`, by the shared averaging `avgTimeOf_le`.

This is the paper's `Õ(N n̂² / p₀ + μ (P_vec-conv + N + |C| Q_vec-conv))` before the parameter
choices: the bad-sum term is bounded via `mul_sum_length_bad_le`, and the convolution terms are
the exact table sizes of `VectorConvolution.time_solveM`. The `TimeM` model and its uncharged
operations are those of `vtrialM` and `reduceM`; sampling is uncharged.

## Main results

* `Cslib.Algorithms.Lean.SubsetConvThreeSum.card_balancedNumbers`,
  `sum_length_balancedTargets`, `vtrial_time_add_le`, `mul_sum_time_vthreeSumM_le`,
  `avg_time_vthreeSumM_le`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset

/-- The balanced numbers below `r ^ d` correspond to the balanced vectors. -/
theorem card_balancedNumbers (r d : ℕ) :
    #((range (r ^ d)).filter fun x => Balanced r d x) = #(balancedVecs r d) := by
  refine card_bij (fun x _ => digitVec r d x) (fun x hx => ?_) (fun x hx y hy h => ?_)
    (fun v hv => ?_)
  · exact mem_balancedVecs.mpr (mem_filter.mp hx).2.2
  · rw [← digitVal_digitVec (mem_filter.mp hx).2.1, ← digitVal_digitVec (mem_filter.mp hy).2.1, h]
  · have hb := mem_balancedVecs.mp hv
    obtain ⟨hlt, hdig⟩ := digitVal_lt_and_digitVec hb.1
    exact ⟨digitVal r v, mem_filter.mpr ⟨mem_range.mpr hlt, hlt, by rw [hdig]; exact hb⟩, hdig⟩

variable {p : ℕ} [Fact p.Prime]

/-- **The expected number of balanced queries**: summed over all seeds, the queries whose target
hash is balanced number `|C| #balancedVecs (p - 1) p`, for `r ^ d ≤ p`. -/
theorem sum_length_balancedTargets {r d : ℕ} (hp : r ^ d ≤ p) (C : List ℕ) :
    ∑ s ∈ seeds p, (C.filter fun c => decide (Balanced r d (s.target c))).length =
      C.length * (#(balancedVecs r d) * ((p - 1) * p)) := by
  simpa only [card_balancedNumbers] using sum_length_filter_target (p := p)
    (T := (range (r ^ d)).filter fun x => Balanced r d x)
    (fun z hz => (mem_range.mp (mem_filter.mp hz).1).trans_le hp)
    (fun z => by simp only [mem_filter, mem_range]; exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩) C

omit [Fact p.Prime] in
/-- **The cost of one base-`r` trial and its reported values**, bounded by the work on the
balanced queries. -/
theorem vtrial_time_add_le {r d s : ℕ} (σ : Seed p) (A B C : List ℕ) :
    let Ag := A.filter fun a => decide (Isolated p A a)
    let Bg := B.filter fun b => decide (Isolated p B b)
    let t := balancedSize r d
    (vtrialM r d s σ Ag Bg C).time +
        (C.filter fun c => decide (VAccepts r d σ Ag Bg c)).length ≤
      (A.length + B.length + C.length + (t + 1) * (A.length + B.length + 3 * (r * d + 1) *
        #((Fintype.piFinset fun _ : Fin d => range r).filter fun x => ∑ i, x i ≤ s))) +
      (2 + (t + 1) * (3 * (r * d + 1) * ∑ j ∈ range (t - s + 1), t.choose j)) *
        (C.filter fun c => decide (Balanced r d (σ.target c))).length := by
  intro Ag Bg t
  rw [time_vtrialM σ Ag Bg C]
  set H := #((Fintype.piFinset fun _ : Fin d => range r).filter fun x => ∑ i, x i ≤ s)
  set Q := ∑ j ∈ range (t - s + 1), t.choose j
  set Cs := C.filter fun c => decide (Balanced r d (σ.target c))
  have hAg : Ag.length ≤ A.length := List.length_filter_le _ _
  have hBg : Bg.length ≤ B.length := List.length_filter_le _ _
  have hC : Cs.length ≤ C.length := List.length_filter_le _ _
  have hacc : (C.filter fun c => decide (VAccepts r d σ Ag Bg c)).length ≤ Cs.length := by
    simp only [Cs, ← List.countP_eq_length_filter]
    exact List.countP_mono_left fun c _ h => by simpa using (of_decide_eq_true h).1
  have hhigh : (Cs.map fun c => #((Iic (digitVec r d (σ.target c))).filter fun y =>
      s ≤ ∑ i, y i)).sum ≤ Cs.length * Q := by
    have := List.sum_le_length_nsmul (Cs.map fun c => #((Iic (digitVec r d (σ.target c))).filter
      fun y => s ≤ ∑ i, y i)) Q fun x hx => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        have hb := (by simpa using (List.mem_filter.mp hc).2 : Balanced r d (σ.target c))
        have hsz : ∑ i, digitVec r d (σ.target c) i = t := sum_digits_of_balancedVec hb.2
        have := card_Iic_filter_le_sum_le (digitVec r d (σ.target c)) s
        rwa [hsz] at this
    simpa using this
  have hsplit : ∀ t₁ ∈ List.range (t + 1),
      (leftEntries r d t₁ σ (starLeftV r d σ Ag) leftWeight).length +
        (rightEntries r d (t - t₁) σ (starRightV r d σ Bg) rightWeight).length +
        3 * (r * d + 1) * (H + (Cs.map fun c => #((Iic (digitVec r d (σ.target c))).filter
          fun y => s ≤ ∑ i, y i)).sum) ≤
      A.length + B.length + 3 * (r * d + 1) * H + 3 * (r * d + 1) * Q * Cs.length := by
    intro t₁ _
    have hl : (leftEntries r d t₁ σ (starLeftV r d σ Ag) leftWeight).length ≤ A.length := by
      simp only [leftEntries, List.length_map]
      exact ((List.length_filter_le _ _).trans (List.length_filter_le _ _)).trans hAg
    have hr : (rightEntries r d (t - t₁) σ (starRightV r d σ Bg) rightWeight).length ≤
        B.length := by
      simp only [rightEntries, List.length_map]
      exact ((List.length_filter_le _ _).trans (List.length_filter_le _ _)).trans hBg
    have := Nat.mul_le_mul_left (3 * (r * d + 1)) hhigh
    nlinarith
  have hsum := List.sum_le_length_nsmul _ _ fun x hx => by
    obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.mp hx
    exact hsplit t₁ ht₁
  simp only [List.length_map, List.length_range, smul_eq_mul] at hsum
  change Ag.length + Bg.length + C.length + _ + Cs.length + _ ≤ _
  nlinarith

/-- **The total cost of the base-`r` reduction over all seed tuples for one prime** `p ≥ r ^ d`:
`p ∑ time ≤ #seeds ^ μ (p (3 |A| + 3 |B| + |C| + |A_bad| |B| + |A| |B_bad| + μ G₀) +
μ G₁ |C| #balancedVecs)`, with `G₀`, `G₁` as in `vtrial_time_add_le`. -/
theorem mul_sum_time_vthreeSumM_le {r d s μ : ℕ} (hp : r ^ d ≤ p) (hs : s ≤ balancedSize r d)
    (A B C : List ℕ) :
    let t := balancedSize r d
    p * ∑ ss ∈ Fintype.piFinset (fun _ : Fin μ => seeds p),
        (vthreeSumM r d s p (List.ofFn ss) A B C).time ≤
      #(seeds p) ^ μ * (p * (3 * A.length + 3 * B.length + C.length +
        (A.filter fun a => decide (¬ Isolated p A a)).length * B.length +
        A.length * (B.filter fun b => decide (¬ Isolated p B b)).length +
        μ * (A.length + B.length + C.length + (t + 1) * (A.length + B.length + 3 * (r * d + 1) *
          #((Fintype.piFinset fun _ : Fin d => range r).filter fun x => ∑ i, x i ≤ s)))) +
        μ * ((2 + (t + 1) * (3 * (r * d + 1) * ∑ j ∈ range (t - s + 1), t.choose j)) *
          (C.length * #(balancedVecs r d)))) :=
  mul_sum_time_reduceM_le (trialSpec_vtrialM hs) A B C (fun σ => vtrial_time_add_le σ A B C)
    (by rw [sum_length_balancedTargets hp]; ring)

omit [Fact p.Prime] in
/-- **The expected cost of the base-`r` reduction** ([ChanItakuraMaYu2026], Theorem 3.4,
running-time analysis): for duplicate-free `A`, `B` with elements below `M`, `1 ≤ e` and
`r ^ d ≤ 2 ^ e`, the expected cost of `vthreeSumM` over a uniform prime of
`[2 ^ e, 2 ^ (e + 1))` and `μ` uniform seeds is at most `3 |A| + 3 |B| + |C| + μ G₀ +
μ G₁ |C| #balancedVecs / 2 ^ e + (|A| ^ 2 |B| + |A| |B| ^ 2) log₂ M / (e #window)`, with `G₀`, `G₁`
as in `vtrial_time_add_le`. -/
theorem avg_time_vthreeSumM_le {r d s e μ M : ℕ} (hs : s ≤ balancedSize r d) (he : 1 ≤ e)
    (hre : r ^ d ≤ 2 ^ e) {A B C : List ℕ} (hA : A.Nodup) (hB : B.Nodup)
    (hAM : ∀ a ∈ A, a < M) (hBM : ∀ b ∈ B, b < M) (hW : (primeWindow e).Nonempty) :
    let t := balancedSize r d
    let G₀ : ℕ := A.length + B.length + C.length + (t + 1) * (A.length + B.length +
      3 * (r * d + 1) * #((Fintype.piFinset fun _ : Fin d => range r).filter
        fun x => ∑ i, x i ≤ s))
    let G₁ : ℕ := 2 + (t + 1) * (3 * (r * d + 1) * ∑ j ∈ range (t - s + 1), t.choose j)
    avgTimeOf (fun q σ => vtrialM r d s (p := q) σ) μ e A B C ≤
      ((3 * A.length + 3 * B.length + C.length + μ * G₀ : ℕ) : ℝ) +
        ((μ * (G₁ * (C.length * #(balancedVecs r d))) : ℕ) : ℝ) / 2 ^ e +
        ((A.length * A.length * B.length + A.length * (B.length * B.length)) * Nat.log 2 M : ℕ) /
          ((e : ℝ) * #(primeWindow e)) := by
  intro t G₀ G₁
  set W := primeWindow e
  set bad : ℕ → ℕ := fun q => (A.filter fun a => decide (¬ Isolated q A a)).length * B.length +
    A.length * (B.filter fun b => decide (¬ Isolated q B b)).length
  have h1 := avgTimeOf_le (trial := fun q σ => vtrialM r d s (p := q) σ) (μ := μ) (C := C) hW
    (K := 3 * A.length + 3 * B.length + C.length + μ * G₀)
    (Y := μ * (G₁ * (C.length * #(balancedVecs r d)))) (bad := bad) fun q hq _ =>
      (mul_sum_time_vthreeSumM_le (μ := μ) (hre.trans (mem_primeWindow.1 hq).2.1) hs A B C).trans_eq
        (by simp only [bad, G₀, G₁, t]; ring)
  refine h1.trans (add_le_add_right ?_ _)
  -- the bad elements over the window
  have hbadA := mul_sum_length_bad_le (d := e) hA hAM
  have hbadB := mul_sum_length_bad_le (d := e) hB hBM
  have hbadsum : e * ∑ q ∈ W, bad q ≤
      (A.length * A.length * B.length + A.length * (B.length * B.length)) * Nat.log 2 M := by
    have : e * ∑ q ∈ W, bad q = B.length * (e * ∑ q ∈ W,
        (A.filter fun a => decide (¬ Isolated q A a)).length) +
        A.length * (e * ∑ q ∈ W, (B.filter fun b => decide (¬ Isolated q B b)).length) := by
      simp only [bad, sum_add_distrib, mul_add, mul_sum]
      congr 1 <;> refine sum_congr rfl fun _ _ => by ring
    rw [this]
    calc _ ≤ B.length * (A.length * A.length * Nat.log 2 M) +
          A.length * (B.length * B.length * Nat.log 2 M) := by gcongr
      _ = _ := by ring
  have hWpos : (0 : ℝ) < #W := by exact_mod_cast hW.card_pos
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_le_div_iff₀ hWpos (by positivity)]
  have : ((e * ∑ q ∈ W, bad q : ℕ) : ℝ) ≤
      ((A.length * A.length * B.length + A.length * (B.length * B.length)) * Nat.log 2 M : ℕ) := by
    exact_mod_cast hbadsum
  push_cast at this ⊢
  nlinarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
