/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.ExpectedCost
public import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Repetition
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import CslibFrontier.Foundations.Data.Finset.Markov
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Truly subquadratic integer 3SUM (Corollary 2.4, balanced case)

The balanced case of [ChanItakuraMaYu2026], Corollary 2.4, in the `TimeM` unit-cost model, with
exponent `2 - 1/100` (`corollary_2_4`). Fix the magnitude exponent `κ`. There are `K` and `m₀`
such that for every unit `m ≥ m₀`, every `R`, and all duplicate-free `A`, `B` and any `C` with at
most `n = 2 ^ (100 m)` elements below `n ^ κ`, the algorithm `corollaryM` with `R` clocked copies
and budget `T = ⌈20 K n ^ (2 - 1/100)⌉` (`budget`):

* costs at most `R (T + |C|) + |C|` ticks for every choice of the random numbers,
* reports only values `c = a + b` with `a ∈ A`, `b ∈ B`, and
* misses each `c ∈ C ∩ (A + B)` with probability at most `(1/5) ^ R`.

Per copy, the miss probability splits into a bad prime (`card_badPrimes_le`, at most `1/20` for
large `m`), all `μ` trials rejecting (`average_miss_le`, at most `e ^ (-3) < 1/20`), and the run
exceeding its budget (Markov's inequality with `exists_avgTime_le`, at most `1/20`); the copies are
independent (`allFailProb_eq_pow`). With `R = ⌈log₅ n⌉`, each query is missed with probability at
most `1 / n` in worst-case time `O(n ^ (2 - 1/100) log n)`.

**Scope.** This is narrower than the paper's Corollary 2.4. The paper allows unbalanced sets, with
`N = |A| + |B|` and `n̂ = √(|A| |B|)`, error `O(1/N)` and time
`O(n̂ ^ 1.965 + N n̂ ^ 0.899 + |C| n̂ ^ 0.965)`, whose separate per-query term also gives the
3SUM-indexing data structure. Here all of `|A|`, `|B|`, `|C|` are at most `n`, and one budget
covers preprocessing and queries together. The theorem accepts every size up to `n = 2 ^ (100 m)`;
a statement for arbitrary sizes (taking the least such `m`, which costs a factor up to `2 ^ 199`
in the constant, and covering `m < m₀`) is not formalized. The paper's exponent `1.965` comes from
real parameters `γ = 0.2`, `δ = 0.033`; the integer parameter family used here
(`CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Params`) gives `2 - 1/100`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum

open Finset Params

/-- The budget of one copy: `⌈20 K 2 ^ (199 m)⌉ = ⌈20 K n ^ (2 - 1/100)⌉`. -/
@[expose] noncomputable def budget (K : ℝ) (m : ℕ) : ℕ := ⌈20 * K * 2 ^ (199 * m)⌉₊

/-- A clocked copy misses `c` only if the unclocked reduction misses `c` or exceeds the budget. -/
theorem copyMissFrac_le {m T : ℕ} (hT : 0 < T) {A B C : List ℕ} {c q : ℕ} (hq : q.Prime) :
    copyMissFrac m T A B C c q ≤ missProb (d m) (t m) (s m) (μ m) A B C c q +
      (if h : q.Prime then
        haveI : Fact q.Prime := ⟨h⟩
        (∑ ss ∈ Fintype.piFinset (fun _ : Fin (μ m) => seeds q),
          ((threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).time : ℝ)) /
          (#(seeds q) : ℝ) ^ μ m
      else 0) / T := by
  have : Fact q.Prime := ⟨hq⟩
  unfold copyMissFrac missProb
  rw [dite_eq_left_of_eq_true (eq_true hq), dite_eq_left_of_eq_true (eq_true hq), seedsOf_eq]
  set S := Fintype.piFinset fun _ : Fin (μ m) => seeds q
  set time : (Fin (μ m) → Seed q) → ℕ := fun ss =>
    (threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).time
  have hsub : S.filter (fun ss => c ∉ (copyM m T A B C q ss).ret) ⊆
      S.filter (fun ss => c ∉ (threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).ret) ∪
        S.filter fun ss => T < time ss := by
    intro ss hss
    obtain ⟨hS, hmiss⟩ := mem_filter.mp hss
    by_cases hle : time ss ≤ T
    · refine mem_union_left _ (mem_filter.mpr ⟨hS, ?_⟩)
      unfold copyM at hmiss
      split_ifs at hmiss with h
      · exact hmiss
      · exact absurd hle h
    · exact mem_union_right _ (mem_filter.mpr ⟨hS, by omega⟩)
  have hpos : (0 : ℝ) < (#(seeds q) : ℝ) ^ μ m := by
    have : 0 < #(seeds q) := by
      rw [card_seeds]; exact Nat.mul_pos (by have := hq.one_lt; omega) (pow_pos hq.pos 2)
    positivity
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have h1 : (#(S.filter fun ss => c ∉ (copyM m T A B C q ss).ret) : ℝ) ≤
      #(S.filter fun ss => c ∉ (threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).ret) +
        (∑ ss ∈ S, (time ss : ℝ)) / T := by
    have h2 : (#(S.filter fun ss => T < time ss) : ℝ) ≤ (∑ ss ∈ S, (time ss : ℝ)) / T := by
      rw [le_div_iff₀ hTpos]
      exact S.card_filter_mul_le_sum (fun ss => T < time ss) (fun ss => (time ss : ℝ))
        (fun _ _ => Nat.cast_nonneg _) fun _ _ h => by exact_mod_cast h.le
    have h3 : (#(S.filter fun ss => c ∉ (copyM m T A B C q ss).ret) : ℝ) ≤
        #(S.filter fun ss => c ∉ (threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).ret) +
          #(S.filter fun ss => T < time ss) := by exact_mod_cast hcard
    linarith
  calc (#(S.filter fun ss => c ∉ (copyM m T A B C q ss).ret) : ℝ) / (#(seeds q) : ℝ) ^ μ m
      ≤ (#(S.filter fun ss => c ∉ (threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).ret) +
          (∑ ss ∈ S, (time ss : ℝ)) / T) / (#(seeds q) : ℝ) ^ μ m := by gcongr
    _ = _ := by rw [add_div, div_div, div_div, mul_comm (T : ℝ)]

/-- **One copy misses with probability at most** the average miss probability of the unclocked
reduction plus the expected cost divided by the budget. -/
theorem copyFailProb_le {m T : ℕ} (hT : 0 < T) (A B C : List ℕ) (c : ℕ) :
    copyFailProb m T A B C c ≤
      (∑ q ∈ primeWindow (d m), missProb (d m) (t m) (s m) (μ m) A B C c q) /
        #(primeWindow (d m)) + avgTime m A B C / T := by
  unfold copyFailProb avgTime
  calc (∑ q ∈ primeWindow (d m), copyMissFrac m T A B C c q) / #(primeWindow (d m))
      ≤ (∑ q ∈ primeWindow (d m), missProb (d m) (t m) (s m) (μ m) A B C c q +
          (∑ q ∈ primeWindow (d m), if h : q.Prime then
            haveI : Fact q.Prime := ⟨h⟩
            (∑ ss ∈ Fintype.piFinset (fun _ : Fin (μ m) => seeds q),
              ((threeSumM (d m) (t m) (s m) q (List.ofFn ss) A B C).time : ℝ)) /
              (#(seeds q) : ℝ) ^ μ m
          else 0) / T) / #(primeWindow (d m)) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [sum_div, ← sum_add_distrib]
        exact sum_le_sum fun q hq => copyMissFrac_le (m := m) hT (mem_primeWindow.mp hq).1
    _ = _ := by rw [add_div, div_div, div_div, mul_comm (T : ℝ)]

/-- `μ` trials suffice: `(1 - 3 #P / 4 ^ (d + 2)) ^ μ ≤ e ^ (-3) < 1/20`. -/
theorem trials_miss_le {m : ℕ} :
    (1 - 3 * #(rankedPairs (d m) (t m)) / (4 : ℝ) ^ (d m + 2)) ^ μ m ≤ 1 / 20 := by
  rw [card_rankedPairs]
  set P := (d m).choose (2 * t m) * (2 * t m).choose (t m)
  have hPpos : 0 < P := Nat.mul_pos (Nat.choose_pos (by unfold d t; omega))
    (Nat.choose_pos (by omega))
  have hμ : 4 ^ (d m + 2) < μ m * P := by
    unfold μ numPairs
    rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hPpos
  have h4 : (0 : ℝ) < (4 : ℝ) ^ (d m + 2) := by positivity
  have hx : (0 : ℝ) ≤ 3 * P / (4 : ℝ) ^ (d m + 2) := by positivity
  have hle1 : 3 * (P : ℝ) / (4 : ℝ) ^ (d m + 2) ≤ 1 := by
    rw [div_le_one h4]
    have : (P : ℝ) ≤ (4 : ℝ) ^ (d m) := by
      have := card_rankedPairs_le (d m) (t m)
      rw [card_rankedPairs] at this
      have h' : (2 ^ d m * 2 ^ d m : ℕ) = 4 ^ d m := by rw [← mul_pow]; norm_num
      exact_mod_cast this.trans h'.le
    rw [pow_add]; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) (d m)]
  have hexp := Real.add_one_le_exp (-(3 * (P : ℝ) / (4 : ℝ) ^ (d m + 2)))
  calc (1 - 3 * (P : ℝ) / (4 : ℝ) ^ (d m + 2)) ^ μ m
      ≤ Real.exp (-(3 * P / (4 : ℝ) ^ (d m + 2))) ^ μ m :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
    _ = Real.exp (-(3 * P * μ m / (4 : ℝ) ^ (d m + 2))) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-3) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, le_div_iff₀ h4]
        have : ((4 ^ (d m + 2) : ℕ) : ℝ) < (μ m : ℝ) * P := by exact_mod_cast hμ
        push_cast at this
        nlinarith
    _ ≤ 1 / 20 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), one_div, inv_inv]
        have h := Real.exp_one_gt_d9
        have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        nlinarith [sq_nonneg (Real.exp 1)]

/-- Eventually `C m ≤ 4 ^ m`. -/
private theorem eventually_mul_le_four_pow (C : ℝ) : ∀ᶠ m : ℕ in Filter.atTop,
    C * m ≤ (4 : ℝ) ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 4 by norm_num)
  have hC : 0 < |C| + 1 := by positivity
  filter_upwards [h.eventually (gt_mem_nhds (inv_pos.mpr hC))] with m hm
  rw [pow_one, div_lt_iff₀ (by positivity)] at hm
  have : C * m ≤ (|C| + 1) * m := by
    gcongr; exact (le_abs_self C).trans (by linarith)
  calc C * m ≤ (|C| + 1) * m := this
    _ ≤ (|C| + 1) * ((|C| + 1)⁻¹ * 4 ^ m) := by gcongr
    _ = 4 ^ m := by field_simp

/-- **Bad primes are rare**: for `m` large enough (depending on `κ`), at most a twentieth of the
window is bad for any query, when all inputs are below `2 ^ (100 κ m)` and `|A|, |B| ≤ n`. -/
theorem eventually_badPrimes_le (κ : ℕ) : ∀ᶠ m : ℕ in Filter.atTop, ∀ A B : List ℕ, ∀ c : ℕ,
    A.length ≤ n m → B.length ≤ n m → (∀ a ∈ A, a < 2 ^ (100 * κ * m)) →
    (∀ b ∈ B, b < 2 ^ (100 * κ * m)) → c < 2 ^ (100 * κ * m) →
    (#(badPrimes (d m) (t m) c A B) : ℝ) / #(primeWindow (d m)) ≤ 1 / 20 := by
  filter_upwards [eventually_mul_le_four_pow (960 * (100 * κ + 1)), Filter.eventually_ge_atTop 1]
    with m hm hm1 A B c hA hB hAV hBV hcV
  set V := 2 ^ (100 * κ * m)
  set L := 100 * κ * m + 1
  have hM : ∀ ab ∈ A.toFinset ×ˢ B.toFinset, (((ab.1 + ab.2 : ℕ) : ℤ) - c).natAbs ≤ 2 ^ L := by
    intro ab hab
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    have h1 := hAV _ (List.mem_toFinset.mp ha)
    have h2 := hBV _ (List.mem_toFinset.mp hb)
    have : 2 ^ L = 2 * V := by rw [pow_succ]; ring
    omega
  have h := card_badPrimes_le (d := d m) (t := t m) hM
  rw [Nat.log_pow (by norm_num)] at h
  set X := #(badPrimes (d m) (t m) c A B)
  set D := 2 ^ d m
  have hD : 2 ≤ D := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ D := Nat.pow_le_pow_right (by norm_num) (by unfold d; omega)
  have hAB : #(A.toFinset ×ˢ B.toFinset) ≤ 2 ^ (200 * m) := by
    rw [card_product]
    calc #A.toFinset * #B.toFinset ≤ A.length * B.length :=
          Nat.mul_le_mul (List.toFinset_card_le _) (List.toFinset_card_le _)
      _ ≤ n m * n m := Nat.mul_le_mul hA hB
      _ = 2 ^ (200 * m) := by unfold n; rw [← pow_add]; ring_nf
  have hC : (2 * t m).choose (t m) ≤ 2 ^ (36 * m) := by
    rw [← two_mul_t]; exact Nat.choose_le_two_pow _ _
  set E := 2 ^ (236 * m)
  have hE : 4 ^ m * E = D * D := by
    unfold D d; rw [← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; ring_nf
  have h1 : d m * X * (D - 1) ≤ 4 * E * L := by
    calc d m * X * (D - 1) = d m * (X * (D - 1)) := by ring
      _ ≤ 4 * (2 * t m).choose (t m) * (#(A.toFinset ×ˢ B.toFinset) * L) := h
      _ ≤ 4 * 2 ^ (36 * m) * (2 ^ (200 * m) * L) := by gcongr
      _ = 4 * E * L := by unfold E; rw [show 236 * m = 36 * m + 200 * m by ring, pow_add]; ring
  have h2 : d m * X * D ≤ 8 * E * L := by
    have : D ≤ 2 * (D - 1) := by omega
    calc d m * X * D ≤ d m * X * (2 * (D - 1)) := Nat.mul_le_mul_left _ this
      _ = 2 * (d m * X * (D - 1)) := by ring
      _ ≤ 2 * (4 * E * L) := Nat.mul_le_mul_left _ h1
      _ = 8 * E * L := by ring
  have hmN : 960 * L ≤ 4 ^ m := by
    have hR : ((960 * (100 * κ + 1) * m : ℕ) : ℝ) ≤ ((4 ^ m : ℕ) : ℝ) := by
      push_cast; linarith [hm]
    have hN : 960 * (100 * κ + 1) * m ≤ 4 ^ m := by exact_mod_cast hR
    have h' : 960 * L ≤ 960 * (100 * κ + 1) * m := by unfold L; nlinarith
    exact h'.trans hN
  have hdpos : 0 < d m := by unfold d; omega
  have h3 : 60 * (d m + 1) * X ≤ D := by
    have key : 60 * (d m + 1) * X * (d m * D) ≤ D * (d m * D) := by
      calc 60 * (d m + 1) * X * (d m * D) = 60 * (d m + 1) * (d m * X * D) := by ring
        _ ≤ 60 * (d m + 1) * (8 * E * L) := Nat.mul_le_mul_left _ h2
        _ = (480 * (d m + 1) * L) * E := by ring
        _ ≤ (d m * 4 ^ m) * E := by
            apply Nat.mul_le_mul_right
            calc 480 * (d m + 1) * L ≤ 480 * (2 * d m) * L := by gcongr; omega
              _ = d m * (960 * L) := by ring
              _ ≤ d m * 4 ^ m := Nat.mul_le_mul_left _ hmN
        _ = D * (d m * D) := by rw [mul_assoc, hE]; ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hdpos (by omega))
  have hW := two_pow_le_card_primeWindow (d := d m) (by unfold d; omega)
  have hWpos : (0 : ℝ) < #(primeWindow (d m)) := by
    have : 0 < #(primeWindow (d m)) := by
      rcases Nat.eq_zero_or_pos #(primeWindow (d m)) with h0 | h0
      · rw [h0] at hW; have := Nat.one_le_two_pow (n := d m); omega
      · exact h0
    exact_mod_cast this
  rw [div_le_iff₀ hWpos]
  have h4 : 20 * X ≤ #(primeWindow (d m)) := by
    have : 3 * (d m + 1) * (20 * X) ≤ 3 * (d m + 1) * #(primeWindow (d m)) := by
      calc 3 * (d m + 1) * (20 * X) = 60 * (d m + 1) * X := by ring
        _ ≤ D := h3
        _ ≤ _ := hW
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have : (20 * X : ℝ) ≤ #(primeWindow (d m)) := by exact_mod_cast h4
  linarith

theorem copyFailProb_nonneg (m T : ℕ) (A B C : List ℕ) (c : ℕ) : 0 ≤ copyFailProb m T A B C c := by
  unfold copyFailProb copyMissFrac
  positivity

/-- **Corollary 2.4 of [ChanItakuraMaYu2026], balanced case: truly subquadratic integer 3SUM**,
with exponent `2 - 1/100` in the `TimeM` unit-cost model. All of `|A|`, `|B|`, `|C|` are at most
`n` and one budget covers preprocessing and queries; the paper's unbalanced form with its per-query
term is not covered (see the module docstring). For the magnitude exponent `κ` there are `K > 0` and
`m₀` such that for every unit `m ≥ m₀` (inputs of at most `n = 2 ^ (100 m)` elements below
`n ^ κ`), every number `R` of copies and budget `T = budget K m = ⌈20 K n ^ (2 - 1/100)⌉`:
`corollaryM` costs at most `R (T + n) + n` ticks for every choice of the random numbers, reports
only sums `a + b`, and misses each `c ∈ C ∩ (A + B)` with probability at most `(1/5) ^ R`. -/
theorem corollary_2_4 (κ : ℕ) : ∃ K : ℝ, 0 < K ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ R : ℕ,
    ∀ A B C : List ℕ, A.Nodup → B.Nodup → A.length ≤ n m → B.length ≤ n m → C.length ≤ n m →
    (∀ a ∈ A, a < 2 ^ (100 * κ * m)) → (∀ b ∈ B, b < 2 ^ (100 * κ * m)) →
    (∀ c ∈ C, c < 2 ^ (100 * κ * m)) →
    (∀ (qs : Fin R → ℕ) (ωs : (i : Fin R) → Fin (μ m) → Seed (qs i)),
      (corollaryM m (budget K m) R A B C qs ωs).time ≤ R * (budget K m + n m) + n m) ∧
    (∀ (qs : Fin R → ℕ) (ωs : (i : Fin R) → Fin (μ m) → Seed (qs i)) (c : ℕ),
      c ∈ (corollaryM m (budget K m) R A B C qs ωs).ret → ∃ a ∈ A, ∃ b ∈ B, a + b = c) ∧
    (∀ c ∈ C, (∃ a ∈ A, ∃ b ∈ B, a + b = c) →
      allFailProb m (budget K m) R A B C c ≤ (1 / 5) ^ R) := by
  obtain ⟨K₀, hK₀⟩ := exists_avgTime_le κ
  set K := max K₀ 1
  have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    ((eventually_badPrimes_le κ).and (Filter.eventually_ge_atTop 1))
  refine ⟨K, hKpos, m₀, fun m hm R A B C hAn hBn hA hB hC hAV hBV hCV => ⟨?_, ?_, ?_⟩⟩
  · intro qs ωs
    refine (time_corollaryM_le m _ R A B C qs ωs).trans ?_
    gcongr
  · intro qs ωs c hc
    exact exists_add_eq_of_mem_ret_corollaryM hc
  · rintro c hc ⟨a, ha, b, hb, habc⟩
    obtain ⟨hbad, hm1⟩ := hm₀ m hm
    rw [allFailProb_eq_pow hc]
    refine pow_le_pow_left₀ (copyFailProb_nonneg _ _ _ _ _ _) ?_ R
    set T := budget K m
    have h2pos : (0 : ℝ) < 2 ^ (199 * m) := by positivity
    have hTge : 20 * K * 2 ^ (199 * m) ≤ (T : ℝ) := by unfold T budget; exact Nat.le_ceil _
    have hTpos : 0 < T := by
      have : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hTge
      exact_mod_cast this
    have hW : (primeWindow (d m)).Nonempty := by
      have h := two_pow_le_card_primeWindow (d := d m) (by unfold d; omega)
      refine card_pos.mp ?_
      rcases Nat.eq_zero_or_pos #(primeWindow (d m)) with h0 | h0
      · rw [h0] at h; have := Nat.one_le_two_pow (n := d m); omega
      · exact h0
    have hmiss := average_miss_le (d := d m) (t := t m) (s := s m) (μ := μ m)
      (by unfold s t; omega) ha hb habc hc hW
    have htrials := trials_miss_le (m := m)
    have hbad' := hbad A B c hA hB hAV hBV (hCV c hc)
    have havg : avgTime m A B C / T ≤ 1 / 20 := by
      have h := hK₀ m hm1 A B C hAn hBn hA hB hC hAV hBV
      rw [div_le_iff₀ (by exact_mod_cast hTpos)]
      calc avgTime m A B C ≤ K₀ * 2 ^ (199 * m) := h
        _ ≤ K * 2 ^ (199 * m) := by gcongr; exact le_max_left _ _
        _ = 1 / 20 * (20 * K * 2 ^ (199 * m)) := by ring
        _ ≤ 1 / 20 * T := by gcongr
    have hcopy := copyFailProb_le hTpos A B C c (m := m)
    linarith

end Cslib.Algorithms.Lean.SubsetConvThreeSum
